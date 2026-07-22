import ShellWall
open System

/-! # Fidelity harness

The first code that runs REAL bash, to validate `evalPipelineFull` against actual
shell behavior. This module is IO/impure tooling: it is NOT imported by the
verified core (`ShellWall.lean`), and `lake build` never runs it. It is driven by
the `fidelity` executable (`lake exe fidelity`).

All real execution is sandboxed to a fresh temp directory — never real paths.

Windows note: bare `bash` often resolves to the WSL launcher
(`C:\Windows\System32\bash.exe`), which on this class of machine may be broken or
do path translation. `detectShell` therefore probes candidates (Git Bash first)
and only uses one that echoes a sentinel correctly. -/

namespace ShellWall.Fidelity

/-! ## Executor -/

/-- Captured result of running a real shell command. -/
structure ShellResult where
  stdout   : String
  exitCode : Nat
  deriving Repr, Inhabited

/-- Candidate shells, in preference order. Git Bash full paths first (most
POSIX-faithful here); bare `bash` last (it may be the WSL launcher). -/
def shellCandidates : List String :=
  [ "C:/Program Files/Git/usr/bin/bash.exe",
    "C:/Program Files/Git/bin/bash.exe",
    "/usr/bin/bash",
    "sh",
    "bash" ]

/-- Probe a shell: it must run and echo a sentinel exactly (guards against a
spawnable-but-broken shell, e.g. a misconfigured WSL). -/
def probeShell (sh : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd := sh, args := #["-c", "printf __sw_ok__"] }
    let clean := (out.stdout.replace "\n" "").replace "\r" ""
    return out.exitCode == 0 && clean == "__sw_ok__"
  catch _ => return false

/-- The first working shell from `shellCandidates`, or `none` if none work. -/
def detectShell : IO (Option String) := do
  for c in shellCandidates do
    if (← probeShell c) then return (some c)
  return none

/-- Run `command` in `shell` with working directory `cwd`, capturing stdout and
exit code. stderr is captured but discarded (the model has no stderr channel). -/
def runBash (shell command : String) (cwd : FilePath) : IO ShellResult := do
  let out ← IO.Process.output { cmd := shell, args := #["-c", command], cwd := some cwd }
  return { stdout := out.stdout, exitCode := out.exitCode.toNat }

/-! ## Renderer (`Pipeline → String`)

The easy direction: a structured term to its bash string. NOT a parser. Each
command renders to the bash it is SUPPOSED to model, so the fidelity test checks
the model's actual claim (e.g. `grep -F`, `LC_ALL=C sort`), not a stricter one. -/

/-- Single-quote for POSIX sh, escaping embedded single quotes. -/
def shq (s : String) : String :=
  "'" ++ s.replace "'" "'\\''" ++ "'"

/-- Model path → sandbox-relative path (drops the leading `/`; normalizes `\`). -/
def relPath (p : Path) : String :=
  let s := p.toString.replace "\\" "/"
  if s.startsWith "/" then String.ofList (s.toList.drop 1) else s

/-- Render one command to bash. Fidelity choices are commented. -/
def renderCmd : Cmd → String
  | .read p             => "cat " ++ shq (relPath p)
  -- write consumes stdin and emits no stdout: `cat > f` / `cat >> f` (NOT `tee`,
  -- which would also echo to stdout).
  | .write p .overwrite => "cat > " ++ shq (relPath p)
  | .write p .append    => "cat >> " ++ shq (relPath p)
  -- FIDELITY: model grep is literal-substring, so render `grep -F` (not BRE). `-e`
  -- gives the pattern explicitly (handles empty / leading-dash patterns).
  | .grep pat           => "grep -F -e " ++ shq pat
  -- FIDELITY: model sorts by Unicode codepoint (C locale); render `LC_ALL=C sort`
  -- so bash matches the model's claim, not a locale-dependent order.
  | .sort               => "LC_ALL=C sort"
  | .uniq               => "uniq"
  | .wc                 => "wc"
  | .rm p               => "rm " ++ shq (relPath p)
  | .mkdir p            => "mkdir " ++ shq (relPath p)

-- Render a whole pipeline, parenthesizing compound operands so bash operator
-- precedence matches the model's binary-tree structure. `partial` because the
-- `renderChild p → renderPipeline p` step is not structural; this is runtime
-- tooling, not proof-bearing (the verified core is `partial`-free).
mutual
  /-- Render a whole pipeline to its bash string (see the note above the block). -/
  partial def renderPipeline : Pipeline → String
    | .single c    => renderCmd c
    | .pipe a b    => renderChild a ++ " | "  ++ renderChild b
    | .seq a b     => renderChild a ++ " ; "  ++ renderChild b
    | .andThen a b => renderChild a ++ " && " ++ renderChild b
    | .orElse a b  => renderChild a ++ " || " ++ renderChild b
  /-- A pipeline as a sub-expression: bare if single, parenthesized if compound. -/
  partial def renderChild : Pipeline → String
    | .single c => renderCmd c
    | p         => "( " ++ renderPipeline p ++ " )"
end

/-! ## Model helpers -/

/-- Best-effort `Content` → `String` for comparing model output to bash stdout. -/
def contentToString : Content → String
  | .text s   => s
  | .empty    => ""
  | .binary b => (String.fromUTF8? b).getD ""

/-- `ExitCode` → the numeric exit status bash would report. -/
def exitToNat : ExitCode → Nat
  | .success   => 0
  | .failure n => n

/-- The empty filesystem (stream ops never consult it). -/
def emptyState : FileState := fun _ => none

/-- Digit-runs of a string, as `Nat`s — for comparing `wc`'s numbers while ignoring
its spacing. (Manual fold to avoid the in-flux `String.split` iterator API.) -/
def numbersOf (s : String) : List Nat :=
  let rec go : List Char → String → List Nat → List Nat
    | [],      cur, acc => if cur.isEmpty then acc else acc ++ [cur.toNat?.getD 0]
    | c :: cs, cur, acc =>
        if c.isDigit then go cs (cur.push c) acc
        else go cs "" (if cur.isEmpty then acc else acc ++ [cur.toNat?.getD 0])
  go s.toList "" []

/-! ## Tier 1: stream fidelity (stdin → stdout, no filesystem) -/

/-- Whether a corpus case is expected to agree with bash, or to diverge on purpose. -/
inductive FidelityExpectation
  /-- Model MUST agree with bash; a mismatch is a real fidelity bug. -/
  | shouldMatch
  /-- Model deliberately differs; the reason records how. -/
  | knownDivergence (reason : String)

/-- A Tier 1 case: feed `input` as stdin to `pipeline`, compare model vs bash. -/
structure StreamCase where
  name     : String
  input    : Content
  pipeline : Pipeline
  expect   : FidelityExpectation
  /-- Naive bash to demonstrate a divergence (e.g. default `grep`/`sort`/`wc`
  instead of the faithful render). When `none`, the faithful render is used. -/
  bashOverride : Option String := none

/-- Escape newlines for one-line reporting. -/
def vis (s : String) : String := s.replace "\n" "\\n"

/-- Run one Tier 1 case and return a report line. -/
def runStreamCase (shell : String) (sandbox : FilePath) (c : StreamCase) : IO String := do
  let (_, outC, ec) := evalPipelineFull c.pipeline emptyState c.input
  let modelOut  := contentToString outC
  let modelExit := exitToNat ec
  IO.FS.writeBinFile (sandbox / "__stdin") (contentBytes c.input)
  let body := c.bashOverride.getD (renderPipeline c.pipeline)
  let r ← runBash shell ("{ " ++ body ++ " ; } < __stdin") sandbox
  let outMatch  := modelOut == r.stdout
  let exitMatch := modelExit == r.exitCode
  let full := outMatch && exitMatch
  let detail := s!"model(out={vis modelOut} exit={modelExit}) bash(out={vis r.stdout} exit={r.exitCode})"
  match c.expect with
  | .shouldMatch =>
      if full then
        return s!"  [PASS ] {c.name}"
      else
        return s!"  [❌BUG] {c.name} — shouldMatch but DIFFERS: {detail}"
  | .knownDivergence reason =>
      let numsMatch := numbersOf modelOut == numbersOf r.stdout
      if full then
        return s!"  [SURPRISE-MATCH] {c.name} — expected divergence ({reason}) but agrees: {detail}"
      else
        let hasNums := !(numbersOf modelOut).isEmpty
        let nums := if hasNums && numsMatch then " (numbers agree)" else ""
        return s!"  [diverges✓] {c.name} — as documented: {reason}{nums}"

/-- The Tier 1 corpus: every `FIDELITY:` note turned into a case. -/
def streamCorpus : List StreamCase :=
  [ -- shouldMatch
    { name := "uniq adjacent-only (b a b unchanged)", input := .text "b\na\nb\n",
      pipeline := .single .uniq, expect := .shouldMatch },
    { name := "sort | uniq full dedup", input := .text "b\na\nb\n",
      pipeline := .pipe (.single .sort) (.single .uniq), expect := .shouldMatch },
    { name := "grep substring present → exit 0", input := .text "abc\nxyz\n",
      pipeline := .single (.grep "bc"), expect := .shouldMatch },
    { name := "grep substring absent → exit 1", input := .text "abc\n",
      pipeline := .single (.grep "zzz"), expect := .shouldMatch },
    { name := "grep empty pattern matches all", input := .text "x\ny\n",
      pipeline := .single (.grep ""), expect := .shouldMatch },
    { name := "sort orders lines", input := .text "banana\napple\ncherry\n",
      pipeline := .single .sort, expect := .shouldMatch },
    { name := "sort adds trailing newline (unterminated input)", input := .text "a\nb",
      pipeline := .single .sort, expect := .shouldMatch },
    { name := "empty input → empty output", input := .empty,
      pipeline := .single .sort, expect := .shouldMatch },
    -- knownDivergence
    { name := "grep 'a.c' on abc", input := .text "abc\n",
      pipeline := .single (.grep "a.c"),
      expect := .knownDivergence "model is grep -F (substring), not BRE regex",
      bashOverride := some "grep -e 'a.c'" },
    { name := "wc output format (file-redirect stdin)", input := .text "a b c\n",
      pipeline := .single .wc,
      expect := .knownDivergence "model emits 'L W B' single-spaced; real wc right-aligns (+ filename)",
      bashOverride := some "wc" },
    { name := "wc output format (pipe stdin)", input := .text "a b c\n",
      pipeline := .single .wc,
      expect := .knownDivergence "GNU wc pads to width 7 when reading a non-seekable pipe; model is single-spaced",
      bashOverride := some "cat | wc" },
    { name := "sort mixed-case locale", input := .text "B\na\nA\nb\n",
      pipeline := .single .sort,
      expect := .knownDivergence "model is codepoint/C-locale; real sort is locale-dependent",
      bashOverride := some "sort" } ]

/-! ## Tier 2: filesystem fidelity (proof-of-concept only) -/

/-- A Tier 2 case: materialize `initFiles`, run `pipeline` in the sandbox, and
compare the resulting files at `checkPaths` to `evalPipelineFull`'s prediction. -/
structure FsCase where
  name       : String
  initFiles  : List (Path × Content)
  pipeline   : Pipeline
  checkPaths : List Path

/-- The model filesystem seeded from an explicit file list. -/
def stateOf (files : List (Path × Content)) : FileState :=
  fun p => (files.find? (fun x => decide (x.1 = p))).map (·.2)

/-- Write a model file to disk under `base`, creating parent directories. -/
def writeModelFile (base : FilePath) (p : Path) (c : Content) : IO Unit := do
  let full := base / relPath p
  match full.parent with
  | some d => IO.FS.createDirAll d
  | none   => pure ()
  IO.FS.writeBinFile full (contentBytes c)

/-- Ensure the parent directory of a model path exists under `base`. -/
def ensureParent (base : FilePath) (p : Path) : IO Unit := do
  match (base / relPath p).parent with
  | some d => IO.FS.createDirAll d
  | none   => pure ()

/-- Read a model file back from disk (as text), or `none` if absent. -/
def readModelFile (base : FilePath) (p : Path) : IO (Option Content) := do
  let full := base / relPath p
  if (← full.pathExists) then return some (.text (← IO.FS.readFile full))
  else return none

/-- Structural comparison of a predicted vs actual file (by string content). -/
def sameContent : Option Content → Option Content → Bool
  | none,   none   => true
  | some a, some b => contentToString a == contentToString b
  | _,      _      => false

/-- Run one Tier 2 case in a fresh sub-sandbox; return a report line. -/
def runFsCase (shell : String) (sandbox : FilePath) (idx : Nat) (c : FsCase) : IO String := do
  let sub := sandbox / s!"fs{idx}"
  IO.FS.createDirAll sub
  -- materialize starting state + ensure write-target parents exist
  for (p, cont) in c.initFiles do writeModelFile sub p cont
  for p in c.checkPaths do ensureParent sub p
  -- run real bash
  let _ ← runBash shell (renderPipeline c.pipeline) sub
  -- model prediction
  let predicted := (evalPipelineFull c.pipeline (stateOf c.initFiles) .empty).1
  -- compare each checked path
  let mut allOk := true
  let mut parts : List String := []
  for p in c.checkPaths do
    let actual ← readModelFile sub p
    let pred := predicted p
    let ok := sameContent pred actual
    allOk := allOk && ok
    let mark := if ok then "ok" else "MISMATCH"
    parts := parts ++ [s!"{relPath p}:{mark}"]
  let tag := if allOk then "[PASS ]" else "[❌BUG]"
  let joined := String.intercalate ", " parts
  return s!"  {tag} {c.name} — {joined}"

/-- The Tier 2 corpus (small proof-of-concept). -/
def fsCorpus : List FsCase :=
  [ { name := "simple write (cat shared > pub)",
      initFiles := [("/shared/ref.txt", .text "PUBDATA\n")],
      pipeline := .pipe (.single (.read "/shared/ref.txt"))
                        (.single (.write "/home/alice/public/out.txt" .overwrite)),
      checkPaths := ["/home/alice/public/out.txt"] },
    { name := "append (cat shared >> pub, existing)",
      initFiles := [("/shared/ref.txt", .text "PUB\n"),
                    ("/home/alice/public/out.txt", .text "existing\n")],
      pipeline := .pipe (.single (.read "/shared/ref.txt"))
                        (.single (.write "/home/alice/public/out.txt" .append)),
      checkPaths := ["/home/alice/public/out.txt"] },
    { name := "rm (remove an existing file)",
      initFiles := [("/home/alice/notes.txt", .text "SECRET\n")],
      pipeline := .single (.rm "/home/alice/notes.txt"),
      checkPaths := ["/home/alice/notes.txt"] },
    { name := "read | write chain (cat notes > notes2)",
      initFiles := [("/home/alice/notes.txt", .text "SECRET\n")],
      pipeline := .pipe (.single (.read "/home/alice/notes.txt"))
                        (.single (.write "/home/alice/notes2.txt" .overwrite)),
      checkPaths := ["/home/alice/notes2.txt"] } ]

/-! ## Driver -/

/-- Run the whole fidelity harness: detect a shell, run Tier 1 then Tier 2 in a
temp sandbox, print a fidelity map, and clean up. Fails gracefully if no shell. -/
def runFidelity : IO Unit := do
  IO.println "=== ShellWall fidelity harness ==="
  match ← detectShell with
  | none =>
      let tried := String.intercalate ", " shellCandidates
      IO.println s!"no bash found (tried: {tried})."
      IO.println "Skipping fidelity checks; the build and proofs are unaffected."
  | some shell =>
      IO.println s!"shell: {shell}"
      let sandbox ← IO.FS.createTempDir
      try
        IO.println "\n-- Tier 1: stream ops (model vs real bash) --"
        for c in streamCorpus do IO.println (← runStreamCase shell sandbox c)
        IO.println "\n-- Tier 2: filesystem (proof-of-concept) --"
        let mut i := 0
        for c in fsCorpus do
          IO.println (← runFsCase shell sandbox i c)
          i := i + 1
      finally
        try IO.FS.removeDirAll sandbox catch _ => pure ()
      IO.println "\nNote: comprehensive Tier 2 differential testing (all commands, all"
      IO.println "path classes, mkdir/directory semantics) is future work — the model's"
      IO.println "no-directory gap in particular is expected to surface there."

end ShellWall.Fidelity
