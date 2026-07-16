import ShellWall.Basic
import ShellWall.Syntax
import ShellWall.Policy

/-! # THREAT MODEL — stdout (v1)

Recorded verbatim as the resolution of gap C2 (Prompt 03 report): `evalPipeline`
returns only `(FileState × ExitCode)`, so a pipeline sending private data to
unredirected stdout (`cat /private/secret`) has no filesystem effect and is
invisible to this model — and because v1's `read_ok` is unconditional, such a
command is *permitted* by `SafeCmd` while `shellwall_noninterference` remains
provable (it quantifies only over the filesystem's public projection).

> **DECISION (v1):** stdout is out of scope for v1's threat model. ShellWall's
> guarantee covers filesystem writes to modeled paths only. This is sound under
> the explicit deployment assumption that the execution proxy does NOT return
> unredirected stdout to the agent. Under that assumption, an unredirected
> stdout channel is not agent-observable and therefore not a leak path. If that
> assumption ever fails to hold, stdout must be modeled as a public sink (an
> `IsPublic` obligation on writes to it), which is a signature change to
> `evalPipeline` — tracked as a v2 item. This is consistent with the existing
> decision to treat covert/side channels (timing, file size) as out of scope for
> v1.

This is accept-and-document: no code or signature change accompanies it. The
deployment assumption above is load-bearing — if the proxy ever returns
unredirected stdout to the agent, v1's guarantee does not cover that channel.
-/

-- `def` (per spec) rather than `abbrev`: FileState is semireducible, so it
-- unfolds during application elaboration but not at `instances` transparency.
-- If later proof work needs it to reduce transparently, revisit this.
def FileState := Path → Option Content

/-! ## Line model

Every text operation below shares one line convention. It is stated once here and
used everywhere; `wc` deliberately does NOT use it (see `countLineBytes`). -/

-- FIDELITY: line model. A `text s` is split into lines by stripping at most one
-- trailing "\n" and then splitting on "\n":
--   "a\nb\n" -> ["a","b"]  (a trailing newline TERMINATES the last line; it is
--                           not a separator introducing an empty final line)
--   "a\nb"   -> ["a","b"]  (an unterminated final line is still a line)
--   ""       -> []         (no lines at all)
--   "\n"     -> [""]       (exactly one, empty, line)
-- This is the Unix text-file convention. The naive alternative (raw
-- `s.splitOn "\n"`) yields a spurious trailing "" for every newline-terminated
-- file, which would corrupt `uniq` output and every line count.
def textToLines (s : String) : List String :=
  if s.isEmpty then []
  else
    let parts := s.splitOn "\n"
    if s.endsWith "\n" then parts.dropLast else parts

-- FIDELITY: rendering always newline-TERMINATES a non-empty result. This matches
-- grep/sort/uniq, which emit "a\nb\n" even when their input lacked a final
-- newline. Consequence: these ops are not the identity on unterminated input
-- ("a\nb" becomes "a\nb\n") -- which is exactly what real coreutils do.
def linesToText (ls : List String) : String :=
  match ls with
  | [] => ""
  | _  => String.intercalate "\n" ls ++ "\n"

-- The model has three distinct representations of "no bytes": `.empty`,
-- `.text ""`, and `.binary ByteArray.empty`. Every empty result produced here is
-- canonicalised to `.empty`. See the report: this is a modeling wart of the
-- `Content` type, not a bash behaviour.
def linesToContent (ls : List String) : Content :=
  match ls with
  | [] => .empty
  | _  => .text (linesToText ls)

-- FIDELITY: binary content is decoded as UTF-8 when valid and then treated as
-- text; bytes that are not valid UTF-8 have no line structure in this model and
-- yield `none`. Real coreutils operate bytewise over arbitrary bytes and have no
-- decode step at all.
def contentLines? : Content → Option (List String)
  | .empty    => some []
  | .text s   => some (textToLines s)
  | .binary b => (String.fromUTF8? b).map textToLines

/-! ## Content helpers -/

-- FIDELITY: real bash has no text/binary distinction -- a file is just bytes, and
-- `cat a b` is byte concatenation. The `text`/`binary` split is an artifact of
-- this model, so the cross-type cases have no direct bash analogue. We
-- concatenate the UTF-8 encodings and return `.binary`, which preserves the bytes
-- exactly and never fails. `.empty` is the identity on both sides.
def concatContent : Content → Content → Content
  | .empty, c => c
  | c, .empty => c
  | .text s₁,   .text s₂   => .text (s₁ ++ s₂)
  | .binary b₁, .binary b₂ => .binary (b₁ ++ b₂)
  | .text s,    .binary b  => .binary (s.toUTF8 ++ b)
  | .binary b,  .text s    => .binary (b ++ s.toUTF8)

-- FIDELITY: substring only, not BRE regex.
-- Real `grep` matches POSIX basic regular expressions. Implementing a regex engine
-- is out of scope for v1, so this is `grep -F` behaviour: a line matches iff it
-- contains `pat` as a literal substring. An empty pattern matches every line,
-- which is what real grep does (and which `String.splitOn` would not give us --
-- it guards the empty separator and returns the whole string).
def lineMatches (pat : String) (line : String) : Bool :=
  if pat.isEmpty then true
  else (line.splitOn pat).length > 1

def grepFilter (pat : String) (c : Content) : Content :=
  match contentLines? c with
  | some ls => linesToContent (ls.filter (lineMatches pat))
  -- FIDELITY: on undecodable bytes real grep prints "Binary file ... matches" and
  -- exits 0 if the pattern occurs; this model reports no match instead.
  | none    => .empty

-- FIDELITY: collation is Lean's `String ≤`, i.e. lexicographic by Unicode
-- codepoint. For valid UTF-8, codepoint order and byte order coincide, so this
-- matches `LC_ALL=C sort`. Real `sort` is locale-dependent (LC_COLLATE): under
-- e.g. en_US.UTF-8 it folds case and ignores punctuation, giving a different
-- order. v1 fixes the C locale.
def insertSortedLine (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSortedLine x ys

-- Stable and deterministic: `foldr` inserts from the right, and `insertSortedLine`
-- places `x` before the first `y` with `x ≤ y`, so equal lines retain their input
-- order. (Insertion sort, not a fast sort -- this is a specification, not a
-- production sorter.)
def sortLines (ls : List String) : List String :=
  ls.foldr insertSortedLine []

def sortContent (c : Content) : Content :=
  match contentLines? c with
  | some ls => linesToContent (sortLines ls)
  -- FIDELITY: undecodable bytes pass through unsorted rather than being dropped;
  -- real `sort` would reorder them bytewise.
  | none    => c

-- FIDELITY: adjacent-only, exactly like real `uniq`. `uniq` alone does NOT
-- deduplicate an unsorted file -- only `sort | uniq` does. Deliberately no sort
-- happens in here; collapsing all duplicates would be the convenient-but-wrong
-- implementation.
def uniqAdjacent : List String → List String
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      if x == y then uniqAdjacent (y :: rest) else x :: uniqAdjacent (y :: rest)

def uniqContent (c : Content) : Content :=
  match contentLines? c with
  | some ls => linesToContent (uniqAdjacent ls)
  | none    => c

/-! ## wc

`wc` is specified over BYTES, not over the line model above -- see below. -/

def contentBytes : Content → ByteArray
  | .empty    => ByteArray.empty
  | .text s   => s.toUTF8
  | .binary b => b

def isSpaceByte (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0B || b == 0x0C || b == 0x0D

-- FIDELITY: `wc -l` counts NEWLINE BYTES, not "lines" as `textToLines` models
-- them. On unterminated input the two differ: "a\nb" contains 1 newline but 2
-- lines. Counting newline bytes is the faithful choice, and this is deliberately
-- NOT `(textToLines s).length`.
def countLineBytes (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => if b == 0x0A then acc + 1 else acc) 0

-- FIDELITY: `wc -w` counts maximal runs of non-whitespace bytes.
def countWordBytes (bs : List UInt8) : Nat :=
  (bs.foldl (fun (st : Nat × Bool) b =>
      if isSpaceByte b then (st.1, false)
      else if st.2 then st else (st.1 + 1, true))
    ((0 : Nat), false)).1

-- FIDELITY: default `wc` prints lines, words, and BYTES (as `-c`), not codepoints
-- (`-m`). "héllo" is 6 bytes but 5 codepoints, so this distinction is real; we
-- count bytes.
-- FIDELITY: output format here is "L W B\n" with single spaces. Real `wc`
-- right-aligns the counts in width-dependent columns (e.g. "      2       4
-- 12") and appends the filename when given one. The three numbers are faithful;
-- the spacing is not.
def wcContent (c : Content) : Content :=
  let bs := (contentBytes c).toList
  .text s!"{countLineBytes bs} {countWordBytes bs} {bs.length}\n"

/-! ## Command evaluation -/

-- Point update: the returned state differs from `s` only at `p`.
def updateState (s : FileState) (p : Path) (c : Option Content) : FileState :=
  fun q => if q = p then c else s q

-- The input `Content` is stdin (the previous stage's stdout); the output
-- `Content` is stdout; the `FileState` in/out is the filesystem.
def evalCmd : Cmd → FileState → Content → (FileState × Content × ExitCode)
  -- FIDELITY: `read` ignores stdin, like `cat p`. A missing file yields no stdout
  -- and exit 1, matching `cat`. The specific code 1 is a decision: `cat` uses 1,
  -- but this model has no stderr on which to carry the diagnostic message.
  | .read p, s, _ =>
      match s p with
      | some c => (s, c, .success)
      | none   => (s, .empty, .failure 1)
  -- `write` consumes stdin and produces NO stdout, like `> p` / `>> p`.
  | .write p mode, s, stdin =>
      let newC := match mode with
        | .overwrite => stdin
        | .append    => concatContent ((s p).getD .empty) stdin
      (updateState s p (some newC), .empty, .success)
  -- FIDELITY: grep exits 0 iff at least one line matched, else 1. (Real grep uses
  -- 2 for errors, which this model cannot raise.) This exit code drives `&&`/`||`
  -- and must be right even though v1's SafePipeline checks both branches anyway.
  | .grep pat, s, stdin =>
      let out := grepFilter pat stdin
      match out with
      | .empty => (s, .empty, .failure 1)
      | _      => (s, out, .success)
  | .sort, s, stdin => (s, sortContent stdin, .success)
  | .uniq, s, stdin => (s, uniqContent stdin, .success)
  | .wc,   s, stdin => (s, wcContent stdin, .success)
  -- FIDELITY: `rm` without `-f` exits 1 on a missing path and removes nothing.
  | .rm p, s, _ =>
      match s p with
      | some _ => (updateState s p none, .empty, .success)
      | none   => (s, .empty, .failure 1)
  -- FIDELITY: model has no directory concept. `FileState` is `Path → Option
  -- Content`, so there is nothing that distinguishes a directory from a file.
  -- Least-bad v1 behaviour: mark `p` as existing with `.empty` content, and fail
  -- with exit 1 if `p` already exists (real `mkdir` without `-p` fails on an
  -- existing path). Consequence: the model cannot distinguish "file exists" from
  -- "directory exists", and a subsequent `read p` succeeds with empty output
  -- whereas real `cat` on a directory errors. Real `mkdir` also fails when the
  -- parent is missing; `Path` has no parent structure here, so that is not modeled.
  | .mkdir p, s, _ =>
      match s p with
      | some _ => (s, .empty, .failure 1)
      | none   => (updateState s p (some .empty), .empty, .success)

/-! ## Pipeline evaluation -/

-- Internal helper carrying stdin/stdout; `evalPipeline` drops the final stdout.
def evalPipelineFull : Pipeline → FileState → Content → (FileState × Content × ExitCode)
  | .single c, s, stdin => evalCmd c s stdin
  -- FIDELITY: `a`'s stdout becomes `b`'s stdin, and the pipeline's exit code is
  -- the LAST command's exit -- bash's default without `set -o pipefail`. `a`'s
  -- exit is discarded, so `false | true` exits 0.
  | .pipe a b, s, stdin =>
      let (s₁, outA, _) := evalPipelineFull a s stdin
      evalPipelineFull b s₁ outA
  -- FIDELITY: `;` is NOT a pipe. `b` runs regardless of `a`'s exit, on the
  -- filesystem `a` left behind, with FRESH empty stdin -- it does not receive
  -- `a`'s stdout. Exit is `b`'s exit.
  | .seq a b, s, stdin =>
      let (s₁, _, _) := evalPipelineFull a s stdin
      evalPipelineFull b s₁ .empty
  -- FIDELITY: `b` runs only when `a` succeeded, with fresh empty stdin.
  | .andThen a b, s, stdin =>
      let (s₁, outA, ecA) := evalPipelineFull a s stdin
      match ecA with
      | .success   => evalPipelineFull b s₁ .empty
      | .failure n => (s₁, outA, .failure n)
  -- FIDELITY: `b` runs only when `a` FAILED, with fresh empty stdin.
  | .orElse a b, s, stdin =>
      let (s₁, outA, ecA) := evalPipelineFull a s stdin
      match ecA with
      | .success   => (s₁, outA, .success)
      | .failure _ => evalPipelineFull b s₁ .empty

-- FIDELITY: initial stdin for a whole pipeline is `.empty` -- nothing is piped in
-- from a terminal.
-- SCOPE: the final stdout is dropped. A pipeline that reads private data and
-- sends it to stdout with no redirect has no filesystem effect and is therefore
-- invisible to this model. stdout-to-terminal is not modeled as a public sink;
-- only filesystem writes are. This is a stated v1 decision, not an oversight --
-- see the `THREAT MODEL — stdout (v1)` note at the top of this file for the
-- decision and the deployment assumption it rests on.
def evalPipeline (p : Pipeline) (s : FileState) : FileState × ExitCode :=
  let (s', _, ec) := evalPipelineFull p s .empty
  (s', ec)

/-! ## Noninterference helpers -/

-- Decides public-ness by cases on `classify`. `PathClass` already derives
-- `DecidableEq` in `Policy.lean`, and matching on the enum needs no instance at
-- all, so `Policy.lean` required no edit.
def isPublicPath (p : Path) : Bool :=
  match classify p with
  | .publicRW  => true
  | .publicRO  => true
  | .privateRW => false
  | .privateRO => false

def publicProjection (s : FileState) : FileState :=
  fun p => if isPublicPath p then s p else none

-- Stated in the pointwise `∀` form (rather than `publicProjection s₁ =
-- publicProjection s₂`) because it is the more primitive form to consume in
-- proofs; the noninterference theorem in `Safety.lean` takes this as its
-- hypothesis and concludes the `publicProjection` equation.
def agreeOnPublicPaths (s₁ s₂ : FileState) : Prop :=
  ∀ p : Path, isPublicPath p = true → s₁ p = s₂ p
