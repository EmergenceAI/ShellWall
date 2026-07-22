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

/-- The filesystem: a total map from paths to their content (or `none` if absent).
There is no directory/file distinction (see `evalCmd`'s `mkdir`).

`def` (per spec) rather than `abbrev`: `FileState` is semireducible, so it unfolds
during application elaboration but not at `instances` transparency. If later proof
work needs it to reduce transparently, revisit this. -/
def FileState := Path → Option Content

/-! ## Line model

Every text operation below shares one line convention. It is stated once here and
used everywhere; `wc` deliberately does NOT use it (see `countLineBytes`). -/

/-- Split text into lines under the shared line model.

FIDELITY: strip at most one trailing `"\n"`, then split on `"\n"`:
`"a\nb\n" → ["a","b"]` (a trailing newline TERMINATES the last line, it is not a
separator introducing an empty final line), `"a\nb" → ["a","b"]` (an unterminated
final line is still a line), `"" → []`, `"\n" → [""]`. This is the Unix text-file
convention; the naive `s.splitOn "\n"` would yield a spurious trailing `""` for
every newline-terminated file, corrupting `uniq` output and line counts. -/
def textToLines (s : String) : List String :=
  if s.isEmpty then []
  else
    let parts := s.splitOn "\n"
    if s.endsWith "\n" then parts.dropLast else parts

/-- Render lines back to text.

FIDELITY: always newline-TERMINATES a non-empty result, matching grep/sort/uniq
(which emit `"a\nb\n"` even when their input lacked a final newline). Consequence:
these ops are not the identity on unterminated input — exactly as real coreutils. -/
def linesToText (ls : List String) : String :=
  match ls with
  | [] => ""
  | _  => String.intercalate "\n" ls ++ "\n"

/-- Render lines to `Content`, canonicalising the empty result to `.empty`.
(The model has three "no bytes" values — `.empty`, `.text ""`,
`.binary ByteArray.empty` — a `Content` wart; every empty result here is `.empty`.) -/
def linesToContent (ls : List String) : Content :=
  match ls with
  | [] => .empty
  | _  => .text (linesToText ls)

/-- A content's lines, if it has line structure.

FIDELITY: binary content is decoded as UTF-8 when valid then treated as text;
bytes that are not valid UTF-8 yield `none` (no line structure). Real coreutils
operate bytewise with no decode step. -/
def contentLines? : Content → Option (List String)
  | .empty    => some []
  | .text s   => some (textToLines s)
  | .binary b => (String.fromUTF8? b).map textToLines

/-! ## Content helpers -/

/-- Concatenate two contents (the `cat a b` operation).

FIDELITY: real bash has no text/binary distinction — a file is just bytes. The
`text`/`binary` split is a model artifact, so cross-type cases concatenate the
UTF-8 encodings and return `.binary` (byte-exact, never fails). `.empty` is the
identity on both sides. -/
def concatContent : Content → Content → Content
  | .empty, c => c
  | c, .empty => c
  | .text s₁,   .text s₂   => .text (s₁ ++ s₂)
  | .binary b₁, .binary b₂ => .binary (b₁ ++ b₂)
  | .text s,    .binary b  => .binary (s.toUTF8 ++ b)
  | .binary b,  .text s    => .binary (b ++ s.toUTF8)

/-- Whether a single line matches a grep pattern.

FIDELITY: substring only, not BRE regex. Real `grep` matches POSIX basic regular
expressions; a regex engine is out of scope for v1, so this is `grep -F`: a line
matches iff it contains `pat` as a literal substring. An empty pattern matches
every line (as real grep does). -/
def lineMatches (pat : String) (line : String) : Bool :=
  if pat.isEmpty then true
  else (line.splitOn pat).length > 1

/-- Keep the lines of `c` matching `pat` (the `grep pat` content transform). -/
def grepFilter (pat : String) (c : Content) : Content :=
  match contentLines? c with
  | some ls => linesToContent (ls.filter (lineMatches pat))
  -- FIDELITY: on undecodable bytes real grep prints "Binary file ... matches" and
  -- exits 0 if the pattern occurs; this model reports no match instead.
  | none    => .empty

/-- Insert `x` into a sorted line list, before the first `y` with `x ≤ y`.

FIDELITY: collation is Lean's `String ≤`, i.e. lexicographic by Unicode codepoint,
matching `LC_ALL=C sort`. Real `sort` is locale-dependent (LC_COLLATE) and would
fold case / ignore punctuation under e.g. en_US.UTF-8; v1 fixes the C locale. -/
def insertSortedLine (x : String) : List String → List String
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSortedLine x ys

/-- Sort a line list. Stable and deterministic: `foldr` inserts from the right and
`insertSortedLine` places `x` before the first `y ≥ x`, so equal lines keep input
order. (Insertion sort — a specification, not a production sorter.) -/
def sortLines (ls : List String) : List String :=
  ls.foldr insertSortedLine []

/-- Sort a content's lines (the `sort` content transform). -/
def sortContent (c : Content) : Content :=
  match contentLines? c with
  | some ls => linesToContent (sortLines ls)
  -- FIDELITY: undecodable bytes pass through unsorted rather than being dropped;
  -- real `sort` would reorder them bytewise.
  | none    => c

/-- Collapse ADJACENT duplicate lines.

FIDELITY: adjacent-only, exactly like real `uniq` — `uniq` alone does NOT dedup an
unsorted file, only `sort | uniq` does. Deliberately no sort here; collapsing all
duplicates would be the convenient-but-wrong implementation. -/
def uniqAdjacent : List String → List String
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      if x == y then uniqAdjacent (y :: rest) else x :: uniqAdjacent (y :: rest)

/-- Collapse adjacent duplicate lines of a content (the `uniq` content transform). -/
def uniqContent (c : Content) : Content :=
  match contentLines? c with
  | some ls => linesToContent (uniqAdjacent ls)
  | none    => c

/-! ## wc

`wc` is specified over BYTES, not over the line model above -- see below. -/

/-- The raw bytes of a content (UTF-8 encoding for text). Basis for `wc`, which is
specified bytewise, not over the line model. -/
def contentBytes : Content → ByteArray
  | .empty    => ByteArray.empty
  | .text s   => s.toUTF8
  | .binary b => b

/-- Whether a byte is ASCII whitespace (space, tab, NL, VT, FF, CR). -/
def isSpaceByte (b : UInt8) : Bool :=
  b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0B || b == 0x0C || b == 0x0D

/-- Count newline bytes.

FIDELITY: `wc -l` counts NEWLINE BYTES, not "lines" as `textToLines` models them —
on unterminated input they differ (`"a\nb"` has 1 newline but 2 lines). Counting
newline bytes is the faithful choice; deliberately NOT `(textToLines s).length`. -/
def countLineBytes (bs : List UInt8) : Nat :=
  bs.foldl (fun acc b => if b == 0x0A then acc + 1 else acc) 0

/-- Count words. FIDELITY: `wc -w` counts maximal runs of non-whitespace bytes. -/
def countWordBytes (bs : List UInt8) : Nat :=
  (bs.foldl (fun (st : Nat × Bool) b =>
      if isSpaceByte b then (st.1, false)
      else if st.2 then st else (st.1 + 1, true))
    ((0 : Nat), false)).1

/-- The `wc` content transform: emit line/word/byte counts of stdin.

FIDELITY: default `wc` counts BYTES (`-c`), not codepoints (`-m`) — `"héllo"` is 6
bytes but 5 codepoints; we count bytes. FIDELITY: output format is `"L W B\n"` with
single spaces; real `wc` right-aligns in width-dependent columns and appends the
filename. The three numbers are faithful; the spacing is not. -/
def wcContent (c : Content) : Content :=
  let bs := (contentBytes c).toList
  .text s!"{countLineBytes bs} {countWordBytes bs} {bs.length}\n"

/-! ## Command evaluation -/

/-- Point update: the returned state differs from `s` only at `p` (set to `c`).
Drives `write` (set) and `rm` (`none`). -/
def updateState (s : FileState) (p : Path) (c : Option Content) : FileState :=
  fun q => if q = p then c else s q

/-- Execute a single command. The input `Content` is stdin (the previous stage's
stdout); the output `Content` is stdout; the `FileState` in/out is the filesystem.
Total and deterministic. Per-command exit codes and edge cases are the FIDELITY
notes on each arm. -/
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

/-- Execute a pipeline, threading state, stdin/stdout, and exit codes between
stages. This is the internal helper that carries the final stdout; `evalPipeline`
is the public wrapper that drops it. The operator-specific threading (pipe feeds
stdout→stdin; `;`/`&&`/`||` give fresh stdin and branch on exit) is the FIDELITY
notes on each arm, and is what `SafePipeline`/`checkFull` mirror. -/
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

/-- Run a whole pipeline: the public denotation, returning only
`(FileState × ExitCode)`. Starts from `.empty` stdin (nothing piped from a
terminal) and drops the final stdout.

SCOPE: dropping stdout means a pipeline that sends private data to unredirected
stdout has no filesystem effect and is invisible to this model — a stated v1
decision, not an oversight. See the `THREAT MODEL — stdout (v1)` note at the top of
this file for the decision and the deployment assumption it rests on. -/
def evalPipeline (p : Pipeline) (s : FileState) : FileState × ExitCode :=
  let (s', _, ec) := evalPipelineFull p s .empty
  (s', ec)

/-! ## Noninterference helpers -/

/-- Whether a path is public (class `publicRW` or `publicRO`) — i.e. observable in
the noninterference guarantee. A boolean view of `classify`. -/
def isPublicPath (p : Path) : Bool :=
  match classify p with
  | .publicRW  => true
  | .publicRO  => true
  | .privateRW => false
  | .privateRO => false

/-- Whether a single command touches only public paths: a path-carrying command
(`read`/`write`/`rm`/`mkdir`) must be on a public path; stream ops carry no path
and are unconstrained. -/
def cmdTouchesOnlyPublic : Cmd → Bool
  | .read p    => isPublicPath p
  | .write p _ => isPublicPath p
  | .rm p      => isPublicPath p
  | .mkdir p   => isPublicPath p
  | .grep _    => true
  | .sort      => true
  | .uniq      => true
  | .wc        => true

/-- `touchesOnlyPublic p` holds iff every path mentioned by any command in `p` is
public. Used to gate conditional guards (`&&`/`||`): if a guard touches only public
paths, its execution — hence its exit code — is determined solely by the public
part of the state, so two states agreeing on all public paths run (or skip) the
body identically. That closes the implicit-flow channel the Prompt-13
counterexample exploited. Conservative (it rejects any conditional whose guard
reads/writes/removes a private path) but sound — the standard "public
program-counter" discipline from information-flow security. -/
def touchesOnlyPublic : Pipeline → Bool
  | .single c    => cmdTouchesOnlyPublic c
  | .pipe a b    => touchesOnlyPublic a && touchesOnlyPublic b
  | .seq a b     => touchesOnlyPublic a && touchesOnlyPublic b
  | .andThen a b => touchesOnlyPublic a && touchesOnlyPublic b
  | .orElse a b  => touchesOnlyPublic a && touchesOnlyPublic b

/-- Restrict a filesystem to its public paths (private paths become `none`). The
observable projection over which `shellwall_noninterference` is stated. -/
def publicProjection (s : FileState) : FileState :=
  fun p => if isPublicPath p then s p else none

/-- Two filesystems agree on every public path. The hypothesis of
`shellwall_noninterference`. Stated in pointwise `∀` form (rather than
`publicProjection s₁ = publicProjection s₂`) as the more primitive form to consume
in proofs. -/
def agreeOnPublicPaths (s₁ s₂ : FileState) : Prop :=
  ∀ p : Path, isPublicPath p = true → s₁ p = s₂ p

/-! ## Forward provenance

`cmdOutIsPublic`/`provOut` compute, FORWARD along execution, whether a command's or
pipeline's stdout is "public-provenance": built only from reads of PUBLIC paths and
public-preserving transforms. This is the notion that makes the safety spec
relationally sound (Prompt 16): unlike the per-state, value-based `IsPublic` (which
a private value coinciding with a public one satisfies), provenance is pinned to the
paths READ, so agreeing states yield the same value. The DECIDER already used this;
`SafeCmd`/`SafePipeline` now consume it too, and it is defined here so both can. -/

/-- Whether a command's stdout is public-PROVENANCE, given the state it runs in and
whether its stdin is public-provenance. Reading a PRIVATE path yields `false` even
if the bytes coincide with a public file's — the fix for the Prompt-15
counterexample. Stream transforms preserve the flag; `wc`/writes/`rm`/`mkdir` are
never public. -/
def cmdOutIsPublic (c : Cmd) (s : FileState) (stdinPub : Bool) : Bool :=
  match c with
  -- a read is public-provenance iff the path is PUBLIC and present (a missing read
  -- yields `.empty`, not certified public). Reading a private path ⇒ false.
  | .read p => isPublicPath p && (s p).isSome
  | .grep _ => stdinPub   -- public-preserving transform
  | .sort   => stdinPub
  | .uniq   => stdinPub
  | .wc     => false      -- aggregation: never public (disclosure-leak exclusion)
  | .write _ _ => false   -- emits `.empty`
  | .rm _      => false
  | .mkdir _   => false

/-- Whether a whole pipeline's stdout is public-provenance, given whether its stdin
is. Threads FORWARD exactly as `evalPipelineFull` runs (and as `checkFull`'s second
component computes — `provOut_eq_checkFull_snd` in `Decide` proves they coincide).
`;`/`&&`/`||` give the second stage fresh non-public (`false`) stdin; `&&`/`||` are
exit-aware. -/
def provOut : Pipeline → FileState → Content → Bool → Bool
  | .single c, s, _stdin, pub => cmdOutIsPublic c s pub
  | .pipe p₁ p₂, s, stdin, pub =>
      provOut p₂ (evalPipelineFull p₁ s stdin).1 (evalPipelineFull p₁ s stdin).2.1
        (provOut p₁ s stdin pub)
  | .seq p₁ p₂, s, stdin, _pub =>
      provOut p₂ (evalPipelineFull p₁ s stdin).1 .empty false
  | .andThen p₁ p₂, s, stdin, pub =>
      match (evalPipelineFull p₁ s stdin).2.2 with
      | .success   => provOut p₂ (evalPipelineFull p₁ s stdin).1 .empty false
      | .failure _ => provOut p₁ s stdin pub
  | .orElse p₁ p₂, s, stdin, pub =>
      match (evalPipelineFull p₁ s stdin).2.2 with
      | .success   => provOut p₁ s stdin pub
      | .failure _ => provOut p₂ (evalPipelineFull p₁ s stdin).1 .empty false
