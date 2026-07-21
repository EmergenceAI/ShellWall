import ShellWall.Basic

/-- The closed-world set of commands v1 can represent. Anything not listed here is,
by design, unrepresentable and therefore out of scope (and so cannot be certified
safe). Closed-worldness is a security property, not an oversight. -/
inductive Cmd where
  /-- Read a file's content to stdout (`cat p`); ignores stdin. -/
  | read    (p : Path)
  /-- Write stdin to `p` under `mode` (`> p` / `>> p`); produces no stdout. -/
  | write   (p : Path) (mode : WriteMode)
  /-- Filter stdin to the lines matching `pattern` (fixed-substring; see
  `grepFilter`). -/
  | grep    (pattern : String)
  /-- Sort stdin's lines (C-locale/codepoint order). -/
  | sort
  /-- Collapse adjacent duplicate lines of stdin (not a global dedup). -/
  | uniq
  /-- Emit line/word/byte counts of stdin. -/
  | wc
  /-- Remove `p` from the filesystem; ignores stdin, no stdout. -/
  | rm      (p : Path)
  /-- Create `p` as a directory (modeled as an empty entry; see `evalCmd`). -/
  | mkdir   (p : Path)

/-- A shell pipeline: a single command or two sub-pipelines joined by an operator.
The operator determines how state, stdin/stdout, and exit codes thread between the
two sides (see `evalPipelineFull`). -/
inductive Pipeline where
  /-- A lone command. -/
  | single  (c : Cmd)
  /-- `a | b` — `a`'s stdout feeds `b`'s stdin. -/
  | pipe    (a b : Pipeline)
  /-- `a ; b` — run `a` then `b` regardless of `a`'s exit; `b` gets fresh stdin. -/
  | seq     (a b : Pipeline)
  /-- `a && b` — run `b` only if `a` succeeds; `b` gets fresh stdin. -/
  | andThen (a b : Pipeline)
  /-- `a || b` — run `b` only if `a` fails; `b` gets fresh stdin. -/
  | orElse  (a b : Pipeline)
