import ShellWall.Basic

-- Closed-world command set. Any command not listed here is, by design,
-- unrepresentable and therefore treated as unsafe.
inductive Cmd where
  | read    (p : Path)
  | write   (p : Path) (mode : WriteMode)
  | grep    (pattern : String)
  | sort
  | uniq
  | wc
  | rm      (p : Path)
  | mkdir   (p : Path)

inductive Pipeline where
  | single  (c : Cmd)
  | pipe    (a b : Pipeline)   -- a | b
  | seq     (a b : Pipeline)   -- a ; b
  | andThen (a b : Pipeline)   -- a && b
  | orElse  (a b : Pipeline)   -- a || b
