import ShellWall.Decide

/-- The gate's outward result: allow the pipeline, or reject it with a reason. -/
inductive Verdict where
  /-- The pipeline is permitted to run. -/
  | permit
  /-- The pipeline is rejected, with a human-readable diagnostic. -/
  | reject (reason : String)

/-- Top-level prove-or-reject entry point: `.permit` iff `checkSafe` returns `true`,
else `.reject` with a diagnostic reason. Body deferred (`sorry`). -/
def gate : Owner → Pipeline → FileState → Verdict := sorry
