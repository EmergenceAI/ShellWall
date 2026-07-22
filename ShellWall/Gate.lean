import ShellWall.Decide

/-- The gate's outward result: allow the pipeline, or reject it with a reason. -/
inductive Verdict where
  /-- The pipeline is permitted to run. -/
  | permit
  /-- The pipeline is rejected, with a human-readable diagnostic. -/
  | reject (reason : String)

/-- The top-level v1 entry point: prove-or-reject. Returns `.permit` iff `checkSafe`
returns `true`, else `.reject` with a diagnostic reason.

A `.permit` verdict is backed by `checkSafe_sound`: permit ⇒ the pipeline satisfies
`SafePipeline`. A `.reject` may be conservative — completeness is not claimed, so
some genuinely-safe pipelines are rejected (an accepted v1 limitation). -/
def gate (a : Owner) (p : Pipeline) (s : FileState) : Verdict :=
  if checkSafe a p s then .permit else .reject "checkSafe: no safety proof found"
