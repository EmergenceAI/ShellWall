import ShellWall.Decide

inductive Verdict where
  | permit
  | reject (reason : String)

-- Top-level entry point. Returns .permit iff checkSafe returns true;
-- otherwise .reject with a diagnostic reason. Body deferred.
def gate : Owner → Pipeline → FileState → Verdict := sorry
