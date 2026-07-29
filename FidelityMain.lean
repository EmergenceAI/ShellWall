import ShellWall.Fidelity

/-- Entry point for the `fidelity` executable (`lake exe fidelity`). Runs the
fidelity harness, which shells out to real bash in a temp sandbox. Kept out of
`lake build`'s default targets so the core build stays pure and hermetic. -/
def main : IO Unit := ShellWall.Fidelity.runFidelity
