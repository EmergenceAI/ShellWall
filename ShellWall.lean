-- Root of the ShellWall library. Import all submodules.
import ShellWall.Basic
import ShellWall.Syntax
import ShellWall.Policy
import ShellWall.Semantics
import ShellWall.Provenance
import ShellWall.Safety
import ShellWall.Decide
import ShellWall.Gate

/-! # ShellWall — ARCHITECTURE (trusted kernel vs. untrusted layer)

The library is deliberately split into a small TRUSTED KERNEL — inductive definitions
audited by inspection — and a larger UNTRUSTED LAYER of fast functions and models that
are believed only through soundness/fidelity, never trusted directly. The security
value rests on the kernel being small enough to read and believe.

TRUSTED BASE (audit these by eye — the whole guarantee rests on them):
- `classify`, `ownerOf`  (Policy.lean) — the policy table: which paths are public and
  who owns them. Configuration, not proof.
- `CanWrite`, `SafeCmd`, `SafePipeline`  (Safety.lean) — the inductive SAFETY spec: what
  it means for a command/pipeline to be safe to run.
- `PublicProv`, `PipeProv`  (Provenance.lean) — the inductive PUBLIC-PROVENANCE kernel:
  what it means for content to be derived only from public sources. Provenance, not
  value (the third-hole correction); no aggregation constructor (statistical-channel
  exclusion).

UNTRUSTED, BUT PROVEN SOUND against the kernel (a `true` answer yields a kernel proof):
- `cmdOutIsPublic` / `provOut`  ⟶  `cmdOutIsPublic_sound` / `provOut_sound` (Provenance).
- `checkCmd` / `checkFull` / `checkSafe`  ⟶  `checkSafe_sound` / `checkFull_sound`
  (Decide.lean): the fast prove-or-reject gate implies `SafePipeline`.

UNTRUSTED MODEL (fidelity-tested against real bash, NOT proven):
- `evalCmd` / `evalPipelineFull`  (Semantics.lean) — the execution model. The kernel
  inductives are stated relative to it (§4 central assumption); its faithfulness is
  checked by the `fidelity` executable, not proved.
- the bash→`Pipeline` parser and the executor — the two remaining unverified edges.

TOP-LEVEL GUARANTEE: `shellwall_noninterference` (Safety.lean) — a pipeline `SafePipeline`
in two states agreeing on public paths cannot leak private data into the public
projection. Proved (0 `sorry`), axiom-clean. It survived four soundness attacks; the
four historical holes and their fixes are recorded in its docstring.

So "how small is the kernel?": five inductive families (`classify`/`ownerOf` tables +
`CanWrite`/`SafeCmd`/`SafePipeline` + `PublicProv`/`PipeProv`). Everything else is a
function proven sound against them, or a model checked for fidelity. -/
