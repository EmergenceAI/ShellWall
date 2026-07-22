import ShellWall
open System

/-! # Implicit-flow counterexample: `shellwall_noninterference` is FALSE

This investigation (Prompt 13) mechanically REFUTES `shellwall_noninterference` as
stated. It is independent of the witness bug fixed in Prompt 07 — that fix tied the
public-write obligation to the actual content, closing an *explicit* flow. This is
an *implicit* flow: private data influences public output by controlling WHETHER a
write happens, never by copying its bytes.

## The counterexample

Pipeline (bash): `(cat /private/secret | grep -F match) && (cat /shared/ref > /home/alice/public/out.txt)`

An `andThen` whose left branch's exit code depends on private content (does the
secret contain "match"?), gating whether the right branch's public write runs.

Two states agreeing on all PUBLIC paths, differing only at the private
`/private/secret`:
- `s1`: secret ↦ "match\n"  → grep matches → left exits success → write RUNS.
- `s2`: secret ↦ "xxx\n"    → grep no match → left exits failure → write SKIPPED.

Both hold `/shared/ref ↦ "PUB\n"` and are identical on every public path.

All four conditions hold (all machine-checked below):
1. `agreeOnPublicPaths s1 s2` — they differ only at a private path.
2/3. `SafePipeline` is derivable in BOTH states — obtained here straight from the
     proven `checkSafe_sound`, so the pipeline is accepted HONESTLY: the write is
     justified by `/shared/ref`'s public content via `of_public_read`, not by any
     residual witness loophole.
4. The public projections DIFFER at `/home/alice/public/out.txt`: `some "PUB\n"`
   in s1 (write ran) vs `none` in s2 (write skipped).

⇒ private data (via the exit code) determined public state. Noninterference is
false as stated.

## Axioms — why not the three standard ones

The proof uses `native_decide` (axiom family `_native.native_decide.ax_*`, i.e.
`Lean.ofReduceBool` — NOT `sorryAx`). This is FORCED by the Prompt-10 `FilePath`
migration: `classify`/`isPublicPath` go through `FilePath.components` →
`String.splitOn`, which the KERNEL cannot reduce on concrete literals (`rfl` and
kernel `decide` get stuck; only `native_decide` — trusting the compiler — closes
them). With the old `List String` paths, Prompt 06's analogous refutation was
kernel-clean. `native_decide` is a standard, sound Lean mechanism (the same
evaluation `#eval`/`#guard`/the fidelity harness use); it does not weaken the
result. A kernel-clean proof would require either reverting the path type (a spec
change, out of scope) or symbolic `String.splitOn`/`components` lemmas.

## Scope of the gap (facts for the design decision)
- The leak is exactly ONE BIT per conditional (grep matched or not). Several
  conditionals — or a loop — would amplify it to many bits.
- It is specific to `andThen`/`orElse`, which gate execution on an exit code.
  `seq` and `pipe` always run their second stage, so no "whether the write
  happens" channel exists (the `seqControl` guard below confirms seq does NOT
  leak: identical public output in both states). `pipe` can still carry an
  *explicit* content flow, but that is the flow `IsPublic`/`write_public_ok`
  already govern.
- `checkSafe`/`gate` PERMIT this pipeline in both states (guards below): the gate
  has the same implicit-flow gap as the spec — expected, since every branch is
  individually safe and `checkSafe` is sound w.r.t. the (gappy) spec, not stronger.

No spec/decider/semantics/`sorry` was changed; this file only ADDS the finding. -/

namespace ShellWall.ImplicitFlow

def alice  : Owner := .agent "alice"
def secret : Path := "/private/secret"        -- privateRW
def shref  : Path := "/shared/ref"            -- publicRO
def outp   : Path := "/home/alice/public/out.txt"  -- publicRW, alice

/-- Left branch: `cat /private/secret | grep -F match` — its exit depends on the
private content. -/
def leftB  : Pipeline := .pipe (.single (.read secret)) (.single (.grep "match"))
/-- Right branch: `cat /shared/ref > /home/alice/public/out.txt` — a public write
of public content. -/
def rightB : Pipeline := .pipe (.single (.read shref)) (.single (.write outp .overwrite))
/-- The leaking pipeline: `left && right`. -/
def thePipeline : Pipeline := .andThen leftB rightB
/-- Control: the same branches under `;` (unconditional) — does NOT leak. -/
def seqControl : Pipeline := .seq leftB rightB

/-- grep matches → left succeeds → the public write runs. -/
def s1 : FileState := fun p =>
  if p = secret then some (.text "match\n") else if p = shref then some (.text "PUB\n") else none
/-- grep fails → left fails → the public write is skipped. -/
def s2 : FileState := fun p =>
  if p = secret then some (.text "xxx\n")   else if p = shref then some (.text "PUB\n") else none

-- The gate PERMITS the leaking pipeline in both states (documents the gate gap):
#guard checkSafe alice thePipeline s1 == true
#guard checkSafe alice thePipeline s2 == true

-- The `andThen` output DIFFERS at outp between the two states — the leak:
#guard decide ((evalPipeline thePipeline s1).1 outp = (evalPipeline thePipeline s2).1 outp) == false

-- The `seq` control does NOT leak: identical public output in both states.
#guard decide ((evalPipeline seqControl s1).1 outp = (evalPipeline seqControl s2).1 outp) == true

/-- (1) The two states agree on every public path (they differ only at the private
`/private/secret`). -/
theorem hAgree : agreeOnPublicPaths s1 s2 := by
  intro p hp
  by_cases h : p = secret
  · subst h
    have hpub : isPublicPath secret = false := by native_decide
    rw [hpub] at hp; exact absurd hp (by simp)
  · simp only [s1, s2, if_neg h]

/-- (2) `SafePipeline` in `s1`, obtained from the proven `checkSafe_sound` — so the
pipeline is accepted honestly by the real gate. -/
theorem hSafe1 : SafePipeline alice thePipeline s1 .empty :=
  checkSafe_sound alice thePipeline s1 (by native_decide)

/-- (3) `SafePipeline` in `s2`, likewise. -/
theorem hSafe2 : SafePipeline alice thePipeline s2 .empty :=
  checkSafe_sound alice thePipeline s2 (by native_decide)

/-- (4) THE REFUTATION: noninterference (in the generalized form
`shellwall_noninterference` is an instance of) is FALSE. All hypotheses hold, yet
the public projections differ. No `sorry`; axioms are the three standard ones plus
`native_decide`'s `ofReduceBool` (see the file header for why). -/
theorem noninterference_false_via_implicit_flow :
    ¬ (∀ (a : Owner) (p : Pipeline) (x y : FileState), agreeOnPublicPaths x y →
         SafePipeline a p x .empty → SafePipeline a p y .empty →
         publicProjection (evalPipeline p x).1 = publicProjection (evalPipeline p y).1) := by
  intro H
  have hEq := H alice thePipeline s1 s2 hAgree hSafe1 hSafe2
  have hne : publicProjection (evalPipeline thePipeline s1).1 outp
           ≠ publicProjection (evalPipeline thePipeline s2).1 outp := by native_decide
  exact hne (congrFun hEq outp)

end ShellWall.ImplicitFlow
