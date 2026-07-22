import ShellWall
open System

/-! # `shellwall_noninterference` is STILL FALSE (Prompt-15 blocker)

Prompt 15 asked to prove `shellwall_noninterference`, on the premise that Prompt 14
made the spec "sound and leak-free". That premise is FALSE: there is a THIRD
counterexample, independent of the Prompt-06 witness bug and the Prompt-13 implicit
flow, and independent of the Prompt-14 public-guard fix.

## The counterexample (proved below, no `sorry`)

Pipeline: `cat /private/secret > /home/alice/public/out.txt`
(`.pipe (read /private/secret) (write /public/out .overwrite)` — a plain pipe, no
conditional, so Prompt 14 doesn't touch it.)

Two states agreeing on all public paths, differing only at the private `secret`:
- `s1`: secret ↦ "PUB\n"   (coincides with the public `/shared/ref = "PUB\n"`)
- `s2`: secret ↦ "OTHER\n" (coincides with the public `/shared/other = "OTHER\n"`)

`SafePipeline` accepts this in BOTH states: the write is `write_public_ok`, whose
obligation is `IsPublic s stdin` on the ACTUAL content written (the Prompt-07 fix).
Here that content is `secret`'s value — and in EACH state that value happens to
equal some public path's content, so `IsPublic` is satisfied in each state
(`of_public_read` on `/shared/ref` in s1, on `/shared/other` in s2). Yet the write
copies `secret`'s value to a public path, which DIFFERS across the two states ⇒ the
public projection differs ⇒ noninterference is false.

## Root cause: `IsPublic` is PER-STATE, not relational

`IsPublic s c` means "c is derivable from public data in state `s`". But the same
syntactic content `c` can be PRIVATE data that merely COINCIDES with a public
value in that particular state. Across two agreeing states the private source (and
thus the written value) differs, while each value is individually "public". So a
per-state `IsPublic` obligation does NOT guarantee the written content is the same
across agreeing states — which is exactly what noninterference needs. This is the
classic "a value being public ≠ a value being independent of secrets" subtlety.

## The DECIDER is fine — only the SPEC is too weak

`checkSafe` REJECTS this pipeline in both states (`#guard`s below): `cmdOutIsPublic`
tracks PROVENANCE — reading a private path flags the output non-public
(`isPublicPath /private/secret = false`), so the downstream public write is
rejected. Since `checkSafe_sound : checkSafe → SafePipeline`, the checkSafe-accepted
set is a STRICT SUBSET of SafePipeline, and this leak lives in the gap. So:
- noninterference about `SafePipeline` (the current statement): FALSE (below).
- noninterference about the checkSafe-accepted fragment: plausibly TRUE (the
  provenance walk excludes this leak) — but that is a DIFFERENT theorem.

## Consequence (a human spec decision — not patched here)

`shellwall_noninterference` cannot be proved as stated. Two directions, both human
decisions (per the standing rule not to change the spec to fit a proof):
1. Strengthen `SafeCmd.write_public_ok` so its content obligation is PROVENANCE-
   based (built only from public *reads*, matching `cmdOutIsPublic`), aligning
   `SafePipeline` with `checkFull`. Then the per-state coincidence is ruled out.
2. Re-target the theorem to the checkSafe-accepted fragment (condition on
   `checkSafe a p .empty = true`), which already excludes this leak.

This file is a permanent regression witness. `isPublic_agrees` (public content
transports across agreeing states) is proved too — a genuine building block for
whichever fix is chosen. -/

namespace ShellWall.ExplicitFlow

def alice  : Owner := .agent "alice"
def secret : Path := "/private/secret"             -- privateRW
def shref  : Path := "/shared/ref"                 -- publicRO, "PUB\n"
def pubB   : Path := "/shared/other"               -- publicRO, "OTHER\n"
def pub    : Path := "/home/alice/public/out.txt"  -- publicRW, alice

/-- `cat /private/secret > /home/alice/public/out.txt` — copies private content to a
public path. A plain pipe (no conditional). -/
def leak2 : Pipeline := .pipe (.single (.read secret)) (.single (.write pub .overwrite))

/-- secret coincides with the public `/shared/ref`. -/
def s1 : FileState := fun p =>
  if p = secret then some (.text "PUB\n") else if p = shref then some (.text "PUB\n")
  else if p = pubB then some (.text "OTHER\n") else none
/-- secret coincides with the public `/shared/other`; agrees with s1 on every public
path, differs only at the private `secret`. -/
def s2 : FileState := fun p =>
  if p = secret then some (.text "OTHER\n") else if p = shref then some (.text "PUB\n")
  else if p = pubB then some (.text "OTHER\n") else none

/-- Public content transports across agreeing states. A building block for the
eventual (spec-fixed) noninterference proof. -/
theorem isPublic_agrees {t₁ : FileState} {c : Content} (h : IsPublic t₁ c) :
    ∀ {t₂ : FileState}, agreeOnPublicPaths t₁ t₂ → IsPublic t₂ c := by
  induction h with
  | of_public_read p c hclass hread =>
      intro t₂ hag
      have hpp : isPublicPath p = true := by
        simp only [isPublicPath]; rcases hclass with h | h <;> rw [h]
      exact IsPublic.of_public_read t₂ p c hclass (by rw [← hag p hpp]; exact hread)
  | of_concat c₁ c₂ _ _ ih₁ ih₂ => intro t₂ hag; exact IsPublic.of_concat t₂ c₁ c₂ (ih₁ hag) (ih₂ hag)
  | of_filter c pat _ ih => intro t₂ hag; exact IsPublic.of_filter t₂ c pat (ih hag)
  | of_sort c _ ih => intro t₂ hag; exact IsPublic.of_sort t₂ c (ih hag)
  | of_uniq c _ ih => intro t₂ hag; exact IsPublic.of_uniq t₂ c (ih hag)

theorem hAgree : agreeOnPublicPaths s1 s2 := by
  intro p hp
  by_cases h : p = secret
  · subst h; have hpub : isPublicPath secret = false := by native_decide
    rw [hpub] at hp; exact absurd hp (by simp)
  · simp only [s1, s2, if_neg h]

/-- SafePipeline accepts the leak in s1: the write's content ("PUB\n" = secret's
value) is `IsPublic s1` via the public `/shared/ref`. -/
theorem safe1 : SafePipeline alice leak2 s1 .empty :=
  SafePipeline.pipe alice _ _ s1 .empty
    (SafePipeline.single _ _ _ _ (SafeCmd.read_ok _ _ _ _))
    (SafePipeline.single _ _ _ _
      (SafeCmd.write_public_ok alice pub .overwrite _ _ (by native_decide)
        (CanWrite.self alice pub (by native_decide))
        (IsPublic.of_public_read _ shref (.text "PUB\n") (Or.inl (by native_decide)) (by native_decide))))

/-- SafePipeline accepts the leak in s2: the write's content ("OTHER\n" = secret's
value) is `IsPublic s2` via the public `/shared/other`. -/
theorem safe2 : SafePipeline alice leak2 s2 .empty :=
  SafePipeline.pipe alice _ _ s2 .empty
    (SafePipeline.single _ _ _ _ (SafeCmd.read_ok _ _ _ _))
    (SafePipeline.single _ _ _ _
      (SafeCmd.write_public_ok alice pub .overwrite _ _ (by native_decide)
        (CanWrite.self alice pub (by native_decide))
        (IsPublic.of_public_read _ pubB (.text "OTHER\n") (Or.inl (by native_decide)) (by native_decide))))

/-- THE BLOCKER: noninterference (the generalized statement `shellwall_noninterference`
instantiates) is FALSE. All hypotheses hold; the public projection at `pub` differs
("PUB\n" vs "OTHER\n"). No `sorry`. Axioms: the standard three plus `native_decide`
(`ofReduceBool`), forced by FilePath's kernel-irreducible `classify` (as in the
Prompt-13 witness) — NOT `sorryAx`. -/
theorem noninterference_still_false :
    ¬ (∀ (a : Owner) (p : Pipeline) (x y : FileState), agreeOnPublicPaths x y →
         SafePipeline a p x .empty → SafePipeline a p y .empty →
         publicProjection (evalPipeline p x).1 = publicProjection (evalPipeline p y).1) := by
  intro H
  have hEq := H alice leak2 s1 s2 hAgree safe1 safe2
  have hne : publicProjection (evalPipeline leak2 s1).1 pub
           ≠ publicProjection (evalPipeline leak2 s2).1 pub := by native_decide
  exact hne (congrFun hEq pub)

-- The decider correctly REJECTS the leak in both states (provenance: reading a
-- private path flags the output non-public), so the leak is in SafePipeline but NOT
-- in the checkSafe-accepted fragment.
#guard checkSafe alice leak2 s1 == false
#guard checkSafe alice leak2 s2 == false

end ShellWall.ExplicitFlow
