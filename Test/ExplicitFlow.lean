import ShellWall
open System

/-! # Per-state-coincidence leak — now CLOSED (regression witness)

Prompt 15 mechanically refuted `shellwall_noninterference` with this pipeline:
`cat /private/secret > /home/alice/public/out.txt`. It was `SafePipeline`-accepted
whenever `secret`'s bytes coincided with some public path's content in each state
(so the old `write_public_ok`'s per-state `IsPublic s stdin` was satisfied), yet it
copied private data to a public path — an explicit value-selection flow.

Prompt 16 CLOSED it by making `write_public_ok` require public PROVENANCE
(`pub = true`, threaded by `provOut`/`cmdOutIsPublic`) rather than a per-state
`IsPublic` value. Provenance is pinned to the paths READ: reading `/private/secret`
yields `pub = false` even when its bytes coincide with a public file's, so the
public write is no longer derivable. This aligns the spec with the already-correct
decider (`checkSafe` rejected this all along).

This file is now a permanent REGRESSION WITNESS that the leak stays closed. The
Prompt-15 refutation (`noninterference_still_false`, with its `safe1`/`safe2`
`SafePipeline` derivations) is intentionally gone: those built `write_public_ok`
from `IsPublic`, which is no longer the obligation, so they no longer typecheck —
which is the whole point. `isPublic_agrees` is kept as a reusable building block for
the Prompt-17 noninterference proof. -/

namespace ShellWall.ExplicitFlow

def alice  : Owner := .agent "alice"
def secret : Path := "/private/secret"             -- privateRW
def shref  : Path := "/shared/ref"                 -- publicRO, "PUB\n"
def pubB   : Path := "/shared/other"               -- publicRO, "OTHER\n"
def pub    : Path := "/home/alice/public/out.txt"  -- publicRW, alice

/-- `cat /private/secret > /home/alice/public/out.txt` — the Prompt-15 leak. -/
def leak2 : Pipeline := .pipe (.single (.read secret)) (.single (.write pub .overwrite))

def s1 : FileState := fun p =>
  if p = secret then some (.text "PUB\n") else if p = shref then some (.text "PUB\n")
  else if p = pubB then some (.text "OTHER\n") else none
def s2 : FileState := fun p =>
  if p = secret then some (.text "OTHER\n") else if p = shref then some (.text "PUB\n")
  else if p = pubB then some (.text "OTHER\n") else none

/-- Public content transports across agreeing states — a reusable building block for
the Prompt-17 noninterference proof. (`IsPublic` is retained for exactly this.) -/
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

-- The read of the private `secret` is NOT public-provenance, even though its bytes
-- coincide with the public `/shared/ref` — provenance is pinned to the path read:
#guard cmdOutIsPublic (.read secret) s1 false == false

-- ⇒ the write's stdin has `pub = false`, so `write_public_ok` (which now requires
-- `pub = true`) is unsatisfiable: `SafePipeline alice leak2 s1 .empty false` is NO
-- LONGER DERIVABLE (the old `safe1`/`safe2` above no longer typecheck), and the
-- decider rejects it in both states — spec and decider now agree.
#guard checkSafe alice leak2 s1 == false
#guard checkSafe alice leak2 s2 == false

end ShellWall.ExplicitFlow
