import ShellWall.Semantics

/-! # TRUSTED KERNEL — public-provenance (audit by inspection)

This module is the small, auditable inductive characterization of *public-provenance*
content: content that is DERIVED from reads of public paths through public-preserving
transforms. A reviewer audits the handful of constructors below and believes them
directly; nothing in the fast decision layer (`cmdOutIsPublic`/`provOut`,
`checkFull`/`checkSafe`) need be trusted beyond the BRIDGE theorems here
(`cmdOutIsPublic_sound`, `provOut_sound`), which prove the fast Bool functions sound
against this kernel.

PROVENANCE, NOT VALUE (the critical correction). This is deliberately NOT the deleted
value-based `IsPublic : FileState → Content → Prop` — that predicate, used as the
write obligation, was the third soundness hole (a private value coinciding with a
public path's bytes satisfied it). The difference is structural: a proposition over
`(state, content)` alone cannot tell "read from a public path" from "happens to equal
a public file's bytes." So the kernel is indexed by the COMMAND / EXECUTION that
produced the content, not by the content value. Consequently
`PublicProv (.read privatePath) s b` has NO applicable constructor even when
`s privatePath` coincides byte-for-byte with a public file — provenance is pinned to
the path actually read.

NO AGGREGATION (load-bearing omission, design §7.3). There is deliberately NO
constructor for `wc`/count/hash/statistics. Aggregation is the covert statistical
disclosure channel; certifying it public would reopen a leak. Do NOT add such a
constructor. This mirrors `cmdOutIsPublic`'s `| .wc => false`.

TRUST BOUNDARY. Trusted (audit these inductives): `PublicProv`, `PipeProv` (here);
`SafeCmd`, `SafePipeline`, `CanWrite` (Safety.lean); `classify`, `ownerOf` (Policy).
Untrusted-but-proven-sound: `cmdOutIsPublic`/`provOut`/`checkFull`/`checkSafe` (via the
bridges here + `checkSafe_sound`). Untrusted model (fidelity-tested, not proven):
`evalCmd`/`evalPipelineFull` and the parser/executor. The kernel inductives reference
the semantics (`evalPipelineFull`) as the shared execution MODEL — exactly as
`SafePipeline` does — but never reference the decision functions. -/

/-- KERNEL (command level): `PublicProv c s stdinPub` — the STDOUT of command `c`, run
in state `s` with a stdin whose public-provenance is `stdinPub`, is public-provenance.

Genuinely provenance: the only base source is reading a path that IS public
(`isPublicPath p = true`) and present; a private read has no constructor no matter the
bytes. The stream transforms preserve provenance (public in ⇒ public out), so they
require `stdinPub = true`. `wc`/`write`/`rm`/`mkdir` have NO constructor — their output
is never public-provenance (see the aggregation note). Mirrors `cmdOutIsPublic`. -/
inductive PublicProv : Cmd → FileState → Bool → Prop where
  /-- BASE: reading a PUBLIC, present path yields public-provenance stdout (any
  incoming `stdinPub`, since `read` ignores stdin). Provenance is pinned to `p`. -/
  | read (p : Path) (s : FileState) (stdinPub : Bool)
      (hpath : isPublicPath p = true) (hpresent : (s p).isSome = true) :
      PublicProv (.read p) s stdinPub
  /-- TRANSFORM: `grep` of public-provenance stdin is public-provenance. -/
  | grep (pat : String) (s : FileState) : PublicProv (.grep pat) s true
  /-- TRANSFORM: `sort` of public-provenance stdin is public-provenance. -/
  | sort (s : FileState) : PublicProv .sort s true
  /-- TRANSFORM: `uniq` of public-provenance stdin is public-provenance. -/
  | uniq (s : FileState) : PublicProv .uniq s true

/-- BRIDGE (command level): the untrusted Bool `cmdOutIsPublic` is SOUND w.r.t. the
kernel — a `true` answer yields a kernel proof. So the fast function need not be
trusted, only this theorem. (Completeness — the converse — is intentionally not
claimed; the project's stance is soundness-only.) -/
theorem cmdOutIsPublic_sound {c : Cmd} {s : FileState} {stdinPub : Bool} :
    cmdOutIsPublic c s stdinPub = true → PublicProv c s stdinPub := by
  intro h
  cases c with
  | read p =>
    simp only [cmdOutIsPublic, Bool.and_eq_true] at h
    exact PublicProv.read p s stdinPub h.1 h.2
  | grep pat => simp only [cmdOutIsPublic] at h; subst h; exact PublicProv.grep pat s
  | sort => simp only [cmdOutIsPublic] at h; subst h; exact PublicProv.sort s
  | uniq => simp only [cmdOutIsPublic] at h; subst h; exact PublicProv.uniq s
  | wc => simp [cmdOutIsPublic] at h
  | write p m => simp [cmdOutIsPublic] at h
  | rm p => simp [cmdOutIsPublic] at h
  | mkdir p => simp [cmdOutIsPublic] at h

/-- KERNEL (pipeline level): `PipeProv p s stdin pub` — the STDOUT of pipeline `p`, run
in `s` on `stdin` whose provenance is `pub`, is public-provenance. Lifts `PublicProv`
through the operators exactly as execution threads them (`evalPipelineFull`), so it
references the execution MODEL but NOT the decision functions.

The `pipe` case is the subtle one: stage 2 runs on stage 1's stdout with input
provenance `b`, and `b = true` is only allowed WITH a proof that stage 1's output is
itself public-provenance (`hb`). Without that guard the relation would be unsound
(one could spuriously claim `b = true` to satisfy a stage-2 `grep`); with it,
`cat privatefile | grep x` is correctly NOT `PipeProv`. -/
inductive PipeProv : Pipeline → FileState → Content → Bool → Prop where
  | single {c : Cmd} {s : FileState} {stdin : Content} {pub : Bool}
      (h : PublicProv c s pub) : PipeProv (.single c) s stdin pub
  | pipe {p₁ p₂ : Pipeline} {s : FileState} {stdin : Content} {pub b : Bool}
      (hb : b = true → PipeProv p₁ s stdin pub)
      (h₂ : PipeProv p₂ (evalPipelineFull p₁ s stdin).1 (evalPipelineFull p₁ s stdin).2.1 b) :
      PipeProv (.pipe p₁ p₂) s stdin pub
  | seq {p₁ p₂ : Pipeline} {s : FileState} {stdin : Content} {pub : Bool}
      (h₂ : PipeProv p₂ (evalPipelineFull p₁ s stdin).1 .empty false) :
      PipeProv (.seq p₁ p₂) s stdin pub
  | andThen_succ {p₁ p₂ : Pipeline} {s : FileState} {stdin : Content} {pub : Bool}
      (hexit : (evalPipelineFull p₁ s stdin).2.2 = .success)
      (h₂ : PipeProv p₂ (evalPipelineFull p₁ s stdin).1 .empty false) :
      PipeProv (.andThen p₁ p₂) s stdin pub
  | andThen_fail {p₁ p₂ : Pipeline} {s : FileState} {stdin : Content} {pub : Bool} {n : Nat}
      (hexit : (evalPipelineFull p₁ s stdin).2.2 = .failure n)
      (h₁ : PipeProv p₁ s stdin pub) :
      PipeProv (.andThen p₁ p₂) s stdin pub
  | orElse_succ {p₁ p₂ : Pipeline} {s : FileState} {stdin : Content} {pub : Bool}
      (hexit : (evalPipelineFull p₁ s stdin).2.2 = .success)
      (h₁ : PipeProv p₁ s stdin pub) :
      PipeProv (.orElse p₁ p₂) s stdin pub
  | orElse_fail {p₁ p₂ : Pipeline} {s : FileState} {stdin : Content} {pub : Bool} {n : Nat}
      (hexit : (evalPipelineFull p₁ s stdin).2.2 = .failure n)
      (h₂ : PipeProv p₂ (evalPipelineFull p₁ s stdin).1 .empty false) :
      PipeProv (.orElse p₁ p₂) s stdin pub

/-- BRIDGE (pipeline level): the untrusted Bool `provOut` is SOUND w.r.t. the kernel —
`provOut p s stdin pub = true` yields a `PipeProv` proof. Proved by induction mirroring
`provOut`'s recursion; each `true`-producing branch maps to exactly one kernel
constructor. This is the manager's "the interpreter hands the kernel a proof" at the
pipeline level. Soundness only (no converse). -/
theorem provOut_sound (p : Pipeline) :
    ∀ (s : FileState) (stdin : Content) (pub : Bool),
      provOut p s stdin pub = true → PipeProv p s stdin pub := by
  induction p with
  | single c =>
    intro s stdin pub h
    simp only [provOut] at h
    exact PipeProv.single (cmdOutIsPublic_sound h)
  | pipe p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub h
    simp only [provOut] at h
    exact PipeProv.pipe (b := provOut p₁ s stdin pub) (fun hb => ih₁ _ _ _ hb) (ih₂ _ _ _ h)
  | seq p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub h
    simp only [provOut] at h
    exact PipeProv.seq (ih₂ _ _ _ h)
  | andThen p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub h
    simp only [provOut] at h
    cases hexit : (evalPipelineFull p₁ s stdin).2.2 with
    | success => rw [hexit] at h; exact PipeProv.andThen_succ hexit (ih₂ _ _ _ h)
    | failure n => rw [hexit] at h; exact PipeProv.andThen_fail hexit (ih₁ _ _ _ h)
  | orElse p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub h
    simp only [provOut] at h
    cases hexit : (evalPipelineFull p₁ s stdin).2.2 with
    | success => rw [hexit] at h; exact PipeProv.orElse_succ hexit (ih₁ _ _ _ h)
    | failure n => rw [hexit] at h; exact PipeProv.orElse_fail hexit (ih₂ _ _ _ h)
