import ShellWall.Safety

/-! # UNTRUSTED DECISION LAYER (proven sound)

`canWriteB`/`checkCmd`/`checkFull`/`checkSafe` are FAST Bool decision procedures — the
untrusted layer. They are not trusted directly: `checkSafe_sound`/`checkFull_sound`
(below) prove a `true` verdict implies the trusted `SafePipeline` kernel (Safety.lean),
and `provOut_sound` (Provenance.lean) links the provenance flag they thread to the
`PublicProv` kernel. Completeness is intentionally NOT claimed — the gate may reject
some genuinely-safe pipelines. See the ARCHITECTURE note in `ShellWall.lean`. -/

/-! ## Deciding `CanWrite` -/

/-- Boolean decision of `CanWrite a p`, which in v1 reduces to `ownerOf p = a`
(`self` is `CanWrite`'s only constructor). Proved sound by `canWriteB_sound`.

TODO(v2): if delegation constructors are added to `CanWrite`, this becomes an
UNDER-approximation (rejecting writes a delegate is entitled to). Sound in that
direction, but must be revisited. -/
def canWriteB (a : Owner) (p : Path) : Bool := decide (ownerOf p = a)

-- Provenance is tracked FORWARD by `cmdOutIsPublic`/`provOut` (in `Semantics`),
-- shared by both the decider here and `SafeCmd`/`SafePipeline`. There is
-- deliberately no `isPublicB : FileState → Content → Bool` (a backward, value-based
-- decision): `Content` carries no trace of its derivation, and value-based public-ness
-- is relationally unsound anyway (a private value coinciding with a public path's bytes
-- would satisfy it). Forward provenance is the right notion.

/-! ## Deciding safety -/

/-- Boolean decision of `SafeCmd` for a single command, given stdin public-ness
`stdinPub`. Mirrors `SafeCmd`'s constructors case-for-case (which
`checkFull_sound`'s single case follows).

NOTE: the state parameter `_s` is deliberately unused. `SafeCmd`'s only state-
dependent premise is the public-provenance of `stdin`, whose decision is factored out
into `stdinPub` (computed by `cmdOutIsPublic` at the producing stage, where the state
IS consulted); `classify`/`ownerOf` are state-independent. The parameter is kept for
signature parallelism with `SafeCmd`. -/
def checkCmd (a : Owner) (c : Cmd) (_s : FileState) (stdinPub : Bool) : Bool :=
  match c with
  -- read_ok / grep_ok / sort_ok / uniq_ok / wc_ok are all unconditional
  | .read _ => true
  | .grep _ => true
  | .sort   => true
  | .uniq   => true
  | .wc     => true
  | .write p _ =>
      match classify p with
      -- write_public_ok: needs CanWrite AND public-provenance stdin (`stdinPub`).
      -- For `.append` the content written is `concatContent (s p) stdin`; since `p`
      -- is publicRW its existing content is public-provenance, so the append obligation
      -- reduces to exactly `stdinPub` -- the same check as `.overwrite`. (When
      -- `s p = none`, `concatContent .empty stdin` reduces to `stdin`, same obligation.)
      | .publicRW  => canWriteB a p && stdinPub
      -- write_private_ok: CanWrite only, no provenance obligation
      | .privateRW => canWriteB a p
      -- read-only classes: NO write rule accepts them, so no write is ever safe
      | .publicRO  => false
      | .privateRO => false
  | .rm p    => canWriteB a p
  | .mkdir p => canWriteB a p

/-- The lockstep decision walk. Returns `(isSafe, stdoutIsPublic)`, threading
filesystem state and stdin EXACTLY as `evalPipelineFull` does. Public-ness is
tracked FORWARD as provenance (`stdinPub`/`cmdOutIsPublic`), never by backward
search. The `andThen`/`orElse` output-public flag is exit-aware (branches on
stage 1's exit like the semantics), while the safety component checks both
branches (v1 conservatism, matching `SafePipeline`).

CONSEQUENCE (intended, load-bearing): `checkSafe`'s notion of "the content written"
is DEFINED by `evalPipelineFull`, so its correctness is downstream of the
semantics' fidelity — this project's central assumption. -/
def checkFull (a : Owner) : Pipeline → FileState → Content → Bool → Bool × Bool
  | .single c, s, _stdin, pub => (checkCmd a c s pub, cmdOutIsPublic c s pub)
  -- `pipe` feeds stage 1's stdout into stage 2, and stage 2 is checked in the
  -- state stage 1 left behind -- mirroring both the semantics and SafePipeline.
  | .pipe p₁ p₂, s, stdin, pub =>
      let (ok₁, pub₁) := checkFull a p₁ s stdin pub
      let (s₁, out₁, _) := evalPipelineFull p₁ s stdin
      let (ok₂, pub₂) := checkFull a p₂ s₁ out₁ pub₁
      (ok₁ && ok₂, pub₂)
  -- `;` gives stage 2 FRESH `.empty` stdin, which no constructor certifies as
  -- public, so its stdin public-ness resets to `false`.
  | .seq p₁ p₂, s, stdin, pub =>
      let (ok₁, _) := checkFull a p₁ s stdin pub
      let (s₁, _, _) := evalPipelineFull p₁ s stdin
      let (ok₂, pub₂) := checkFull a p₂ s₁ .empty false
      (ok₁ && ok₂, pub₂)
  -- MATCHES SafePipeline's DELIBERATE v1 CONSERVATISM: both branches are checked
  -- regardless of exit code, even though at runtime `&&` only runs `b` on success
  -- and `||` only on failure. v1 does not short-circuit the SAFETY check; that
  -- refinement needs ExitCode reasoning and is deferred.
  | .andThen p₁ p₂, s, stdin, pub =>
      let (ok₁, pub₁) := checkFull a p₁ s stdin pub
      let (s₁, _, ec₁) := evalPipelineFull p₁ s stdin
      let (ok₂, pub₂) := checkFull a p₂ s₁ .empty false
      -- SAFETY: both branches safe AND public-guard: `p₁` touches only public PATHS
      -- AND its incoming STDIN is public-provenance (`pub`) or `.empty` — closing the
      -- guard-stdin channel; matches SafePipeline.andThen.
      -- FAITHFUL output flag: `&&` runs stage 2 only on SUCCESS, so on failure the
      -- pipeline's output — and its flag — is stage 1's.
      (ok₁ && ok₂ && touchesOnlyPublic p₁ && (pub || decide (stdin = .empty)),
       match ec₁ with | .success => pub₂ | .failure _ => pub₁)
  | .orElse p₁ p₂, s, stdin, pub =>
      let (ok₁, pub₁) := checkFull a p₁ s stdin pub
      let (s₁, _, ec₁) := evalPipelineFull p₁ s stdin
      let (ok₂, pub₂) := checkFull a p₂ s₁ .empty false
      -- SAFETY: both branches safe AND public-guard (paths + stdin), as andThen.
      -- FAITHFUL output flag (unchanged): `||` runs stage 2 only on FAILURE, so on
      -- success the output — and its flag — is stage 1's.
      (ok₁ && ok₂ && touchesOnlyPublic p₁ && (pub || decide (stdin = .empty)),
       match ec₁ with | .success => pub₁ | .failure _ => pub₂)

/-- The v1 prove-or-reject gate's decision: `true` iff the pipeline is provably
safe. A whole pipeline starts with `.empty` stdin (nothing piped from a terminal),
not certified public — hence the initial `false`. Proved sound by `checkSafe_sound`
(soundness only; completeness is intentionally not claimed). -/
def checkSafe (a : Owner) (p : Pipeline) (s : FileState) : Bool :=
  (checkFull a p s .empty false).1

/-! ## Soundness

Soundness only: `checkSafe = true → SafePipeline`. Completeness (the converse) is
intentionally NOT claimed and is known to be unattainable -- the forward
provenance walk rejects some genuinely-safe pipelines. -/

/-- `canWriteB` is sound: if it returns `true`, `CanWrite` holds (v1: `self` is the
only constructor). -/
theorem canWriteB_sound {a : Owner} {p : Path} : canWriteB a p = true → CanWrite a p := by
  intro h
  exact CanWrite.self a p (of_decide_eq_true h)

/-- The soundness bridge, by induction mirroring the decider's walk. Two facts are
threaded together (the second feeds the first in `pipe`):
- (safety) the safety flag implies a `SafePipeline` derivation, THREADING the same
  provenance flag `pub` that the spec now consumes;
- (prov)   the decider's output flag equals `provOut` — so the flag `checkFull`
  threads into the next stage is exactly the one `SafePipeline` expects.

The write obligation is the checkable `pub = true` (no value-predicate
reconstruction), because spec and decider share the same forward-provenance notion. -/
theorem checkFull_sound (a : Owner) (p : Pipeline) :
    ∀ (s : FileState) (stdin : Content) (pub : Bool),
      ((checkFull a p s stdin pub).1 = true → SafePipeline a p s stdin pub) ∧
      ((checkFull a p s stdin pub).2 = provOut p s stdin pub) := by
  induction p with
  | single c =>
    intro s stdin pub
    refine ⟨?_, ?_⟩
    · intro hok
      apply SafePipeline.single
      simp only [checkFull] at hok
      cases c with
      | read q => exact SafeCmd.read_ok a q s stdin pub
      | grep pat => exact SafeCmd.grep_ok a pat s stdin pub
      | sort => exact SafeCmd.sort_ok a s stdin pub
      | uniq => exact SafeCmd.uniq_ok a s stdin pub
      | wc => exact SafeCmd.wc_ok a s stdin pub
      | write q mode =>
        simp only [checkCmd] at hok
        split at hok
        · rename_i hcls
          rw [Bool.and_eq_true] at hok
          exact SafeCmd.write_public_ok a q mode s stdin pub hcls (canWriteB_sound hok.1) hok.2
        · rename_i hcls
          exact SafeCmd.write_private_ok a q mode s stdin pub hcls (canWriteB_sound hok)
        · simp at hok
        · simp at hok
      | rm q => simp only [checkCmd] at hok; exact SafeCmd.rm_ok a q s stdin pub (canWriteB_sound hok)
      | mkdir q => simp only [checkCmd] at hok; exact SafeCmd.mkdir_ok a q s stdin pub (canWriteB_sound hok)
    · rfl
  | pipe p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub
    rcases h1 : checkFull a p₁ s stdin pub with ⟨ok₁, pub₁⟩
    rcases he1 : evalPipelineFull p₁ s stdin with ⟨s₁, out₁, ec₁⟩
    rcases h2 : checkFull a p₂ s₁ out₁ pub₁ with ⟨ok₂, pub₂⟩
    obtain ⟨H1safe, H1eq⟩ := ih₁ s stdin pub
    rw [h1] at H1safe H1eq
    obtain ⟨H2safe, H2eq⟩ := ih₂ s₁ out₁ pub₁
    rw [h2] at H2safe H2eq
    have hcf : checkFull a (.pipe p₁ p₂) s stdin pub = (ok₁ && ok₂, pub₂) := by
      simp only [checkFull, h1, he1, h2]
    refine ⟨?_, ?_⟩
    · simp only [hcf]; intro hok
      rw [Bool.and_eq_true] at hok
      refine SafePipeline.pipe a p₁ p₂ s stdin pub (H1safe hok.1) ?_
      rw [he1, ← H1eq]; exact H2safe hok.2
    · -- restate the flag equations at their reduced (defeq) types so `simp` matches
      have e1 : pub₁ = provOut p₁ s stdin pub := H1eq
      have e2 : pub₂ = provOut p₂ s₁ out₁ pub₁ := H2eq
      simp only [hcf, e2, provOut, he1, e1]
  | seq p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub
    rcases h1 : checkFull a p₁ s stdin pub with ⟨ok₁, pub₁⟩
    rcases he1 : evalPipelineFull p₁ s stdin with ⟨s₁, out₁, ec₁⟩
    rcases h2 : checkFull a p₂ s₁ .empty false with ⟨ok₂, pub₂⟩
    obtain ⟨H1safe, _⟩ := ih₁ s stdin pub
    rw [h1] at H1safe
    obtain ⟨H2safe, H2eq⟩ := ih₂ s₁ .empty false
    rw [h2] at H2safe H2eq
    have hcf : checkFull a (.seq p₁ p₂) s stdin pub = (ok₁ && ok₂, pub₂) := by
      simp only [checkFull, h1, he1, h2]
    refine ⟨?_, ?_⟩
    · simp only [hcf]; intro hok
      rw [Bool.and_eq_true] at hok
      refine SafePipeline.seq a p₁ p₂ s stdin pub (H1safe hok.1) ?_
      rw [he1]; exact H2safe hok.2
    · simp only [hcf, H2eq, provOut, he1]
  | andThen p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub
    rcases h1 : checkFull a p₁ s stdin pub with ⟨ok₁, pub₁⟩
    rcases he1 : evalPipelineFull p₁ s stdin with ⟨s₁, out₁, ec₁⟩
    rcases h2 : checkFull a p₂ s₁ .empty false with ⟨ok₂, pub₂⟩
    obtain ⟨H1safe, H1eq⟩ := ih₁ s stdin pub
    rw [h1] at H1safe H1eq
    obtain ⟨H2safe, H2eq⟩ := ih₂ s₁ .empty false
    rw [h2] at H2safe H2eq
    -- case on stage-1 exit so the exit-aware `.2` match resolves concretely
    cases ec₁ with
    | success =>
      have hcf : checkFull a (.andThen p₁ p₂) s stdin pub
               = (ok₁ && ok₂ && touchesOnlyPublic p₁ && (pub || decide (stdin = .empty)), pub₂) := by
        simp only [checkFull, h1, he1, h2]
      refine ⟨?_, ?_⟩
      · simp only [hcf]; intro hok
        simp only [Bool.and_eq_true] at hok
        obtain ⟨⟨⟨h_ok1, h_ok2⟩, h_g⟩, h_sd⟩ := hok
        rw [Bool.or_eq_true] at h_sd
        refine SafePipeline.andThen a p₁ p₂ s stdin pub h_g (h_sd.imp id of_decide_eq_true)
          (H1safe h_ok1) ?_
        rw [he1]; exact H2safe h_ok2
      · simp only [hcf, provOut, he1]; exact H2eq
    | failure n =>
      have hcf : checkFull a (.andThen p₁ p₂) s stdin pub
               = (ok₁ && ok₂ && touchesOnlyPublic p₁ && (pub || decide (stdin = .empty)), pub₁) := by
        simp only [checkFull, h1, he1, h2]
      refine ⟨?_, ?_⟩
      · simp only [hcf]; intro hok
        simp only [Bool.and_eq_true] at hok
        obtain ⟨⟨⟨h_ok1, h_ok2⟩, h_g⟩, h_sd⟩ := hok
        rw [Bool.or_eq_true] at h_sd
        refine SafePipeline.andThen a p₁ p₂ s stdin pub h_g (h_sd.imp id of_decide_eq_true)
          (H1safe h_ok1) ?_
        rw [he1]; exact H2safe h_ok2
      · simp only [hcf, provOut, he1]; exact H1eq
  | orElse p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub
    rcases h1 : checkFull a p₁ s stdin pub with ⟨ok₁, pub₁⟩
    rcases he1 : evalPipelineFull p₁ s stdin with ⟨s₁, out₁, ec₁⟩
    rcases h2 : checkFull a p₂ s₁ .empty false with ⟨ok₂, pub₂⟩
    obtain ⟨H1safe, H1eq⟩ := ih₁ s stdin pub
    rw [h1] at H1safe H1eq
    obtain ⟨H2safe, H2eq⟩ := ih₂ s₁ .empty false
    rw [h2] at H2safe H2eq
    cases ec₁ with
    | success =>
      have hcf : checkFull a (.orElse p₁ p₂) s stdin pub
               = (ok₁ && ok₂ && touchesOnlyPublic p₁ && (pub || decide (stdin = .empty)), pub₁) := by
        simp only [checkFull, h1, he1, h2]
      refine ⟨?_, ?_⟩
      · simp only [hcf]; intro hok
        simp only [Bool.and_eq_true] at hok
        obtain ⟨⟨⟨h_ok1, h_ok2⟩, h_g⟩, h_sd⟩ := hok
        rw [Bool.or_eq_true] at h_sd
        refine SafePipeline.orElse a p₁ p₂ s stdin pub h_g (h_sd.imp id of_decide_eq_true)
          (H1safe h_ok1) ?_
        rw [he1]; exact H2safe h_ok2
      · simp only [hcf, provOut, he1]; exact H1eq
    | failure n =>
      have hcf : checkFull a (.orElse p₁ p₂) s stdin pub
               = (ok₁ && ok₂ && touchesOnlyPublic p₁ && (pub || decide (stdin = .empty)), pub₂) := by
        simp only [checkFull, h1, he1, h2]
      refine ⟨?_, ?_⟩
      · simp only [hcf]; intro hok
        simp only [Bool.and_eq_true] at hok
        obtain ⟨⟨⟨h_ok1, h_ok2⟩, h_g⟩, h_sd⟩ := hok
        rw [Bool.or_eq_true] at h_sd
        refine SafePipeline.orElse a p₁ p₂ s stdin pub h_g (h_sd.imp id of_decide_eq_true)
          (H1safe h_ok1) ?_
        rw [he1]; exact H2safe h_ok2
      · simp only [hcf, provOut, he1]; exact H2eq

/-- SOUNDNESS of the gate: if `checkSafe` permits, the pipeline really is
`SafePipeline` (indexed by `.empty` top-level stdin, matching how `checkSafe` and
`evalPipeline` start). This is the theorem that makes a permit verdict meaningful.

Completeness (`SafePipeline → checkSafe = true`) is intentionally NOT claimed and
is unattainable in general — v1 may reject some genuinely-safe pipelines (an
accepted, deliberate limitation). -/
theorem checkSafe_sound (a : Owner) (p : Pipeline) (s : FileState) :
    checkSafe a p s = true → SafePipeline a p s .empty false := by
  intro h
  -- top-level stdin is `.empty` with provenance flag `false`
  exact (checkFull_sound a p s .empty false).1 h
