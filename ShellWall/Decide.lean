import ShellWall.Safety

/-! ## Deciding `CanWrite` -/

/-- Boolean decision of `CanWrite a p`, which in v1 reduces to `ownerOf p = a`
(`self` is `CanWrite`'s only constructor). Proved sound by `canWriteB_sound`.

TODO(v2): if delegation constructors are added to `CanWrite`, this becomes an
UNDER-approximation (rejecting writes a delegate is entitled to). Sound in that
direction, but must be revisited. -/
def canWriteB (a : Owner) (p : Path) : Bool := decide (ownerOf p = a)

/-! ## Deciding public-ness of content

WHY THERE IS NO `isPublicB : FileState → Content → Bool`.

The subprompt suggested deciding public-ness with a recursive
`isPublicB : FileState → Content → Bool` mirroring `IsPublic`'s constructors.
That signature is NOT implementable, for two independent reasons:

1. `of_public_read` needs `∃ p, isPublicPath p ∧ s p = some c`. `FileState` is a
   FUNCTION `Path → Option Content` and `Path` (`System.FilePath`) is infinite, so
   this existential cannot be decided by search.
2. `of_filter`/`of_sort` would require INVERTING `grepFilter`/`sortContent`: given
   an opaque `c`, decide whether `∃ pat c', c = grepFilter pat c'` with `c'`
   public. `Content` records no provenance, and `pat` ranges over all `String`.

`IsPublic` is not structurally recursive on `Content` -- it is an inductive
*derivation* relation, and a `Content` value carries no trace of its derivation.

WHAT IS DONE INSTEAD: public-ness is tracked as PROVENANCE along the same
lockstep walk that threads state and stdin. At each stage we know how the content
was produced, so we never have to invert anything. `cmdOutIsPublic` below is a
transcription of `IsPublic`'s constructors read FORWARDS (producer to product)
rather than backwards.
RESOLVED (was TODO 5b): that this provenance flag implies `IsPublic` — i.e. it is a
sound under-approximation — is exactly the second conjunct of `checkFull_sound`. -/

/-- Whether a command's stdout is provably public, given the state it runs in and
whether its stdin is provably public. Each case reads an `IsPublic` constructor
FORWARDS (or returns `false` where no constructor applies). Proved a sound
under-approximation by `checkFull_sound`'s output-public conjunct. -/
def cmdOutIsPublic (c : Cmd) (s : FileState) (stdinPub : Bool) : Bool :=
  match c with
  -- of_public_read needs BOTH a public class AND `s p = some c`. A read of a
  -- MISSING public path yields `.empty`, which no constructor certifies, hence
  -- the `isSome` conjunct.
  | .read p => isPublicPath p && (s p).isSome
  | .grep _ => stdinPub   -- of_filter
  | .sort   => stdinPub   -- of_sort
  -- of_uniq: uniq output is public iff its input is, same safe class as grep/sort.
  | .uniq   => stdinPub
  -- `wc` is aggregation/summarisation -- the DELIBERATE omission from `IsPublic`
  -- that guards against counting leaks. Never public.
  | .wc     => false
  -- these emit `.empty`, which no constructor certifies as public
  | .write _ _ => false
  | .rm _      => false
  | .mkdir _   => false

/-! ## Deciding safety -/

/-- Boolean decision of `SafeCmd` for a single command, given stdin public-ness
`stdinPub`. Mirrors `SafeCmd`'s constructors case-for-case (which
`checkFull_sound`'s single case follows).

NOTE: the state parameter `_s` is deliberately unused. `SafeCmd` is state-indexed,
but its only state-dependent premise is `IsPublic s stdin`, whose decision is
factored out into `stdinPub` (computed by `cmdOutIsPublic` at the producing stage,
where the state IS consulted); `classify`/`ownerOf` are state-independent. The
parameter is kept for signature parallelism with `SafeCmd`. -/
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
      -- write_public_ok: needs CanWrite AND IsPublic on the content flowing in.
      -- For `.append` the content written is `concatContent (s p) stdin`; since
      -- `p` is publicRW, the existing content is public by of_public_read, so
      -- of_concat reduces the obligation to exactly `stdinPub` -- the same check
      -- as `.overwrite`. (When `s p = none`, `concatContent .empty stdin` reduces
      -- to `stdin`, giving the same obligation.)
      | .publicRW  => canWriteB a p && stdinPub
      -- write_private_ok: CanWrite only, no IsPublic obligation
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
semantics' fidelity — this project's central assumption (§4). -/
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
      -- SAFETY: both branches safe AND the guard `p₁` touches only public paths
      -- (the public-guard requirement matching SafePipeline.andThen -- closes the
      -- exit-code implicit-flow channel; Prompt 13/14).
      -- FAITHFUL output flag (unchanged from Prompt 09): `&&` runs stage 2 only on
      -- SUCCESS, so on failure the pipeline's output — and its flag — is stage 1's.
      (ok₁ && ok₂ && touchesOnlyPublic p₁, match ec₁ with | .success => pub₂ | .failure _ => pub₁)
  | .orElse p₁ p₂, s, stdin, pub =>
      let (ok₁, pub₁) := checkFull a p₁ s stdin pub
      let (s₁, _, ec₁) := evalPipelineFull p₁ s stdin
      let (ok₂, pub₂) := checkFull a p₂ s₁ .empty false
      -- SAFETY: both branches safe AND public-only guard (as andThen).
      -- FAITHFUL output flag (unchanged): `||` runs stage 2 only on FAILURE, so on
      -- success the output — and its flag — is stage 1's.
      (ok₁ && ok₂ && touchesOnlyPublic p₁, match ec₁ with | .success => pub₁ | .failure _ => pub₂)

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

/-- `isPublicPath` is sound for `of_public_read`: if it returns `true`, the path is
classified `publicRO` or `publicRW`. -/
theorem isPublicPath_sound {p : Path} :
    isPublicPath p = true → classify p = .publicRO ∨ classify p = .publicRW := by
  intro h
  unfold isPublicPath at h
  split at h
  · rename_i hc; exact Or.inr hc
  · rename_i hc; exact Or.inl hc
  · simp at h
  · simp at h

/-- `grep`'s output state is unchanged and its stdout is exactly
`grepFilter pat stdin` — despite `evalCmd`'s inner empty-match returning a literal
`.empty` in one branch (which equals `grepFilter pat stdin` there anyway). -/
theorem grep_out (pat : String) (s : FileState) (stdin : Content) :
    (evalCmd (.grep pat) s stdin).1 = s ∧
    (evalCmd (.grep pat) s stdin).2.1 = grepFilter pat stdin := by
  simp only [evalCmd]
  split <;> simp_all

/-- The load-bearing soundness bridge, by induction mirroring the decider's own
walk. Two invariants are threaded together (the second feeds the first in `pipe`):
- (safety) the safety flag implies a `SafePipeline` derivation;
- (out-pub) the output-public flag implies the ACTUAL threaded output content
  (per `evalPipelineFull`) is `IsPublic`.

The out-pub conjunct is where the exit-aware `andThen`/`orElse` flag pays off: it
branches on `ec₁` in step with `evalPipelineFull`, so each branch discharges from
the corresponding IH. -/
theorem checkFull_sound (a : Owner) (p : Pipeline) :
    ∀ (s : FileState) (stdin : Content) (pub : Bool),
      (pub = true → IsPublic s stdin) →
      ((checkFull a p s stdin pub).1 = true → SafePipeline a p s stdin) ∧
      ((checkFull a p s stdin pub).2 = true →
        IsPublic (evalPipelineFull p s stdin).1 (evalPipelineFull p s stdin).2.1) := by
  induction p with
  | single c =>
    intro s stdin pub hpub
    constructor
    · intro hok
      apply SafePipeline.single
      simp only [checkFull] at hok
      cases c with
      | read q => exact SafeCmd.read_ok a q s stdin
      | grep pat => exact SafeCmd.grep_ok a pat s stdin
      | sort => exact SafeCmd.sort_ok a s stdin
      | uniq => exact SafeCmd.uniq_ok a s stdin
      | wc => exact SafeCmd.wc_ok a s stdin
      | write q mode =>
        simp only [checkCmd] at hok
        split at hok
        · rename_i hcls
          rw [Bool.and_eq_true] at hok
          exact SafeCmd.write_public_ok a q mode s stdin hcls (canWriteB_sound hok.1) (hpub hok.2)
        · rename_i hcls
          exact SafeCmd.write_private_ok a q mode s stdin hcls (canWriteB_sound hok)
        · simp at hok
        · simp at hok
      | rm q => simp only [checkCmd] at hok; exact SafeCmd.rm_ok a q s stdin (canWriteB_sound hok)
      | mkdir q => simp only [checkCmd] at hok; exact SafeCmd.mkdir_ok a q s stdin (canWriteB_sound hok)
    · intro hpb
      simp only [checkFull] at hpb
      simp only [evalPipelineFull]
      cases c with
      | read q =>
        simp only [cmdOutIsPublic] at hpb
        rw [Bool.and_eq_true] at hpb
        cases hsp : s q with
        | none => rw [hsp] at hpb; simp at hpb
        | some cc =>
          simp only [evalCmd, hsp]
          rcases isPublicPath_sound hpb.1 with h | h
          · exact IsPublic.of_public_read s q cc (Or.inl h) hsp
          · exact IsPublic.of_public_read s q cc (Or.inr h) hsp
      | grep pat =>
        simp only [cmdOutIsPublic] at hpb
        obtain ⟨hst, hout⟩ := grep_out pat s stdin
        rw [hst, hout]
        exact IsPublic.of_filter s stdin pat (hpub hpb)
      | sort =>
        simp only [cmdOutIsPublic] at hpb
        simp only [evalCmd]
        exact IsPublic.of_sort s stdin (hpub hpb)
      | uniq =>
        simp only [cmdOutIsPublic] at hpb
        simp only [evalCmd]
        exact IsPublic.of_uniq s stdin (hpub hpb)
      | wc => simp [cmdOutIsPublic] at hpb
      | write q mode => simp [cmdOutIsPublic] at hpb
      | rm q => simp [cmdOutIsPublic] at hpb
      | mkdir q => simp [cmdOutIsPublic] at hpb
  | pipe p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub hpub
    rcases h1 : checkFull a p₁ s stdin pub with ⟨ok₁, pub₁⟩
    rcases he1 : evalPipelineFull p₁ s stdin with ⟨s₁, out₁, ec₁⟩
    rcases h2 : checkFull a p₂ s₁ out₁ pub₁ with ⟨ok₂, pub₂⟩
    obtain ⟨H1safe, H1pub⟩ := ih₁ s stdin pub hpub
    rw [h1] at H1safe H1pub
    rw [he1] at H1pub
    obtain ⟨H2safe, H2pub⟩ := ih₂ s₁ out₁ pub₁ H1pub
    rw [h2] at H2safe H2pub
    have hcf : checkFull a (.pipe p₁ p₂) s stdin pub = (ok₁ && ok₂, pub₂) := by
      simp only [checkFull, h1, he1, h2]
    have hef : evalPipelineFull (.pipe p₁ p₂) s stdin = evalPipelineFull p₂ s₁ out₁ := by
      simp only [evalPipelineFull, he1]
    constructor
    · rw [hcf]; intro hok
      rw [Bool.and_eq_true] at hok
      refine SafePipeline.pipe a p₁ p₂ s stdin (H1safe hok.1) ?_
      rw [he1]; exact H2safe hok.2
    · rw [hcf, hef]; exact H2pub
  | seq p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub hpub
    rcases h1 : checkFull a p₁ s stdin pub with ⟨ok₁, pub₁⟩
    rcases he1 : evalPipelineFull p₁ s stdin with ⟨s₁, out₁, ec₁⟩
    rcases h2 : checkFull a p₂ s₁ .empty false with ⟨ok₂, pub₂⟩
    obtain ⟨H1safe, _⟩ := ih₁ s stdin pub hpub
    rw [h1] at H1safe
    obtain ⟨H2safe, H2pub⟩ := ih₂ s₁ .empty false (by intro hc; simp at hc)
    rw [h2] at H2safe H2pub
    have hcf : checkFull a (.seq p₁ p₂) s stdin pub = (ok₁ && ok₂, pub₂) := by
      simp only [checkFull, h1, he1, h2]
    have hef : evalPipelineFull (.seq p₁ p₂) s stdin = evalPipelineFull p₂ s₁ .empty := by
      simp only [evalPipelineFull, he1]
    constructor
    · rw [hcf]; intro hok
      rw [Bool.and_eq_true] at hok
      refine SafePipeline.seq a p₁ p₂ s stdin (H1safe hok.1) ?_
      rw [he1]; exact H2safe hok.2
    · rw [hcf, hef]; exact H2pub
  | andThen p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub hpub
    rcases h1 : checkFull a p₁ s stdin pub with ⟨ok₁, pub₁⟩
    rcases he1 : evalPipelineFull p₁ s stdin with ⟨s₁, out₁, ec₁⟩
    rcases h2 : checkFull a p₂ s₁ .empty false with ⟨ok₂, pub₂⟩
    obtain ⟨H1safe, H1pub⟩ := ih₁ s stdin pub hpub
    rw [h1] at H1safe H1pub
    rw [he1] at H1pub
    obtain ⟨H2safe, H2pub⟩ := ih₂ s₁ .empty false (by intro hc; simp at hc)
    rw [h2] at H2safe H2pub
    constructor
    · have hcf1 : (checkFull a (.andThen p₁ p₂) s stdin pub).1
                = (ok₁ && ok₂ && touchesOnlyPublic p₁) := by
        simp only [checkFull, h1, he1, h2]
      rw [hcf1]; intro hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨⟨h_ok1, h_ok2⟩, h_g⟩ := hok
      refine SafePipeline.andThen a p₁ p₂ s stdin h_g (H1safe h_ok1) ?_
      rw [he1]; exact H2safe h_ok2
    · simp only [checkFull, evalPipelineFull, h1, he1, h2]
      cases ec₁ with
      | success => exact H2pub
      | failure n => exact H1pub
  | orElse p₁ p₂ ih₁ ih₂ =>
    intro s stdin pub hpub
    rcases h1 : checkFull a p₁ s stdin pub with ⟨ok₁, pub₁⟩
    rcases he1 : evalPipelineFull p₁ s stdin with ⟨s₁, out₁, ec₁⟩
    rcases h2 : checkFull a p₂ s₁ .empty false with ⟨ok₂, pub₂⟩
    obtain ⟨H1safe, H1pub⟩ := ih₁ s stdin pub hpub
    rw [h1] at H1safe H1pub
    rw [he1] at H1pub
    obtain ⟨H2safe, H2pub⟩ := ih₂ s₁ .empty false (by intro hc; simp at hc)
    rw [h2] at H2safe H2pub
    constructor
    · have hcf1 : (checkFull a (.orElse p₁ p₂) s stdin pub).1
                = (ok₁ && ok₂ && touchesOnlyPublic p₁) := by
        simp only [checkFull, h1, he1, h2]
      rw [hcf1]; intro hok
      simp only [Bool.and_eq_true] at hok
      obtain ⟨⟨h_ok1, h_ok2⟩, h_g⟩ := hok
      refine SafePipeline.orElse a p₁ p₂ s stdin h_g (H1safe h_ok1) ?_
      rw [he1]; exact H2safe h_ok2
    · simp only [checkFull, evalPipelineFull, h1, he1, h2]
      cases ec₁ with
      | success => exact H1pub
      | failure n => exact H2pub

/-- SOUNDNESS of the gate: if `checkSafe` permits, the pipeline really is
`SafePipeline` (indexed by `.empty` top-level stdin, matching how `checkSafe` and
`evalPipeline` start). This is the theorem that makes a permit verdict meaningful.

Completeness (`SafePipeline → checkSafe = true`) is intentionally NOT claimed and
is unattainable in general — v1 may reject some genuinely-safe pipelines (an
accepted, deliberate limitation). -/
theorem checkSafe_sound (a : Owner) (p : Pipeline) (s : FileState) :
    checkSafe a p s = true → SafePipeline a p s .empty := by
  intro h
  -- top-level stdin is `.empty` with flag `false`, so the input hypothesis is vacuous
  exact (checkFull_sound a p s .empty false (by intro hc; simp at hc)).1 h
