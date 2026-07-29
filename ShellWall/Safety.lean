import ShellWall.Semantics

/-! ## TRUSTED KERNEL — the safety spec

`CanWrite`, `SafeCmd`, `SafePipeline` below are TRUSTED inductive definitions: the
guarantee is only as good as reading these and believing they capture "safe to run".
Audit them by inspection. Everything downstream (`checkFull`/`checkSafe` in Decide,
the noninterference proof further down this file) is proven RELATIVE to them and need
not be trusted directly. See the ARCHITECTURE note in `ShellWall.lean` and the
public-provenance kernel in `Provenance.lean` (`PublicProv`/`PipeProv`).

PROVENANCE, NOT A VALUE PREDICATE (design note). Public-ness of content is tracked
FORWARD, along execution, by the Bool `cmdOutIsPublic`/`provOut` (in `Semantics`),
pinned to the PATHS a stage reads, and characterized inductively by `PublicProv`
(`Provenance.lean`). A per-state value predicate of the form
`FileState → Content → Prop` as the `write_public_ok` obligation would be relationally
UNSOUND (a private value coinciding with a public path's bytes satisfies it in each
state yet differs across agreeing states — e.g. `cat /private/secret > public`);
provenance (`pub = true`) avoids this because it is pinned to the paths READ, so
agreeing states force the same value. The load-bearing omission is that
`cmdOutIsPublic`/`PublicProv` NEVER certify `wc` (or any aggregation) as public,
closing the covert statistical channel. Do NOT reintroduce a value-based public
predicate. -/

/-- `CanWrite a p`: owner `a` has write-authority over path `p`. In v1 the only
way to hold it is to own `p` outright; delegation is deferred to v2. -/
inductive CanWrite : Owner → Path → Prop where
  /-- An owner may write a path it owns (`ownerOf p = a`). The sole v1 constructor;
  delegation constructors are deferred to v2. -/
  | self (a : Owner) (p : Path) (h : ownerOf p = a) : CanWrite a p

/-- `SafeCmd a cmd s stdin pub`: owner `a` may execute `cmd` in state `s` with the
given `stdin` content flowing in, where `pub : Bool` records whether that stdin is
public-PROVENANCE (produced by reads of public paths / public-preserving transforms
— see `provOut`). Only `write_public_ok` consumes `pub`.

`write_public_ok` requires `pub = true` (provenance) rather than a per-state value
predicate. A value-based obligation would be relationally UNSOUND: a private value
coinciding with a public path's bytes satisfies it in each state separately, yet
differs across agreeing states (e.g. `cat /private/secret > public`). Provenance is
pinned to the paths READ, so agreeing states force the same value. This aligns the
spec with the decider (`checkCmd`/`cmdOutIsPublic`).

The four stream-transform commands (grep/sort/uniq/wc) touch no path directly, so
they are unconditionally safe *as commands*; their provenance effect is in
`cmdOutIsPublic`, not here. -/
inductive SafeCmd : Owner → Cmd → FileState → Content → Bool → Prop where
  /-- Reading is UNCONDITIONALLY safe at the command layer. Confidentiality is
  enforced at the write boundary, not the read boundary — reading private data is
  never itself the violation, only publishing it is. -/
  | read_ok (a : Owner) (p : Path) (s : FileState) (stdin : Content) (pub : Bool) :
      SafeCmd a (.read p) s stdin pub

  /-- Writing to a public (`publicRW`) path is safe iff the writer owns it AND the
  content flowing in is public-PROVENANCE (`pub = true`). See the type note: the
  obligation is on provenance, not per-state value (relational soundness). -/
  | write_public_ok (a : Owner) (p : Path) (mode : WriteMode) (s : FileState)
      (stdin : Content) (pub : Bool)
      (hclass : classify p = .publicRW)
      (hown : CanWrite a p)
      (hpub : pub = true) :                -- ← stdin is public-PROVENANCE
      SafeCmd a (.write p mode) s stdin pub

  /-- Writing to a private (`privateRW`) path is safe iff the writer owns it — no
  provenance obligation, because a private path is not a public sink. -/
  | write_private_ok (a : Owner) (p : Path) (mode : WriteMode) (s : FileState)
      (stdin : Content) (pub : Bool)
      (hclass : classify p = .privateRW)
      (hown : CanWrite a p) :
      SafeCmd a (.write p mode) s stdin pub

  /-- `grep` is unconditionally safe as a command (a content transform). -/
  | grep_ok (a : Owner) (pat : String) (s : FileState) (stdin : Content) (pub : Bool) :
      SafeCmd a (.grep pat) s stdin pub
  /-- `sort` is unconditionally safe as a command. -/
  | sort_ok (a : Owner) (s : FileState) (stdin : Content) (pub : Bool) : SafeCmd a .sort s stdin pub
  /-- `uniq` is unconditionally safe as a command. -/
  | uniq_ok (a : Owner) (s : FileState) (stdin : Content) (pub : Bool) : SafeCmd a .uniq s stdin pub
  /-- `wc` is unconditionally safe as a command. (Its output is never certified
  public — see `cmdOutIsPublic`.) -/
  | wc_ok   (a : Owner) (s : FileState) (stdin : Content) (pub : Bool) : SafeCmd a .wc s stdin pub

  /-- `rm` is a destructive write and requires write-authority over the target. No
  provenance obligation (removing data cannot leak private content to a public
  sink), but `CanWrite` is mandatory — the most dangerous command in the set. -/
  | rm_ok (a : Owner) (p : Path) (s : FileState) (stdin : Content) (pub : Bool)
      (hown : CanWrite a p) :
      SafeCmd a (.rm p) s stdin pub

  /-- `mkdir` requires write-authority over the target path. NOTE: ownership of the
  *newly created* directory is design open-question 5.4, unresolved here; for v1,
  `CanWrite a p` is the gate. -/
  | mkdir_ok (a : Owner) (p : Path) (s : FileState) (stdin : Content) (pub : Bool)
      (hown : CanWrite a p) :
      SafeCmd a (.mkdir p) s stdin pub

/-- `SafePipeline a pipe s stdin`: owner `a` may execute `pipe` in state `s` with
the given `stdin`. Each second stage is checked against the state AND stdin it
ACTUALLY runs in, threaded EXACTLY as `evalPipelineFull` threads them (not
`evalPipeline`, which forces `.empty` stdin) — so the safety obligations match real
execution. This is why `Safety` depends on `Semantics`.

DELIBERATE v1 CONSERVATISM: `andThen`/`orElse` require BOTH branches safe, even
though at runtime `a && b` runs `b` only on success and `a || b` only on failure.
v1 does not reason about which branch executes for the SAFETY check (sound but
conservative — it may reject a pipeline whose unsafe branch never runs). Refining
this needs ExitCode reasoning and is deferred. (Note: the *decider*'s output-public
flag IS exit-aware — see `checkFull` — but the safety judgment here is not.) -/
inductive SafePipeline : Owner → Pipeline → FileState → Content → Bool → Prop where
  /-- A single command is safe iff the command is safe (same stdin/`pub`). -/
  | single (a : Owner) (c : Cmd) (s : FileState) (stdin : Content) (pub : Bool) :
      SafeCmd a c s stdin pub → SafePipeline a (.single c) s stdin pub

  /-- `a | b`: `a` safe, and `b` safe in the state AFTER `a`, on `a`'s stdout as its
  stdin, with `pub` updated to `a`'s output provenance (`provOut p₁ s stdin pub`) —
  threaded exactly as `evalPipelineFull` and the decider run. -/
  | pipe (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content) (pub : Bool) :
      SafePipeline a p₁ s stdin pub →
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 (evalPipelineFull p₁ s stdin).2.1
        (provOut p₁ s stdin pub) →
      SafePipeline a (.pipe p₁ p₂) s stdin pub

  /-- `a ; b`: `a` safe, and `b` safe in the post-`a` state with FRESH `.empty` stdin
  and `pub = false` (a fresh terminal-empty stdin is not public-provenance). -/
  | seq (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content) (pub : Bool) :
      SafePipeline a p₁ s stdin pub →
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 .empty false →
      SafePipeline a (.seq p₁ p₂) s stdin pub

  /-- `a && b`: BOTH branches safe (v1 conservatism), `b` in the post-`a` state with
  fresh `.empty` stdin and `pub = false`. PUBLIC-GUARD requirement — the guard `a`'s
  exit code (which decides whether `b` runs) must be public-determined, so it agrees
  across states that agree on public paths. That needs BOTH:
  - `hguard`: `a` touches only public PATHS (closes the path channel);
  - `hstdin`: `a`'s incoming STDIN is public-provenance (`pub = true`) or the
    canonical empty content (`.empty`, which is constant hence trivially agrees).
    Without this, a guard like `grep` reads private data through a piped stdin and
    leaks it via the exit code. -/
  | andThen (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content) (pub : Bool)
      (hguard : touchesOnlyPublic p₁ = true)
      (hstdin : pub = true ∨ stdin = .empty) :
      SafePipeline a p₁ s stdin pub →
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 .empty false →
      SafePipeline a (.andThen p₁ p₂) s stdin pub

  /-- `a || b`: BOTH branches safe (v1 conservatism), `b` in the post-`a` state with
  fresh `.empty` stdin and `pub = false`. PUBLIC-GUARD requirement, same as
  `andThen`: the guard's exit must be public-determined — `hguard` (public paths)
  AND `hstdin` (public-provenance or empty stdin). -/
  | orElse (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content) (pub : Bool)
      (hguard : touchesOnlyPublic p₁ = true)
      (hstdin : pub = true ∨ stdin = .empty) :
      SafePipeline a p₁ s stdin pub →
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 .empty false →
      SafePipeline a (.orElse p₁ p₂) s stdin pub

/-! ## Noninterference proof infrastructure

The relational (two-execution) machinery proving `shellwall_noninterference`. Built
bottom-up: agreement algebra → command-level agreement (`evalCmd_agrees`) → the
public-program-counter lemma (`touchesOnlyPublic_agrees`) → the main relational
invariant (`eval_agrees`) → the theorem. See the `eval_agrees` docstring for where
each of the four safety requirements is consumed. -/

/-- `updateState` preserves public-path agreement when the SAME content is written to
the SAME path. -/
theorem updateState_agrees {s₁ s₂ : FileState} (p : Path) (c : Option Content)
    (hag : agreeOnPublicPaths s₁ s₂) :
    agreeOnPublicPaths (updateState s₁ p c) (updateState s₂ p c) := by
  intro q hq
  simp only [updateState]
  split
  · rfl
  · exact hag q hq

/-- Writing to a PRIVATE path preserves public-path agreement, regardless of the
(possibly differing) content written — the write cannot touch a public path. -/
theorem updateState_private_agrees {s₁ s₂ : FileState} {p : Path} (c₁ c₂ : Option Content)
    (hpriv : isPublicPath p = false) (hag : agreeOnPublicPaths s₁ s₂) :
    agreeOnPublicPaths (updateState s₁ p c₁) (updateState s₂ p c₂) := by
  intro q hq
  simp only [updateState]
  have hqp : ¬ (q = p) := by
    intro h; rw [h] at hq; rw [hpriv] at hq; exact Bool.noConfusion hq
  simp only [if_neg hqp]
  exact hag q hq

/-- `agreeOnPublicPaths` is symmetric. -/
theorem agree_symm {s₁ s₂ : FileState} (h : agreeOnPublicPaths s₁ s₂) :
    agreeOnPublicPaths s₂ s₁ := fun p hp => (h p hp).symm

/-- `agreeOnPublicPaths` is transitive. -/
theorem agree_trans {s₁ s₂ s₃ : FileState} (h₁ : agreeOnPublicPaths s₁ s₂)
    (h₂ : agreeOnPublicPaths s₂ s₃) : agreeOnPublicPaths s₁ s₃ :=
  fun p hp => (h₁ p hp).trans (h₂ p hp)

/-- Updating a PRIVATE path leaves the public projection unchanged (agrees with the
pre-update state). -/
theorem updateState_private_self {s : FileState} {q : Path} (c : Option Content)
    (hpriv : isPublicPath q = false) : agreeOnPublicPaths (updateState s q c) s := by
  intro p hp
  simp only [updateState]
  have hpq : ¬ (p = q) := by intro h; rw [h, hpriv] at hp; exact Bool.noConfusion hp
  rw [if_neg hpq]

/-- Public-path agreement gives equal public projections. -/
theorem publicProjection_eq_of_agree {s₁ s₂ : FileState} (hag : agreeOnPublicPaths s₁ s₂) :
    publicProjection s₁ = publicProjection s₂ := by
  funext p
  simp only [publicProjection]
  split
  · rename_i h; exact hag p h
  · rfl

/-- `read` leaves the state unchanged. -/
theorem evalCmd_fst_read (q : Path) (s : FileState) (stdin : Content) :
    (evalCmd (.read q) s stdin).1 = s := by simp only [evalCmd]; split <;> rfl

/-- `grep` leaves the state unchanged. -/
theorem evalCmd_fst_grep (pat : String) (s : FileState) (stdin : Content) :
    (evalCmd (.grep pat) s stdin).1 = s := by simp only [evalCmd]; split <;> rfl

/-- COMMAND-LEVEL RELATIONAL AGREEMENT (the `single` base case). For a command safe in
both runs, from agreeing states with stdin that agrees when public-provenance
(`pub = true`): the resulting states agree on public paths; the stdout is EQUAL when
the command's output is public-provenance (`cmdOutIsPublic = true`); and the output
provenance flag agrees. Consumes: the `write_public_ok` `pub = true` obligation forces
equal written content into public paths; `write_private_ok` sends (possibly differing)
content only to a private path, invisible to the projection. -/
theorem evalCmd_agrees (a : Owner) (c : Cmd) (s₁ s₂ : FileState)
    (stdin₁ stdin₂ : Content) (pub : Bool)
    (hag : agreeOnPublicPaths s₁ s₂)
    (hc₁ : SafeCmd a c s₁ stdin₁ pub) (hc₂ : SafeCmd a c s₂ stdin₂ pub)
    (hin : pub = true → stdin₁ = stdin₂) :
    agreeOnPublicPaths (evalCmd c s₁ stdin₁).1 (evalCmd c s₂ stdin₂).1
    ∧ (cmdOutIsPublic c s₁ pub = true →
        (evalCmd c s₁ stdin₁).2.1 = (evalCmd c s₂ stdin₂).2.1)
    ∧ cmdOutIsPublic c s₁ pub = cmdOutIsPublic c s₂ pub := by
  cases c with
  | read q =>
    refine ⟨?_, ?_, ?_⟩
    · rw [evalCmd_fst_read, evalCmd_fst_read]; exact hag
    · intro hp
      simp only [cmdOutIsPublic, Bool.and_eq_true] at hp
      obtain ⟨hqpub, _⟩ := hp
      simp only [evalCmd]; rw [hag q hqpub]; split <;> rfl
    · simp only [cmdOutIsPublic]
      cases hq : isPublicPath q with
      | false => rfl
      | true => rw [hag q hq]
  | write q mode =>
    cases hc₁ with
    | write_public_ok =>
      rename_i hclass hown hpub
      have hqpub : isPublicPath q = true := by simp only [isPublicPath, hclass]
      have hstdineq : stdin₁ = stdin₂ := hin hpub
      refine ⟨?_, ?_, ?_⟩
      · cases mode with
        | overwrite =>
          simp only [evalCmd]; rw [hstdineq]; exact updateState_agrees q _ hag
        | append =>
          simp only [evalCmd]; rw [hstdineq, hag q hqpub]; exact updateState_agrees q _ hag
      · intro hp; simp [cmdOutIsPublic] at hp
      · simp only [cmdOutIsPublic]
    | write_private_ok =>
      rename_i hclass hown
      have hpriv : isPublicPath q = false := by simp only [isPublicPath, hclass]
      refine ⟨?_, ?_, ?_⟩
      · simp only [evalCmd]; exact updateState_private_agrees _ _ hpriv hag
      · intro hp; simp [cmdOutIsPublic] at hp
      · simp only [cmdOutIsPublic]
  | grep pat =>
    refine ⟨?_, ?_, ?_⟩
    · rw [evalCmd_fst_grep, evalCmd_fst_grep]; exact hag
    · intro hp; simp only [cmdOutIsPublic] at hp
      have hstdineq : stdin₁ = stdin₂ := hin hp
      simp only [evalCmd]; rw [hstdineq]; split <;> rfl
    · simp only [cmdOutIsPublic]
  | sort =>
    refine ⟨hag, ?_, ?_⟩
    · intro hp; simp only [cmdOutIsPublic] at hp
      simp only [evalCmd]; rw [hin hp]
    · simp only [cmdOutIsPublic]
  | uniq =>
    refine ⟨hag, ?_, ?_⟩
    · intro hp; simp only [cmdOutIsPublic] at hp
      simp only [evalCmd]; rw [hin hp]
    · simp only [cmdOutIsPublic]
  | wc =>
    refine ⟨hag, ?_, ?_⟩
    · intro hp; simp [cmdOutIsPublic] at hp
    · simp only [cmdOutIsPublic]
  | rm q =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalCmd]
      cases hq : isPublicPath q with
      | true =>
        rw [hag q hq]; split
        · exact updateState_agrees q none hag
        · exact hag
      | false =>
        split <;> split
        · exact updateState_private_agrees none none hq hag
        · exact agree_trans (updateState_private_self none hq) hag
        · exact agree_trans hag (agree_symm (updateState_private_self none hq))
        · exact hag
    · intro hp; simp [cmdOutIsPublic] at hp
    · simp only [cmdOutIsPublic]
  | mkdir q =>
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalCmd]
      cases hq : isPublicPath q with
      | true =>
        rw [hag q hq]; split
        · exact hag
        · exact updateState_agrees q (some .empty) hag
      | false =>
        split <;> split
        · exact hag
        · exact agree_trans hag (agree_symm (updateState_private_self (some .empty) hq))
        · exact agree_trans (updateState_private_self (some .empty) hq) hag
        · exact updateState_private_agrees (some .empty) (some .empty) hq hag
    · intro hp; simp [cmdOutIsPublic] at hp
    · simp only [cmdOutIsPublic]

/-- GUARD-EXIT AGREEMENT (the `hguard` payoff). A pipeline that touches only PUBLIC
paths, run on two states agreeing on public paths WITH THE SAME stdin, produces
agreeing public state, EQUAL stdout, and EQUAL exit code. Its control flow and output
are functions of the public part of the state only — the "public program counter"
discipline. Proved by induction over the pipeline structure, so compound and nested
guards are covered automatically. -/
theorem touchesOnlyPublic_agrees (p : Pipeline) :
    ∀ (s₁ s₂ : FileState) (stdin : Content),
      touchesOnlyPublic p = true → agreeOnPublicPaths s₁ s₂ →
      agreeOnPublicPaths (evalPipelineFull p s₁ stdin).1 (evalPipelineFull p s₂ stdin).1
      ∧ (evalPipelineFull p s₁ stdin).2.1 = (evalPipelineFull p s₂ stdin).2.1
      ∧ (evalPipelineFull p s₁ stdin).2.2 = (evalPipelineFull p s₂ stdin).2.2 := by
  induction p with
  | single c =>
    intro s₁ s₂ stdin htp hag
    simp only [touchesOnlyPublic, cmdTouchesOnlyPublic] at htp
    cases c with
    | read q =>
      have hqp : s₁ q = s₂ q := hag q htp
      simp only [evalPipelineFull, evalCmd, hqp]
      split <;> exact ⟨hag, by trivial, by trivial⟩
    | write q mode =>
      have hqp : s₁ q = s₂ q := hag q htp
      cases mode with
      | overwrite =>
        simp only [evalPipelineFull, evalCmd]
        exact ⟨updateState_agrees q (some stdin) hag, by trivial, by trivial⟩
      | append =>
        simp only [evalPipelineFull, evalCmd, hqp]
        exact ⟨updateState_agrees q _ hag, by trivial, by trivial⟩
    | grep pat =>
      simp only [evalPipelineFull, evalCmd]
      split <;> exact ⟨hag, by trivial, by trivial⟩
    | sort => simp only [evalPipelineFull, evalCmd]; exact ⟨hag, by trivial, by trivial⟩
    | uniq => simp only [evalPipelineFull, evalCmd]; exact ⟨hag, by trivial, by trivial⟩
    | wc => simp only [evalPipelineFull, evalCmd]; exact ⟨hag, by trivial, by trivial⟩
    | rm q =>
      have hqp : s₁ q = s₂ q := hag q htp
      simp only [evalPipelineFull, evalCmd, hqp]
      split
      · exact ⟨updateState_agrees q none hag, by trivial, by trivial⟩
      · exact ⟨hag, by trivial, by trivial⟩
    | mkdir q =>
      have hqp : s₁ q = s₂ q := hag q htp
      simp only [evalPipelineFull, evalCmd, hqp]
      split
      · exact ⟨hag, by trivial, by trivial⟩
      · exact ⟨updateState_agrees q (some .empty) hag, by trivial, by trivial⟩
  | pipe p₁ p₂ ih₁ ih₂ =>
    intro s₁ s₂ stdin htp hag
    simp only [touchesOnlyPublic, Bool.and_eq_true] at htp
    obtain ⟨ht1, ht2⟩ := htp
    obtain ⟨ha1, ho1, _⟩ := ih₁ s₁ s₂ stdin ht1 hag
    simp only [evalPipelineFull]
    rw [ho1]
    exact ih₂ _ _ (evalPipelineFull p₁ s₂ stdin).2.1 ht2 ha1
  | seq p₁ p₂ ih₁ ih₂ =>
    intro s₁ s₂ stdin htp hag
    simp only [touchesOnlyPublic, Bool.and_eq_true] at htp
    obtain ⟨ht1, ht2⟩ := htp
    obtain ⟨ha1, _, _⟩ := ih₁ s₁ s₂ stdin ht1 hag
    simp only [evalPipelineFull]
    exact ih₂ _ _ .empty ht2 ha1
  | andThen p₁ p₂ ih₁ ih₂ =>
    intro s₁ s₂ stdin htp hag
    simp only [touchesOnlyPublic, Bool.and_eq_true] at htp
    obtain ⟨ht1, ht2⟩ := htp
    obtain ⟨ha1, ho1, he1⟩ := ih₁ s₁ s₂ stdin ht1 hag
    simp only [evalPipelineFull]
    rw [he1, ho1]
    cases hec : (evalPipelineFull p₁ s₂ stdin).2.2 with
    | success => exact ih₂ _ _ .empty ht2 ha1
    | failure n => exact ⟨ha1, rfl, rfl⟩
  | orElse p₁ p₂ ih₁ ih₂ =>
    intro s₁ s₂ stdin htp hag
    simp only [touchesOnlyPublic, Bool.and_eq_true] at htp
    obtain ⟨ht1, ht2⟩ := htp
    obtain ⟨ha1, ho1, he1⟩ := ih₁ s₁ s₂ stdin ht1 hag
    simp only [evalPipelineFull]
    rw [he1, ho1]
    cases hec : (evalPipelineFull p₁ s₂ stdin).2.2 with
    | success => exact ⟨ha1, rfl, rfl⟩
    | failure n => exact ih₂ _ _ .empty ht2 ha1

/-- THE RELATIONAL INVARIANT (main induction). For a pipeline safe in two runs from
agreeing states, with stdin that agrees when public-provenance (`pub = true`):
(1) resulting public state agrees; (2) the stdout is EQUAL when the pipeline's output
is public-provenance (`provOut = true`) — the provenance-transport payoff; (3) the
output provenance flag agrees across runs.

Where the four safety requirements are consumed:
- `evalCmd_agrees` (single/write case): the content-indexed write obligation and the
  `pub` provenance flag force equal content into public paths.
- `andThen`/`orElse`: `hguard` lets `touchesOnlyPublic_agrees` fire, and `hstdin` —
  combined across BOTH runs — forces `stdin₁ = stdin₂`, so the guard's exit agrees and
  the SAME branch runs in both. -/
theorem eval_agrees (a : Owner) (p : Pipeline) :
    ∀ (s₁ s₂ : FileState) (stdin₁ stdin₂ : Content) (pub : Bool),
      agreeOnPublicPaths s₁ s₂ →
      SafePipeline a p s₁ stdin₁ pub →
      SafePipeline a p s₂ stdin₂ pub →
      (pub = true → stdin₁ = stdin₂) →
      agreeOnPublicPaths (evalPipelineFull p s₁ stdin₁).1 (evalPipelineFull p s₂ stdin₂).1
      ∧ (provOut p s₁ stdin₁ pub = true →
          (evalPipelineFull p s₁ stdin₁).2.1 = (evalPipelineFull p s₂ stdin₂).2.1)
      ∧ provOut p s₁ stdin₁ pub = provOut p s₂ stdin₂ pub := by
  induction p with
  | single c =>
    intro s₁ s₂ stdin₁ stdin₂ pub hag hs₁ hs₂ hin
    cases hs₁ with
    | single _ _ _ _ hc₁ =>
    cases hs₂ with
    | single _ _ _ _ hc₂ =>
    exact evalCmd_agrees a c s₁ s₂ stdin₁ stdin₂ pub hag hc₁ hc₂ hin
  | pipe p₁ p₂ ih₁ ih₂ =>
    intro s₁ s₂ stdin₁ stdin₂ pub hag hs₁ hs₂ hin
    cases hs₁ with
    | pipe _ _ _ _ _ S1₁ S2₁ =>
    cases hs₂ with
    | pipe _ _ _ _ _ S1₂ S2₂ =>
    obtain ⟨ha1, hb1, hc1⟩ := ih₁ s₁ s₂ stdin₁ stdin₂ pub hag S1₁ S1₂ hin
    rw [← hc1] at S2₂
    obtain ⟨ha2, hb2, hc2⟩ :=
      ih₂ (evalPipelineFull p₁ s₁ stdin₁).1 (evalPipelineFull p₁ s₂ stdin₂).1
        (evalPipelineFull p₁ s₁ stdin₁).2.1 (evalPipelineFull p₁ s₂ stdin₂).2.1
        (provOut p₁ s₁ stdin₁ pub) ha1 S2₁ S2₂ hb1
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalPipelineFull]; exact ha2
    · simp only [evalPipelineFull, provOut]; exact hb2
    · simp only [provOut]; rw [← hc1]; exact hc2
  | seq p₁ p₂ ih₁ ih₂ =>
    intro s₁ s₂ stdin₁ stdin₂ pub hag hs₁ hs₂ hin
    cases hs₁ with
    | seq _ _ _ _ _ S1₁ S2₁ =>
    cases hs₂ with
    | seq _ _ _ _ _ S1₂ S2₂ =>
    obtain ⟨ha1, _, _⟩ := ih₁ s₁ s₂ stdin₁ stdin₂ pub hag S1₁ S1₂ hin
    obtain ⟨ha2, hb2, hc2⟩ :=
      ih₂ (evalPipelineFull p₁ s₁ stdin₁).1 (evalPipelineFull p₁ s₂ stdin₂).1
        .empty .empty false ha1 S2₁ S2₂ (fun _ => rfl)
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalPipelineFull]; exact ha2
    · simp only [evalPipelineFull, provOut]; exact hb2
    · simp only [provOut]; exact hc2
  | andThen p₁ p₂ ih₁ ih₂ =>
    intro s₁ s₂ stdin₁ stdin₂ pub hag hs₁ hs₂ hin
    cases hs₁ with
    | andThen _ _ _ _ _ hguard₁ hstdin₁ S1₁ S2₁ =>
    cases hs₂ with
    | andThen _ _ _ _ _ hguard₂ hstdin₂ S1₂ S2₂ =>
    have hstdineq : stdin₁ = stdin₂ := by
      rcases hstdin₁ with h | h
      · exact hin h
      · rcases hstdin₂ with h2 | h2
        · exact hin h2
        · rw [h, h2]
    rw [hstdineq] at S1₁ S2₁ ⊢
    obtain ⟨hga, hgo, hge⟩ := touchesOnlyPublic_agrees p₁ s₁ s₂ stdin₂ hguard₁ hag
    obtain ⟨_, _, hpc1⟩ := ih₁ s₁ s₂ stdin₂ stdin₂ pub hag S1₁ S1₂ (fun _ => rfl)
    obtain ⟨ha2, hb2, hc2⟩ :=
      ih₂ (evalPipelineFull p₁ s₁ stdin₂).1 (evalPipelineFull p₁ s₂ stdin₂).1
        .empty .empty false hga S2₁ S2₂ (fun _ => rfl)
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalPipelineFull]; rw [hge]
      cases hec : (evalPipelineFull p₁ s₂ stdin₂).2.2 with
      | success => exact ha2
      | failure n => exact hga
    · simp only [evalPipelineFull, provOut]; rw [hge]
      cases hec : (evalPipelineFull p₁ s₂ stdin₂).2.2 with
      | success => exact hb2
      | failure n => intro _; exact hgo
    · simp only [provOut]; rw [hge]
      cases hec : (evalPipelineFull p₁ s₂ stdin₂).2.2 with
      | success => exact hc2
      | failure n => exact hpc1
  | orElse p₁ p₂ ih₁ ih₂ =>
    intro s₁ s₂ stdin₁ stdin₂ pub hag hs₁ hs₂ hin
    cases hs₁ with
    | orElse _ _ _ _ _ hguard₁ hstdin₁ S1₁ S2₁ =>
    cases hs₂ with
    | orElse _ _ _ _ _ hguard₂ hstdin₂ S1₂ S2₂ =>
    have hstdineq : stdin₁ = stdin₂ := by
      rcases hstdin₁ with h | h
      · exact hin h
      · rcases hstdin₂ with h2 | h2
        · exact hin h2
        · rw [h, h2]
    rw [hstdineq] at S1₁ S2₁ ⊢
    obtain ⟨hga, hgo, hge⟩ := touchesOnlyPublic_agrees p₁ s₁ s₂ stdin₂ hguard₁ hag
    obtain ⟨_, _, hpc1⟩ := ih₁ s₁ s₂ stdin₂ stdin₂ pub hag S1₁ S1₂ (fun _ => rfl)
    obtain ⟨ha2, hb2, hc2⟩ :=
      ih₂ (evalPipelineFull p₁ s₁ stdin₂).1 (evalPipelineFull p₁ s₂ stdin₂).1
        .empty .empty false hga S2₁ S2₂ (fun _ => rfl)
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalPipelineFull]; rw [hge]
      cases hec : (evalPipelineFull p₁ s₂ stdin₂).2.2 with
      | success => exact hga
      | failure n => exact ha2
    · simp only [evalPipelineFull, provOut]; rw [hge]
      cases hec : (evalPipelineFull p₁ s₂ stdin₂).2.2 with
      | success => intro _; exact hgo
      | failure n => exact hb2
    · simp only [provOut]; rw [hge]
      cases hec : (evalPipelineFull p₁ s₂ stdin₂).2.2 with
      | success => exact hpc1
      | failure n => exact hc2

/-- NONINTERFERENCE (the top-level security guarantee): if two filesystems agree on
all public paths and the same pipeline is safe in both, then running it in either
yields the same public projection — a safe pipeline cannot leak private data into
public paths. Top-level pipelines start from `.empty` stdin.

SCOPE: over the FILESYSTEM public projection only; does NOT cover stdout — see the
`THREAT MODEL — stdout (v1)` note at the top of `Semantics.lean`.

FOUR leak channels the spec closes — each was a real counterexample to an earlier,
weaker spec, and each is defended by a specific mechanism:
- unconstrained write witness → the content-indexed `write_public_ok` obligation;
- implicit exit-code flow via a private-PATH guard → the `touchesOnlyPublic` guard;
- per-state value-predicate coincidence → provenance-based `write_public_ok` (the
  `pub = true` obligation, not a per-state value);
- implicit exit-code flow via a private-STDIN guard → the
  `hstdin : pub = true ∨ stdin = .empty` premise on `andThen`/`orElse`. Example:
  `cat /private/secret | (grep yes && (cat /shared/ref > pub))` — the guard reads
  private data through its piped stdin; `touchesOnlyPublic` checks the guard's paths
  but not its stdin, so `hstdin` is what rejects it (the conditional's incoming stdin
  is private-provenance).

With all four channels closed, this theorem is PROVED (`eval_agrees`), with a clean
axiom footprint (`propext`, `Classical.choice`, `Quot.sound` — no `sorryAx`, no
`native_decide`). Top-level pipelines start from `.empty` stdin with `pub = false`;
`.empty` counts as public-provenance for the guard-stdin check (it is constant, hence
agrees across states — the `fun _ => rfl` witness below, since `pub = false`).

PROOF: specialise the relational invariant `eval_agrees` to top-level `.empty` stdin
(where the `pub = true → stdin₁ = stdin₂` obligation is vacuous), extract its
public-state-agreement conjunct, and turn agreement into equal public projections. -/
theorem shellwall_noninterference
    (a : Owner) (p : Pipeline) (s₁ s₂ : FileState)
    (hagree : agreeOnPublicPaths s₁ s₂)
    (h₁ : SafePipeline a p s₁ .empty false) (h₂ : SafePipeline a p s₂ .empty false) :
    publicProjection (evalPipeline p s₁).1 = publicProjection (evalPipeline p s₂).1 := by
  obtain ⟨ha, _, _⟩ :=
    eval_agrees a p s₁ s₂ .empty .empty false hagree h₁ h₂ (fun _ => rfl)
  simp only [evalPipeline]
  exact publicProjection_eq_of_agree ha
