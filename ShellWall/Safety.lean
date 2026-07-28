import ShellWall.Semantics

/-- `IsPublic s c`: content `c` is derivable solely from public data in state `s`.

NOTE (Prompt 16): this is NO LONGER the write obligation — `write_public_ok` now
requires public PROVENANCE (`pub = true`), because a per-state `IsPublic` value is
relationally unsound (a private value coinciding with a public one satisfies it; see
`Test/ExplicitFlow.lean`). `IsPublic` is retained as a reusable building block for
the noninterference proof (`isPublic_agrees`: public content transports across
agreeing states), not as a safety gate.

⚠ DELIBERATE OMISSION — LOAD-BEARING (design §3.2/§7.3): there is NO constructor
deriving `IsPublic` from aggregation or summarization of private content (counts,
hashes, samples, statistics — anything `wc`-like). This omission is the primary
mechanism preventing leakage through covert statistical channels. Do NOT
"helpfully" add such a constructor: it would make the whole guarantee unsound. The
present constructors are exactly the "safe transform" class (identity-preserving of
public-ness) plus the public-read base case. -/
inductive IsPublic : FileState → Content → Prop where
  /-- BASE CASE: content read from a path classified public (`publicRO`/`publicRW`)
  is public. -/
  | of_public_read (s : FileState) (p : Path) (c : Content)
      (hclass : classify p = .publicRO ∨ classify p = .publicRW)
      (hread  : s p = some c) :
      IsPublic s c
  /-- Concatenation of two public contents is public (`cat` of public sources). -/
  | of_concat (s : FileState) (c₁ c₂ : Content) :
      IsPublic s c₁ → IsPublic s c₂ → IsPublic s (concatContent c₁ c₂)
  /-- SAFE TRANSFORM: filtering public content through `grep` keeps it public. -/
  | of_filter (s : FileState) (c : Content) (pat : String) :
      IsPublic s c → IsPublic s (grepFilter pat c)
  /-- SAFE TRANSFORM: sorting public content keeps it public. -/
  | of_sort (s : FileState) (c : Content) :
      IsPublic s c → IsPublic s (sortContent c)
  /-- SAFE TRANSFORM: `uniq` of public content is public — same safe class as
  `of_filter`/`of_sort` (adjacent dedup reveals no more than `grep` already does).
  Uses the same `uniqContent` helper as `evalCmd`'s uniq case, so `checkSafe`'s uniq
  handling and this constructor agree on "uniq output". Deliberately NOT the same
  class as `wc`: no aggregation/count constructor exists (see the type note). -/
  | of_uniq (s : FileState) (c : Content) :
      IsPublic s c → IsPublic s (uniqContent c)

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

PROMPT-16 FIX: `write_public_ok` now requires `pub = true` (provenance) rather than
`IsPublic s stdin` (value). The value-based obligation was relationally UNSOUND: a
private value coinciding with a public path's bytes satisfied `IsPublic` in each
state separately, yet differed across agreeing states (the Prompt-15 counterexample
`cat /private/secret > public`). Provenance is pinned to the paths READ, so agreeing
states force the same value. This aligns the spec with the already-correct decider
(`checkCmd`/`cmdOutIsPublic`). `IsPublic` is retained (see `isPublic_agrees`) but is
no longer the write obligation.

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
  content flowing in is public-PROVENANCE (`pub = true`). See the type note: this is
  the Prompt-16 relational-soundness fix (provenance, not per-state value). -/
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
  - `hguard`: `a` touches only public PATHS (Prompt 14 — closes the path channel);
  - `hstdin`: `a`'s incoming STDIN is public-provenance (`pub = true`) or the
    canonical empty content (`.empty`, which is constant hence trivially agrees).
    NEW (Prompt 21): without this, a guard like `grep` reads private data through a
    piped stdin and leaks it via the exit code — the fourth counterexample. -/
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

/-- NONINTERFERENCE (the top-level security guarantee): if two filesystems agree on
all public paths and the same pipeline is safe in both, then running it in either
yields the same public projection — a safe pipeline cannot leak private data into
public paths. Top-level pipelines start from `.empty` stdin.

SCOPE: over the FILESYSTEM public projection only; does NOT cover stdout — see the
`THREAT MODEL — stdout (v1)` note at the top of `Semantics.lean`.

SPEC HISTORY — FOUR leaks found and closed, each a machine-checked counterexample
before its fix:
- unconstrained write witness (Prompt 06 → fixed Prompt 07);
- implicit exit-code flow via a private-PATH guard (Prompt 13 → `touchesOnlyPublic`
  guard, Prompt 14);
- per-state `IsPublic` coincidence (Prompt 15 → provenance-based `write_public_ok`,
  Prompt 16);
- implicit exit-code flow via a private-STDIN guard (Prompt 20 →
  `hstdin : pub = true ∨ stdin = .empty` on `andThen`/`orElse`, Prompt 21):
  `cat /private/secret | (grep yes && (cat /shared/ref > pub))` — the guard reads
  private data through its piped stdin; `touchesOnlyPublic` checks the guard's paths
  but not its stdin. Now REJECTED (the conditional's incoming stdin is
  private-provenance).

With all FOUR known holes closed, this theorem is BELIEVED PROVABLE (pending the
next proof attempt). Top-level pipelines start from `.empty` stdin with `pub = false`;
`.empty` counts as public-provenance for the guard-stdin check (it is constant,
hence agrees across states). -/
theorem shellwall_noninterference
    (a : Owner) (p : Pipeline) (s₁ s₂ : FileState)
    (hagree : agreeOnPublicPaths s₁ s₂)
    (h₁ : SafePipeline a p s₁ .empty false) (h₂ : SafePipeline a p s₂ .empty false) :
    publicProjection (evalPipeline p s₁).1 = publicProjection (evalPipeline p s₂).1 := by
  sorry
