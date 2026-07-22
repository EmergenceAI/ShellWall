import ShellWall.Semantics

/-- `IsPublic s c`: content `c` is derivable solely from public data in state `s`.
The judgment that gates public writes (`SafeCmd.write_public_ok`).

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

/-- `SafeCmd a cmd s stdin`: owner `a` may execute `cmd` in state `s` with the
given `stdin` content flowing in. The `stdin` index is threaded but UNUSED by every
rule except `write_public_ok` — only a public write's safety depends on the content
being written.

The four stream-transform commands (grep/sort/uniq/wc) touch no path directly (all
restriction is at the read/write endpoints), so they are unconditionally safe *as
commands*; their safety relevance is entirely in how they transform content, which
`IsPublic`'s transform constructors handle. -/
inductive SafeCmd : Owner → Cmd → FileState → Content → Prop where
  /-- Reading is UNCONDITIONALLY safe at the command layer. Confidentiality is
  enforced at the write boundary (via `IsPublic`), not the read boundary — reading
  private data is never itself the violation, only publishing it is. -/
  | read_ok (a : Owner) (p : Path) (s : FileState) (stdin : Content) :
      SafeCmd a (.read p) s stdin

  /-- Writing to a public (`publicRW`) path is safe iff the writer owns it AND the
  actual `stdin` content flowing in is `IsPublic`. The obligation is on the ACTUAL
  `stdin` (not an arbitrary witness): this is the Prompt 06 soundness fix — an
  unconstrained content witness let the rule fire with unrelated public content,
  which made `shellwall_noninterference` false. -/
  | write_public_ok (a : Owner) (p : Path) (mode : WriteMode) (s : FileState)
      (stdin : Content)
      (hclass : classify p = .publicRW)
      (hown : CanWrite a p)
      (hpub : IsPublic s stdin) :          -- ← the ACTUAL content written
      SafeCmd a (.write p mode) s stdin

  /-- Writing to a private (`privateRW`) path is safe iff the writer owns it — no
  `IsPublic` obligation, because a private path is not a public sink. -/
  | write_private_ok (a : Owner) (p : Path) (mode : WriteMode) (s : FileState)
      (stdin : Content)
      (hclass : classify p = .privateRW)
      (hown : CanWrite a p) :
      SafeCmd a (.write p mode) s stdin

  /-- `grep` is unconditionally safe as a command (a content transform). -/
  | grep_ok (a : Owner) (pat : String) (s : FileState) (stdin : Content) :
      SafeCmd a (.grep pat) s stdin
  /-- `sort` is unconditionally safe as a command. -/
  | sort_ok (a : Owner) (s : FileState) (stdin : Content) : SafeCmd a .sort s stdin
  /-- `uniq` is unconditionally safe as a command. -/
  | uniq_ok (a : Owner) (s : FileState) (stdin : Content) : SafeCmd a .uniq s stdin
  /-- `wc` is unconditionally safe as a command. (Its output is never certified
  public — see the `IsPublic` aggregation-omission note.) -/
  | wc_ok   (a : Owner) (s : FileState) (stdin : Content) : SafeCmd a .wc s stdin

  /-- `rm` is a destructive write and requires write-authority over the target. No
  `IsPublic` obligation (removing data cannot leak private content to a public
  sink), but `CanWrite` is mandatory — the most dangerous command in the set, never
  permitted without ownership. -/
  | rm_ok (a : Owner) (p : Path) (s : FileState) (stdin : Content)
      (hown : CanWrite a p) :
      SafeCmd a (.rm p) s stdin

  /-- `mkdir` requires write-authority over the target path. NOTE: ownership of the
  *newly created* directory is design open-question 5.4, unresolved here; for v1,
  `CanWrite a p` is the gate. -/
  | mkdir_ok (a : Owner) (p : Path) (s : FileState) (stdin : Content)
      (hown : CanWrite a p) :
      SafeCmd a (.mkdir p) s stdin

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
inductive SafePipeline : Owner → Pipeline → FileState → Content → Prop where
  /-- A single command is safe iff the command is safe. -/
  | single (a : Owner) (c : Cmd) (s : FileState) (stdin : Content) :
      SafeCmd a c s stdin → SafePipeline a (.single c) s stdin

  /-- `a | b`: `a` safe, and `b` safe in the state AFTER `a` with `a`'s stdout as
  its stdin — threaded via `evalPipelineFull` exactly as execution runs. -/
  | pipe (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content) :
      SafePipeline a p₁ s stdin →
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 (evalPipelineFull p₁ s stdin).2.1 →
      SafePipeline a (.pipe p₁ p₂) s stdin

  /-- `a ; b`: `a` safe, and `b` safe in the post-`a` state with FRESH `.empty`
  stdin (`;` is not a pipe). -/
  | seq (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content) :
      SafePipeline a p₁ s stdin →
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 .empty →
      SafePipeline a (.seq p₁ p₂) s stdin

  /-- `a && b`: BOTH branches required safe (v1 conservatism), `b` in the post-`a`
  state with fresh `.empty` stdin. PUBLIC-GUARD requirement (`hguard`): the guard
  `a` must touch only public paths, so its exit code — which decides whether `b`
  runs — is determined solely by public state. Without this the exit code is an
  implicit channel: private data could gate the public write (Prompt-13
  counterexample). Closing it is what makes noninterference true (Prompt 15). -/
  | andThen (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content)
      (hguard : touchesOnlyPublic p₁ = true) :
      SafePipeline a p₁ s stdin →
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 .empty →
      SafePipeline a (.andThen p₁ p₂) s stdin

  /-- `a || b`: BOTH branches required safe (v1 conservatism), `b` in the post-`a`
  state with fresh `.empty` stdin. PUBLIC-GUARD requirement (`hguard`), same as
  `andThen`: the guard `a` must touch only public paths so its exit code is
  public-determined, closing the implicit-flow channel through `||`. -/
  | orElse (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content)
      (hguard : touchesOnlyPublic p₁ = true) :
      SafePipeline a p₁ s stdin →
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 .empty →
      SafePipeline a (.orElse p₁ p₂) s stdin

/-- NONINTERFERENCE (the top-level security guarantee, proof deferred): if two
filesystems agree on all public paths and the same pipeline is safe in both, then
running it in either yields the same public projection — a safe pipeline cannot
leak private data into public paths. Top-level pipelines start from `.empty` stdin.

SCOPE: over the FILESYSTEM public projection only; does NOT cover stdout — see the
`THREAT MODEL — stdout (v1)` note at the top of `Semantics.lean`. -/
theorem shellwall_noninterference
    (a : Owner) (p : Pipeline) (s₁ s₂ : FileState)
    (hagree : agreeOnPublicPaths s₁ s₂)
    (h₁ : SafePipeline a p s₁ .empty) (h₂ : SafePipeline a p s₂ .empty) :
    publicProjection (evalPipeline p s₁).1 = publicProjection (evalPipeline p s₂).1 := by
  sorry
