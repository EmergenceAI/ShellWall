import ShellWall.Semantics

-- IsPublic s c: content c is derivable solely from public data in state s.
--
-- DELIBERATE OMISSION: no constructor derives IsPublic from aggregation or
-- summarization of private content (counts, hashes, samples, statistics).
-- This omission is load-bearing: it is the primary mechanism preventing
-- information leakage through covert statistical channels.
inductive IsPublic : FileState → Content → Prop where
  | of_public_read (s : FileState) (p : Path) (c : Content)
      (hclass : classify p = .publicRO ∨ classify p = .publicRW)
      (hread  : s p = some c) :
      IsPublic s c
  | of_concat (s : FileState) (c₁ c₂ : Content) :
      IsPublic s c₁ → IsPublic s c₂ → IsPublic s (concatContent c₁ c₂)
  | of_filter (s : FileState) (c : Content) (pat : String) :
      IsPublic s c → IsPublic s (grepFilter pat c)
  | of_sort (s : FileState) (c : Content) :
      IsPublic s c → IsPublic s (sortContent c)
  -- of_uniq is in the SAME safe class as of_filter/of_sort: `uniq` (adjacent
  -- dedup) reveals no more than `grep` already does, so uniq-ing public content
  -- keeps it public. Uses the same `uniqContent` helper as `evalCmd`'s uniq case,
  -- so `checkSafe`'s uniq handling and this constructor agree on "uniq output".
  -- It is deliberately NOT in the same class as `wc`: no wc/count/hash
  -- constructor exists, and that aggregation omission remains load-bearing as a
  -- disclosure-leak exclusion (§7.3).
  | of_uniq (s : FileState) (c : Content) :
      IsPublic s c → IsPublic s (uniqContent c)

inductive CanWrite : Owner → Path → Prop where
  | self (a : Owner) (p : Path) (h : ownerOf p = a) : CanWrite a p
  -- delegation constructors deferred to v2

-- SafeCmd a cmd s stdin: owner a may execute cmd in state s with the given stdin
-- content flowing in.
--
-- The `stdin` index is threaded but UNUSED by every rule except write_public_ok:
-- only a public write's safety depends on the content being written. This is the
-- fix for the falsified-noninterference hole (Prompt 06): write_public_ok's
-- IsPublic obligation is now tied to the ACTUAL `stdin` being written, so the
-- rule can no longer fire by choosing an arbitrary unrelated public witness.
--
-- The four stream-transform commands (grep, sort, uniq, wc) touch no path
-- directly -- all real restriction happens at the read/write endpoints -- so
-- they are unconditionally safe as commands. This is a deliberate decision:
-- their safety relevance is entirely in how they transform *content* (handled
-- by IsPublic's of_filter/of_sort/of_uniq constructors), not in command-level
-- access control.
inductive SafeCmd : Owner → Cmd → FileState → Content → Prop where
  | read_ok (a : Owner) (p : Path) (s : FileState) (stdin : Content) :
      SafeCmd a (.read p) s stdin
      -- reads are unconditionally permitted at the command layer;
      -- confidentiality restriction enters only at write time, via IsPublic.
      -- (Reading private data is never itself the violation -- only publishing it is.)

  | write_public_ok (a : Owner) (p : Path) (mode : WriteMode) (s : FileState)
      (stdin : Content)
      (hclass : classify p = .publicRW)
      (hown : CanWrite a p)
      (hpub : IsPublic s stdin) :          -- ← the ACTUAL content written
      SafeCmd a (.write p mode) s stdin

  | write_private_ok (a : Owner) (p : Path) (mode : WriteMode) (s : FileState)
      (stdin : Content)
      (hclass : classify p = .privateRW)
      (hown : CanWrite a p) :
      SafeCmd a (.write p mode) s stdin

  | grep_ok (a : Owner) (pat : String) (s : FileState) (stdin : Content) :
      SafeCmd a (.grep pat) s stdin
  | sort_ok (a : Owner) (s : FileState) (stdin : Content) : SafeCmd a .sort s stdin
  | uniq_ok (a : Owner) (s : FileState) (stdin : Content) : SafeCmd a .uniq s stdin
  | wc_ok   (a : Owner) (s : FileState) (stdin : Content) : SafeCmd a .wc s stdin

  | rm_ok (a : Owner) (p : Path) (s : FileState) (stdin : Content)
      (hown : CanWrite a p) :
      SafeCmd a (.rm p) s stdin
      -- rm is a destructive write; it requires write-authority over the target.
      -- No IsPublic obligation (removing data cannot leak private content to a
      -- public sink), but CanWrite is mandatory -- this is the most dangerous
      -- command in the set and must never be permitted without ownership.

  | mkdir_ok (a : Owner) (p : Path) (s : FileState) (stdin : Content)
      (hown : CanWrite a p) :
      SafeCmd a (.mkdir p) s stdin
      -- mkdir requires write-authority over the target path. NOTE: ownership of
      -- the *newly created* directory is governed by open question 5.4 and is
      -- not resolved here; for v1, CanWrite a p is the gate.

-- SafePipeline a pipe s stdin: owner a may execute the pipeline in state s with
-- the given stdin content.
--
-- Each second stage is checked against the state AND stdin it actually runs in,
-- threaded EXACTLY as `evalPipelineFull` threads them (not `evalPipeline`, which
-- forces `.empty` stdin). This also fixes the right-nested-pipe mismatch flagged
-- in Prompt 06: `a | (b | c)` now checks `c` against the real threaded state,
-- not a `.empty`-stdin one. This is why Safety depends on Semantics.
--   • pipe: stage 2 gets stage 1's stdout as its stdin, in the post-stage-1 state
--   • seq/andThen/orElse: stage 2 gets FRESH `.empty` stdin (not a pipe), in the
--     post-stage-1 state
--
-- DELIBERATE v1 CONSERVATISM: andThen (&&) and orElse (||) require *both*
-- branches safe, even though at runtime `a && b` only runs b when a succeeds
-- and `a || b` only runs b when a fails. v1 demands both branches be safe
-- unconditionally rather than reasoning about which branch actually executes.
-- This is sound (it never permits an unsafe execution) but conservative (it
-- rejects some pipelines whose unsafe branch never runs). Refining this
-- requires evalPipeline's ExitCode semantics and is deferred.
inductive SafePipeline : Owner → Pipeline → FileState → Content → Prop where
  | single (a : Owner) (c : Cmd) (s : FileState) (stdin : Content) :
      SafeCmd a c s stdin → SafePipeline a (.single c) s stdin

  | pipe (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content) :
      SafePipeline a p₁ s stdin →
      -- stage 2 runs in the state AFTER p₁, on p₁'s stdout as its stdin
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 (evalPipelineFull p₁ s stdin).2.1 →
      SafePipeline a (.pipe p₁ p₂) s stdin

  | seq (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content) :
      SafePipeline a p₁ s stdin →
      -- ';' gives stage 2 fresh empty stdin, in the post-p₁ state
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 .empty →
      SafePipeline a (.seq p₁ p₂) s stdin

  | andThen (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content) :
      SafePipeline a p₁ s stdin →
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 .empty →
      SafePipeline a (.andThen p₁ p₂) s stdin

  | orElse (a : Owner) (p₁ p₂ : Pipeline) (s : FileState) (stdin : Content) :
      SafePipeline a p₁ s stdin →
      SafePipeline a p₂ (evalPipelineFull p₁ s stdin).1 .empty →
      SafePipeline a (.orElse p₁ p₂) s stdin

-- Noninterference: if two states agree on all public paths, and the same
-- pipeline is safe in both, then running it in either state produces the same
-- public projection. Proof deferred.
--
-- SCOPE: this guarantee is over the FILESYSTEM public projection only and does
-- NOT cover stdout -- see the `THREAT MODEL — stdout (v1)` note at the top of
-- Semantics.lean.
-- Top-level pipelines start from `.empty` stdin (nothing piped from a terminal),
-- matching how `evalPipeline`/`checkSafe` begin.
theorem shellwall_noninterference
    (a : Owner) (p : Pipeline) (s₁ s₂ : FileState)
    (hagree : agreeOnPublicPaths s₁ s₂)
    (h₁ : SafePipeline a p s₁ .empty) (h₂ : SafePipeline a p s₂ .empty) :
    publicProjection (evalPipeline p s₁).1 = publicProjection (evalPipeline p s₂).1 := by
  sorry
