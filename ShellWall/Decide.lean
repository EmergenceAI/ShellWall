import ShellWall.Safety

/-! ## Deciding `CanWrite` -/

-- `CanWrite a p` reduces to `ownerOf p = a`: `self` is the only constructor in
-- v1, and its sole premise is that equation.
-- TODO(v2): if delegation constructors are added to `CanWrite`, this becomes an
-- UNDER-approximation (it would reject writes a delegate is entitled to). It
-- stays sound in that direction, but must be revisited.
def canWriteB (a : Owner) (p : Path) : Bool := decide (ownerOf p = a)

/-! ## Deciding public-ness of content

WHY THERE IS NO `isPublicB : FileState → Content → Bool`.

The subprompt suggested deciding public-ness with a recursive
`isPublicB : FileState → Content → Bool` mirroring `IsPublic`'s constructors.
That signature is NOT implementable, for two independent reasons:

1. `of_public_read` needs `∃ p, isPublicPath p ∧ s p = some c`. `FileState` is a
   FUNCTION `Path → Option Content` and `Path = List String` is infinite, so this
   existential cannot be decided by search.
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
TODO(5b): prove `cmdOutIsPublic`/`checkFull`'s public flag implies `IsPublic`,
i.e. that this provenance tracking is a sound under-approximation. -/

-- Public-ness of a command's stdout, given the state it runs in and whether its
-- stdin is provably public. Each case is justified by an `IsPublic` constructor
-- (or the absence of one).
def cmdOutIsPublic (c : Cmd) (s : FileState) (stdinPub : Bool) : Bool :=
  match c with
  -- of_public_read needs BOTH a public class AND `s p = some c`. A read of a
  -- MISSING public path yields `.empty`, which no constructor certifies, hence
  -- the `isSome` conjunct.
  | .read p => isPublicPath p && (s p).isSome
  | .grep _ => stdinPub   -- of_filter
  | .sort   => stdinPub   -- of_sort
  -- of_uniq (added this prompt): uniq output is public iff its input is, same as
  -- grep/sort. This is the one decider change the of_uniq spec addition forces --
  -- it was `false` in Prompt 06 (no of_uniq existed then), which is why case 9c
  -- rejected. Flipping it to `stdinPub` keeps the decider aligned with the
  -- extended IsPublic and makes 9c permit, as required.
  | .uniq   => stdinPub   -- of_uniq
  -- `wc` is aggregation/summarisation -- the DELIBERATE omission from `IsPublic`
  -- that guards against counting leaks. Never public.
  | .wc     => false
  -- these emit `.empty`, which no constructor certifies as public
  | .write _ _ => false
  | .rm _      => false
  | .mkdir _   => false

/-! ## Deciding safety -/

-- Safety of a single command in state `_s` with stdin public-ness `stdinPub`.
-- Mirrors `SafeCmd`'s constructors.
--
-- NOTE: `_s` is deliberately unused. `SafeCmd a c s` is indexed by the state, but
-- the only state-dependent premise is `IsPublic s c`, whose decision has been
-- factored out into `stdinPub` (computed by `cmdOutIsPublic` at the producing
-- stage, where the state IS consulted). `classify`/`ownerOf` are state-
-- independent policy. The parameter is kept for signature parallelism with
-- `SafeCmd`, which Phase 5c's proof will follow case-for-case.
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

-- Lockstep walk. Returns `(isSafe, stdoutIsPublic)`, threading filesystem state
-- and stdin exactly as `evalPipelineFull` does.
--
-- CONSEQUENCE (intended, but load-bearing): `checkSafe`'s notion of "the content
-- written" is DEFINED by `evalPipelineFull`, i.e. by the execution model. Safety
-- is checked against what the model says actually happens, so `checkSafe`'s
-- correctness is downstream of the semantics' fidelity -- already this project's
-- central assumption (§4 / Smoosh differential-testing requirement).
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
      let (ok₁, _) := checkFull a p₁ s stdin pub
      let (s₁, _, _) := evalPipelineFull p₁ s stdin
      let (ok₂, pub₂) := checkFull a p₂ s₁ .empty false
      (ok₁ && ok₂, pub₂)
  | .orElse p₁ p₂, s, stdin, pub =>
      let (ok₁, _) := checkFull a p₁ s stdin pub
      let (s₁, _, _) := evalPipelineFull p₁ s stdin
      let (ok₂, pub₂) := checkFull a p₂ s₁ .empty false
      (ok₁ && ok₂, pub₂)

-- A whole pipeline starts with `.empty` stdin (nothing piped from a terminal),
-- which is not certified public -- hence the initial `false`.
def checkSafe (a : Owner) (p : Pipeline) (s : FileState) : Bool :=
  (checkFull a p s .empty false).1

-- Soundness: if checkSafe approves, the pipeline is genuinely safe.
-- This direction is required and must be proved when the body is filled in.
--
-- Completeness (SafePipeline → checkSafe = true) is NOT a goal and is known
-- to be unattainable in general. Some genuinely safe pipelines will be
-- rejected by the v1 procedure; this is an accepted, deliberate limitation.
-- The conclusion is indexed by `.empty` top-level stdin, matching how `checkSafe`
-- and `evalPipeline` both start.
theorem checkSafe_sound (a : Owner) (p : Pipeline) (s : FileState) :
    checkSafe a p s = true → SafePipeline a p s .empty := by
  sorry
