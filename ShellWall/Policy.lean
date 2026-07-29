import ShellWall.Basic

/-- The confidentiality/writability class the policy assigns to a path. Two axes:
public vs. private (may its content flow to a public sink?) and RW vs. RO (may it
be written?). `cmdOutIsPublic` seeds public PROVENANCE from reads of `public*` paths;
the `write_*` safety rules gate writes on the `*RW` classes. -/
inductive PathClass where
  /-- Public and writable: readable as public data, and a valid public write sink. -/
  | publicRW
  /-- Public and read-only: a frozen, world-readable source; never a write target. -/
  | publicRO
  /-- Private and writable: writable by its owner; never a public sink. -/
  | privateRW
  /-- Private and read-only: e.g. system config; readable, never written. -/
  | privateRO
  deriving DecidableEq

-- Externally configured policy table. In a real deployment this would be loaded
-- from config; v1 fixes a small, legible, illustrative table so that `checkSafe`
-- is computable and testable. Total and deterministic.
--
-- DENY-BY-DEFAULT: the final catch-all is a deliberate policy stance, not a
-- throwaway. The safest classification for an *unknown* path is the most
-- restrictive one that still lets its owner use it -- `privateRW`: writable by
-- its owner, never a public sink. Defaulting unknown paths to any `public` class
-- would let unmodeled paths act as leak sinks, because `cmdOutIsPublic` seeds public
-- provenance from exactly the paths classified public.
--
-- SUBTREE MATCHING: each rule matches a path PREFIX with a `List`-cons tail
-- (`_`) absorbing arbitrary remaining depth, so a rule governs its whole subtree
-- at any depth. Totality is structural and needs no termination argument: each
-- pattern inspects a bounded number of leading segments, the trailing `_` absorbs
-- any remainder, and the final catch-all makes the match exhaustive. There is no
-- recursion here.
--
-- PRECEDENCE IS A CORRECTNESS REQUIREMENT, NOT STYLE: `home/<a>/public/...` is
-- tested BEFORE the general `home/<a>/...` rule, because every public path also
-- matches the general rule. Ordered matching therefore implements longest-match.
-- Reversing these two would classify public subtrees as `privateRW` -- the safe
-- direction, but wrong, and it would make `write_public_ok` unreachable for
-- agents, silently killing the public-output flow.
--
-- `publicRO` (/shared) = public AND read-only: a published, frozen,
-- world-readable artifact. No `SafeCmd` write rule accepts `publicRO`
-- (`write_public_ok` needs `publicRW`, `write_private_ok` needs `privateRW`), so
-- /shared is unwritable by everyone -- including `system`. It is exactly the kind
-- of source `cmdOutIsPublic` certifies public-provenance from, so making it reachable
-- means the noninterference proof must discharge a real public-read case rather than
-- a vacuous one.
/-- A path's segment list for policy matching (approach (A)). `FilePath.components`
yields a leading `""` for absolute paths (`/home/a` → `["", "home", "a"]`);
filtering empty segments normalizes absolute, relative, and trailing-slash forms
to the bare segment list the subtree patterns expect. -/
def segments (p : Path) : List String := p.components.filter (· ≠ "")

/-- Classify a path per the policy table (see the design notes above for the
deny-by-default, longest-match, and `publicRO` rationale). Total and deterministic;
subtree matching via ordered patterns over `segments p`. -/
def classify (p : Path) : PathClass :=
  match segments p with
  | "home" :: _ :: "public" :: _ => .publicRW   -- agent's public output subtree, any depth
  | "home" :: _ :: _             => .privateRW  -- rest of an agent's home, any depth
  | "shared" :: _                => .publicRO   -- world-readable frozen reference tree
  | "tmp" :: _                   => .publicRW   -- scratch space
  | "etc" :: _                   => .privateRO  -- system config: readable, never written
  -- DELIBERATELY REDUNDANT: `/private` gets the same class (`privateRW`) as the
  -- default catch-all, so this arm changes no behavior. Kept as an explicit entry
  -- documenting that `/private` is intentionally private data, not an unclassified
  -- path that merely happens to land on the default.
  | "private" :: _               => .privateRW
  | _                            => .privateRW  -- DEFAULT: deny-by-default (see above)

/-- Who owns a path, i.e. who has write-authority over it via `CanWrite`. Either a
named agent or the system. -/
inductive Owner where
  /-- An agent, identified by `id` (e.g. the owner of `/home/<id>/...`). -/
  | agent  (id : String)
  /-- The system — owns everything not under an agent's home. -/
  | system
  deriving DecidableEq

-- DENY-BY-DEFAULT: `CanWrite` (Safety.lean) currently has only the `self`
-- constructor, which requires `ownerOf p = a`. Defaulting unknown paths to
-- `.system` therefore means no *agent* can write them without an explicit
-- ownership entry: an agent cannot write a path it does not provably own. This
-- is the correct deny-by-default direction.
--
-- Intended interaction with `classify`: a default-unknown path is `privateRW`
-- AND `.system`-owned, so an agent gets neither a public-write path nor
-- ownership of it -- it simply cannot write there at all.
--
-- SUBTREE MATCHING: as in `classify`, and total for the same structural reason.
-- One rule now covers an agent's ENTIRE home subtree, public or not: the separate
-- `public` entry that exact-shape matching needed is subsumed, because
-- `"home" :: a :: _` already matches every depth under `home/<a>`. Ownership is
-- therefore uniform across an agent's home, while `classify` is what varies
-- between its public and private parts.
/-- The owner of a path (see the design notes above). Total and deterministic;
one rule covers an agent's entire home subtree, everything else is `system`. -/
def ownerOf (p : Path) : Owner :=
  match segments p with
  | "home" :: agentId :: _ => .agent agentId  -- an agent owns its whole home subtree
  | "shared" :: _          => .system         -- frozen reference tree, owned by system
  -- CHOICE: /tmp is `.system`-owned. Combined with `classify`'s `.publicRW`, this
  -- means NO agent can write /tmp in v1 (CanWrite has only `self`, and delegation
  -- is deferred to v2). That is the safe direction, but /tmp is labelled "scratch
  -- space" yet is agent-unwritable until v2 delegation lands.
  | "tmp" :: _             => .system
  | "etc" :: _             => .system
  | _                      => .system         -- DEFAULT: unowned-by-agents => system
