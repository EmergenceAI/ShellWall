import ShellWall.Basic

inductive PathClass where
  | publicRW
  | publicRO
  | privateRW
  | privateRO
  deriving DecidableEq

-- Externally configured policy table. In a real deployment this would be loaded
-- from config; v1 fixes a small, legible, illustrative table so that `checkSafe`
-- (Phase 5) is computable and testable. Total and deterministic.
--
-- DENY-BY-DEFAULT: the final catch-all is a deliberate policy stance, not a
-- throwaway. The safest classification for an *unknown* path is the most
-- restrictive one that still lets its owner use it -- `privateRW`: writable by
-- its owner, never a public sink. Defaulting unknown paths to any `public` class
-- would let unmodeled paths act as leak sinks, because `IsPublic.of_public_read`
-- seeds public content from exactly the paths classified public.
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
-- of source `IsPublic.of_public_read` is meant to certify content from, so making
-- it reachable means the Phase 8 noninterference proof must discharge a real
-- public-read case rather than a vacuous one.
-- Approach (A): decompose the `FilePath` to its segment list and keep the
-- Prompt 05 ordered subtree patterns verbatim.
-- `FilePath.components` yields a leading "" for absolute paths
-- (`/home/a` -> ["", "home", "a"]); filtering empty segments normalizes absolute,
-- relative, and trailing-slash forms to the bare segment list the patterns expect,
-- reproducing the prior `List String` behavior exactly (representation change only).
def segments (p : Path) : List String := p.components.filter (· ≠ "")

def classify (p : Path) : PathClass :=
  match segments p with
  | "home" :: _ :: "public" :: _ => .publicRW   -- agent's public output subtree, any depth
  | "home" :: _ :: _             => .privateRW  -- rest of an agent's home, any depth
  | "shared" :: _                => .publicRO   -- world-readable frozen reference tree
  | "tmp" :: _                   => .publicRW   -- scratch space
  | "etc" :: _                   => .privateRO  -- system config: readable, never written
  | "private" :: _               => .privateRW  -- owned private data (same as default;
                                                --   kept as explicit intent, not a no-op rule)
  | _                            => .privateRW  -- DEFAULT: deny-by-default (see above)

inductive Owner where
  | agent  (id : String)
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
