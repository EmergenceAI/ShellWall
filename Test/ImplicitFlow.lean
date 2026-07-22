import ShellWall
open System

/-! # Implicit-flow leak — now CLOSED (regression witness)

Prompt 13 mechanically refuted `shellwall_noninterference` with this pipeline: an
`andThen` whose guard's exit code depends on private content, gating a public
write — an implicit flow leaking one bit per conditional through the exit-code
channel.

Prompt 14 CLOSED it by strengthening the spec (`SafePipeline.andThen`/`orElse` now
carry `hguard : touchesOnlyPublic p₁ = true`) and enforcing the same conjunct in
`checkFull`. A guard that touches only public paths has a public-determined exit
code, so two states agreeing on all public paths run (or skip) the body
identically — the channel is gone.

This file is now a permanent REGRESSION WITNESS that the leak stays rejected. The
Prompt-13 refutation theorem is intentionally gone: it obtained its two
`SafePipeline` derivations from `checkSafe_sound` fed by `checkSafe … = true`, and
`checkSafe` now returns `false` for this pipeline, so those derivations no longer
exist and the term no longer typechecks. That is the desired outcome.

(The `#guard`s below evaluate via the interpreter, so unlike the Prompt-13
theorems this file carries no `native_decide`/`ofReduceBool` axioms at all.) -/

namespace ShellWall.ImplicitFlow

def alice  : Owner := .agent "alice"
def secret : Path := "/private/secret"             -- privateRW
def shref  : Path := "/shared/ref"                 -- publicRO
def outp   : Path := "/home/alice/public/out.txt"  -- publicRW, alice

/-- Guard: `cat /private/secret | grep -F match` — its exit depends on private
content, and it READS a private path. -/
def leftB  : Pipeline := .pipe (.single (.read secret)) (.single (.grep "match"))
/-- Body: `cat /shared/ref > /home/alice/public/out.txt` — a public write. -/
def rightB : Pipeline := .pipe (.single (.read shref)) (.single (.write outp .overwrite))
/-- The Prompt-13 leaking pipeline `left && right`. -/
def thePipeline : Pipeline := .andThen leftB rightB
/-- Same branches under `;` — no branching, so no implicit-flow channel. -/
def seqControl : Pipeline := .seq leftB rightB

def s1 : FileState := fun p =>
  if p = secret then some (.text "match\n") else if p = shref then some (.text "PUB\n") else none
def s2 : FileState := fun p =>
  if p = secret then some (.text "xxx\n")   else if p = shref then some (.text "PUB\n") else none

-- The guard touches a private path, so it is not public-only:
#guard touchesOnlyPublic leftB == false

-- ⇒ the leaking `&&` pipeline is now REJECTED by the gate in BOTH states
-- (pre-Prompt-14 it was permitted, which is exactly what made the leak possible):
#guard checkSafe alice thePipeline s1 == false
#guard checkSafe alice thePipeline s2 == false

-- The fix is targeted: `seq` (and `pipe`) have no exit-code branch, so reading the
-- private guard there is harmless and still PERMITTED — the body runs regardless,
-- so no private bit reaches public state. Only `andThen`/`orElse` are constrained.
#guard checkSafe alice seqControl s1 == true

end ShellWall.ImplicitFlow
