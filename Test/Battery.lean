import Test.Fixtures
open System

/-! # Build-time `checkSafe` validation battery

The 26-case battery (20 core + 6 conditional) as `#guard` assertions checked at
ELABORATION time: any future change that moves a verdict fails `lake build`. Each
guard is annotated with its bash-equivalent and the expected verdict + reason.

(Plain `--` comments, not `/-- -/` docstrings: `#guard` is a command, not a
declaration, so a doc comment has nothing to attach to.) -/

namespace ShellWall.Test

-- Case 1: `cat /home/alice/notes.txt` → permit (reading is never the violation).
#guard checkSafe alice rdP s0 == true

-- Case 2: `cat notes | > notes` (write own private file) → permit (write_private_ok).
#guard checkSafe alice (.pipe rdP (.single (.write priv .overwrite))) s0 == true

-- Case 3: `cat notes | > public/out` → reject (private content to a public path).
#guard checkSafe alice (.pipe rdP (.single (.write pub .overwrite))) s0 == false

-- Case 4: `cat /shared/ref | > public/out` → permit (public content to public path).
#guard checkSafe alice (.pipe rdS (.single (.write pub .overwrite))) s0 == true

-- Case 5a: write to `/shared/ref` (publicRO) → reject (read-only class).
#guard checkSafe alice (.pipe rdS (.single (.write shr .overwrite))) s0 == false

-- Case 5b: write to `/etc/passwd` (privateRO) → reject (read-only class).
#guard checkSafe alice (.pipe rdS (.single (.write etcf .overwrite))) s0 == false

-- Case 6a: write to `/home/bob/public/o` (unowned) → reject (CanWrite fails).
#guard checkSafe alice (.pipe rdS (.single (.write bobpub .overwrite))) s0 == false

-- Case 6b: write to `/tmp/t` (publicRW but system-owned) → reject (CanWrite fails).
#guard checkSafe alice (.pipe rdS (.single (.write tmpf .overwrite))) s0 == false

-- Case 7a: `rm /home/alice/notes.txt` (owned) → permit.
#guard checkSafe alice (.single (.rm priv)) s0 == true

-- Case 7b: `rm /etc/passwd` (unowned) → reject (CanWrite fails).
#guard checkSafe alice (.single (.rm etcf)) s0 == false

-- Case 8: `(cat shared | > notes) ; (cat notes | > public/out)` → reject
-- (second stage writes private-sourced content to a public path).
#guard checkSafe alice
  (.seq (.pipe rdS (.single (.write priv .overwrite)))
        (.pipe rdP (.single (.write pub .overwrite)))) s0 == false

-- Case 8b: `(cat shared | > notes) ; (cat shared | > public/out)` → permit
-- (control: both public-sourced).
#guard checkSafe alice
  (.seq (.pipe rdS (.single (.write priv .overwrite)))
        (.pipe rdS (.single (.write pub .overwrite)))) s0 == true

-- Case 9a: `cat shared | grep -F PUB | > public/out` → permit (grep of public is public).
#guard checkSafe alice
  (.pipe (.pipe rdS (.single (.grep "PUB"))) (.single (.write pub .overwrite))) s0 == true

-- Case 9b: `cat shared | sort | > public/out` → permit (sort of public is public).
#guard checkSafe alice
  (.pipe (.pipe rdS (.single .sort)) (.single (.write pub .overwrite))) s0 == true

-- Case 9c: `cat shared | uniq | > public/out` → permit (of_uniq: uniq of public is public).
#guard checkSafe alice
  (.pipe (.pipe rdS (.single .uniq)) (.single (.write pub .overwrite))) s0 == true

-- Case 9d: `cat shared | wc | > public/out` → reject (aggregation is never public).
#guard checkSafe alice
  (.pipe (.pipe rdS (.single .wc)) (.single (.write pub .overwrite))) s0 == false

-- Case 10a: `cat shared | >> public/out` (append, existing public) → permit.
#guard checkSafe alice (.pipe rdS (.single (.write pub .append))) s0 == true

-- Case 10b: `cat notes | >> public/out` (append, private source) → reject.
#guard checkSafe alice (.pipe rdP (.single (.write pub .append))) s0 == false

-- Case 10c: `cat shared | >> public/o2` (append, absent target) → permit.
#guard checkSafe alice (.pipe rdS (.single (.write pub2 .append))) s0 == true

-- Case X: `cat /shared/nope | > public/out` (read absent public path) → reject
-- (missing read yields non-public `.empty`).
#guard checkSafe alice
  (.pipe (.single (.read "/shared/nope")) (.single (.write pub .overwrite))) s0 == false

/-! ## Conditional C-cases (Prompt 09): `(cond) | write`, exercising the
exit-aware output flag. -/

-- C1: `(cat gone && cat shared) | > public/out` → reject. Stage 1 FAILS, so the
-- conditional's output is stage 1's (non-public `.empty`) — sound reject. This is
-- the case the pre-fix (buggy) decider wrongly ACCEPTED.
#guard checkSafe alice (.pipe (.andThen rdG rdS) wr) s0 == false

-- C2: `(cat shared && cat shared) | > public/out` → permit (stage 1 succeeds →
-- stage 2 runs → public output).
#guard checkSafe alice (.pipe (.andThen rdS rdS) wr) s0 == true

-- C3: `(cat shared && cat notes) | > public/out` → reject (stage 2 runs → private).
#guard checkSafe alice (.pipe (.andThen rdS rdP) wr) s0 == false

-- C4: `(cat gone || cat shared) | > public/out` → permit (stage 1 fails → stage 2
-- runs → public).
#guard checkSafe alice (.pipe (.orElse rdG rdS) wr) s0 == true

-- C5: `(cat shared || cat notes) | > public/out` → permit (stage 1 succeeds →
-- output is stage 1's, public).
#guard checkSafe alice (.pipe (.orElse rdS rdP) wr) s0 == true

-- C6: `(cat notes || cat shared) | > public/out` → reject (stage 1 succeeds →
-- output is stage 1's, private).
#guard checkSafe alice (.pipe (.orElse rdP rdS) wr) s0 == false

end ShellWall.Test
