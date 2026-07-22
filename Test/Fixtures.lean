import ShellWall
open System

/-! # Shared test fixtures

Concrete `Owner`/`Path`/`FileState`/`Pipeline` values used by both the build-time
`checkSafe` battery (`Test/Battery.lean`) and the runtime fidelity harness. Kept in
one place so the two stay in sync. -/

namespace ShellWall.Test

/-- The agent under test. -/
def alice : Owner := .agent "alice"

/-! ## Model paths (abstract; the fidelity harness remaps these into a sandbox) -/

/-- `/home/alice/notes.txt` — privateRW, alice-owned, present with SECRET content. -/
def priv   : Path := "/home/alice/notes.txt"
/-- `/home/alice/public/out.txt` — publicRW, alice-owned. -/
def pub    : Path := "/home/alice/public/out.txt"
/-- `/home/alice/public/o2.txt` — publicRW, alice-owned, absent. -/
def pub2   : Path := "/home/alice/public/o2.txt"
/-- `/shared/ref.txt` — publicRO, present with PUBDATA content. -/
def shr    : Path := "/shared/ref.txt"
/-- `/home/bob/public/o.txt` — publicRW, bob-owned (alice cannot write). -/
def bobpub : Path := "/home/bob/public/o.txt"
/-- `/tmp/t.txt` — publicRW but system-owned (agents cannot write in v1). -/
def tmpf   : Path := "/tmp/t.txt"
/-- `/etc/passwd` — privateRO. -/
def etcf   : Path := "/etc/passwd"
/-- `/home/alice/gone.txt` — privateRW, alice-owned, ABSENT (a read of it fails). -/
def gone   : Path := "/home/alice/gone.txt"

/-- The starting filesystem: `priv`, `shr`, `pub`, `tmpf` present; everything else
absent. -/
def s0 : FileState := fun p =>
  if p = priv then some (.text "SECRET\n")
  else if p = shr then some (.text "PUBDATA\n")
  else if p = pub then some (.text "already\n")
  else if p = tmpf then some (.text "tmp\n")
  else none

/-! ## Building-block pipelines -/

/-- `cat /home/alice/notes.txt` (read a private file). -/
def rdP : Pipeline := .single (.read priv)
/-- `cat /shared/ref.txt` (read a public file). -/
def rdS : Pipeline := .single (.read shr)
/-- `cat /home/alice/gone.txt` (read an absent file → exit failure). -/
def rdG : Pipeline := .single (.read gone)
/-- `> /home/alice/public/out.txt` (overwrite a public path alice owns). -/
def wr  : Pipeline := .single (.write pub .overwrite)

end ShellWall.Test
