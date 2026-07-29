/-- A filesystem path. Lean's standard path type: a structure wrapping a `String`,
with real path operations (`components`, `join`, `/`, `parent`, ...).
`DecidableEq` comes from the underlying `String` and is available without a manual
instance. Policy subtree-matching decomposes to `components` inside
`classify`/`ownerOf`; everywhere else `Path` flows opaquely. -/
abbrev Path := System.FilePath

/-- The content of a file or a pipe stage's stdin/stdout: UTF-8 text, raw bytes,
or nothing. Note the three distinct "no bytes" representations (`.text ""`,
`.binary ByteArray.empty`, `.empty`); the semantics canonicalise empty results to
`.empty`. -/
inductive Content where
  /-- Text content, held as a `String`. -/
  | text   (s : String)
  /-- Binary content, held as a raw `ByteArray`. -/
  | binary (b : ByteArray)
  /-- No content — the canonical empty value. -/
  | empty

/-- How a `write` deposits its stdin at the target path. -/
inductive WriteMode where
  /-- Replace the target's content outright (`> p`). -/
  | overwrite
  /-- Append to the target's existing content (`>> p`). -/
  | append
  deriving DecidableEq

/-- A command/pipeline exit status. `failure` carries the nonzero code, mirroring
POSIX exit codes; drives `&&`/`||` short-circuiting in the semantics. -/
inductive ExitCode where
  /-- Exit 0. -/
  | success
  /-- Nonzero exit, carrying the code. -/
  | failure (code : Nat)
  deriving DecidableEq

/-- Two `ByteArray`s with equal underlying `data` arrays are equal. Bridges the
gap that `ByteArray` exposes no `DecidableEq` in core; the `Content` equality
decision below relies on it. -/
theorem byteArray_eq_of_data_eq {b₁ b₂ : ByteArray} (h : b₁.data = b₂.data) : b₁ = b₂ := by
  cases b₁; cases b₂; simp only [ByteArray.mk.injEq]; exact h

/-- Decidable equality on `Content`, deciding the `binary` case through the
underlying `Array UInt8` (`ByteArray` has no core `DecidableEq`, so `Content`
cannot simply `deriving DecidableEq`).

NOTE: this instance is NOT load-bearing for execution — the stream operations in
`Semantics.lean` compare *lines* (`String`s), never whole `Content` values. It is
provided for completeness and for later proof/testing use. -/
instance : DecidableEq Content
  | .text s₁, .text s₂ =>
      if h : s₁ = s₂ then isTrue (by rw [h])
      else isFalse (by intro hc; injection hc with h'; exact h h')
  | .binary b₁, .binary b₂ =>
      if h : b₁.data = b₂.data then isTrue (by rw [byteArray_eq_of_data_eq h])
      else isFalse (by intro hc; injection hc with h'; exact h (by rw [h']))
  | .empty, .empty => isTrue rfl
  | .text _,   .binary _ => isFalse (fun h => Content.noConfusion h)
  | .text _,   .empty    => isFalse (fun h => Content.noConfusion h)
  | .binary _, .text _   => isFalse (fun h => Content.noConfusion h)
  | .binary _, .empty    => isFalse (fun h => Content.noConfusion h)
  | .empty,    .text _   => isFalse (fun h => Content.noConfusion h)
  | .empty,    .binary _ => isFalse (fun h => Content.noConfusion h)
