-- Placeholder removed; see design doc for motivation.

abbrev Path := List String   -- canonical segments, no symlinks, e.g. ["home","user","f.txt"]

inductive Content where
  | text   (s : String)
  | binary (b : ByteArray)
  | empty

inductive WriteMode where
  | overwrite
  | append
  deriving DecidableEq

inductive ExitCode where
  | success
  | failure (code : Nat)
  deriving DecidableEq

-- `ByteArray` has no `DecidableEq` in core, which is why `Content` cannot simply
-- `deriving DecidableEq`. `ByteArray` is a one-field structure wrapping
-- `Array UInt8`, and `Array UInt8` does have decidable equality, so equality on
-- the `binary` case is decided through the underlying `data` array.
theorem byteArray_eq_of_data_eq {b₁ b₂ : ByteArray} (h : b₁.data = b₂.data) : b₁ = b₂ := by
  cases b₁; cases b₂; simp only [ByteArray.mk.injEq]; exact h

-- NOTE: this instance is NOT load-bearing for execution. The stream operations in
-- `Semantics.lean` compare *lines* (i.e. `String`s), never whole `Content` values.
-- It is provided for completeness and for later proof/testing use.
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
