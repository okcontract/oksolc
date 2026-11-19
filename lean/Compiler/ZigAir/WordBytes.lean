/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypes

/-! Defined byte representation of initialized u32 storage. This codec has no
padding, pointer provenance or partially initialized bytes. Target byte order
is explicit, and is not inferred from the host running Lean. -/
namespace Compiler.ZigAir.WordBytes

inductive Order where
  | little | big
  deriving DecidableEq, Repr

def lane (order : Order) (index : Fin 4) : Nat :=
  match order with | .little => index.val | .big => 3 - index.val

def read (order : Order) (value : BitVec 32) (index : Fin 4) : BitVec 8 :=
  BitVec.ofNat 8 (value.toNat / 256 ^ lane order index)

def write (order : Order) (value : BitVec 32) (index : Fin 4) (byte : BitVec 8) : BitVec 32 :=
  let position := lane order index
  BitVec.ofNat 32 (value.toNat % 256 ^ position + 256 ^ position * byte.toNat +
    256 ^ (position + 1) * (value.toNat / 256 ^ (position + 1)))

private theorem lanes (index : Fin 4) : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by
  have := index.isLt
  have : index.val = 0 ∨ index.val = 1 ∨ index.val = 2 ∨ index.val = 3 := by omega
  rcases this with h | h | h | h <;> simp only [Fin.ext_iff] <;> omega

private theorem top_val : (3 : Fin 4).val = 3 := rfl

theorem read_write_same (order : Order) (value : BitVec 32) (index : Fin 4) (byte : BitVec 8) :
    read order (write order value index byte) index = byte := by
  apply BitVec.eq_of_toNat_eq
  have := value.isLt
  have := byte.isLt
  rcases lanes index with rfl | rfl | rfl | rfl <;> cases order <;>
    simp [read, write, lane, top_val, BitVec.toNat_ofNat] <;> omega

theorem read_write_other (order : Order) (value : BitVec 32) (index other : Fin 4) (byte : BitVec 8)
    (apart : other ≠ index) :
    read order (write order value index byte) other = read order value other := by
  apply BitVec.eq_of_toNat_eq
  have := value.isLt
  have := byte.isLt
  rcases lanes index with rfl | rfl | rfl | rfl <;>
    rcases lanes other with rfl | rfl | rfl | rfl <;> cases order <;>
    simp [read, write, lane, top_val, BitVec.toNat_ofNat] at * <;> omega

theorem write_read (order : Order) (value : BitVec 32) (index : Fin 4) :
    write order value index (read order value index) = value := by
  apply BitVec.eq_of_toNat_eq
  have := value.isLt
  rcases lanes index with rfl | rfl | rfl | rfl <;> cases order <;>
    simp [read, write, lane, top_val, BitVec.toNat_ofNat] <;> omega

/-- The four byte observations determine the complete word. -/
theorem ext (order : Order) (a b : BitVec 32)
    (same : ∀ index, read order a index = read order b index) : a = b := by
  have h0 := congrArg BitVec.toNat (same 0)
  have h1 := congrArg BitVec.toNat (same 1)
  have h2 := congrArg BitVec.toNat (same 2)
  have h3 := congrArg BitVec.toNat (same 3)
  apply BitVec.eq_of_toNat_eq
  have := a.isLt
  have := b.isLt
  cases order <;> simp [read, lane, top_val, BitVec.toNat_ofNat] at h0 h1 h2 h3 <;> omega

end Compiler.ZigAir.WordBytes
