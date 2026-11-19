/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryByteAccessProofs

namespace Compiler.ZigAir.Memory.ByteAccess
open WordArray

def slice (writable : Bool) (address : Address) : Value := .slice (.slice writable byte) address 4

/-- Every admitted byte access stays within the checked four-byte subobject,
including the zero-width pointer-arithmetic checks that precede a load/store. -/
theorem access_bytes (state : State) (address : Address) (cell : Allocation) (offset bytes : Nat)
    (full : access state address ⟨4, 4⟩ false = .ok cell) (inside : offset < 4) (fits : offset + bytes ≤ 4) :
    access state { address with offset := address.offset + offset } ⟨bytes, 1⟩ false = .ok cell := by
  obtain ⟨found, region, shaped, positive, regionBound, _, extent, _, _⟩ := access_success_region state address _ false cell full
  dsimp only at extent
  have checked : ¬(cell.base = 0 ∨ cell.base + region.bytes > addressLimit ∨
      cell.base + (address.offset + offset) ≥ addressLimit ∨
      address.offset + offset + bytes > region.bytes ∨ (cell.base + (address.offset + offset)) % 1 ≠ 0) := by omega
  simp only [access, found, shaped, Bool.false_and, Bool.false_eq_true, ↓reduceIte, if_neg checked]

theorem make_byte_slice (state : State) (view : View) (index : Nat) (writable : Bool)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length) :
    makeSlice state (.slice writable byte) (pointer writable true (view.address index)) 4 =
      .ok (slice writable (view.address index)) := by
  obtain ⟨_, cell, _, _, _, _, full⟩ := element_access state view index 4 initial cap inside (by omega) false
  have checked := access_bytes state (view.address index) cell 0 4 full (by decide) (by decide)
  simp only [Nat.add_zero] at checked
  have width : ¬(4 ≥ addressLimit) := by decide
  cases writable <;>
    simp only [makeSlice, pointer, slice, byte, ne_self_iff_false, Bool.not_true, Bool.not_false,
      Bool.and_false, Bool.false_and, Bool.false_eq_true, or_self, ↓reduceIte, if_neg width,
      Ty.layout, Ty.leafLayout, Nat.reduceEqDiff, Nat.mul_one, checked, bind, Except.bind]

/-- The ordinary AIR slice-element operation can address each byte of the
cast word. Its original four-byte bound and allocation checks both remain. -/
theorem byte_element (state : State) (view : View) (index : Nat) (offset : Fin 4) (writable : Bool)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length) :
    sliceElementPointer state (slice writable (view.address index)) offset.val =
      .ok (pointer writable false (atByte (view.address index) offset)) := by
  obtain ⟨_, cell, _, _, _, _, full⟩ := element_access state view index 4 initial cap inside (by omega) false
  have start := access_bytes state (view.address index) cell 0 0 full (by decide) (by decide)
  simp only [Nat.add_zero] at start
  have atEnd := access_bytes state (view.address index) cell offset.val 0 full offset.isLt (by have := offset.isLt; omega)
  have atElement := access_bytes state (view.address index) cell offset.val 1 full offset.isLt (by have := offset.isLt; omega)
  obtain ⟨_, region, _, _, regionBound, _, extent, _, _⟩ := access_success_region state (view.address index) _ false cell full
  dsimp only at extent
  have bound := offset.isLt
  have rawBounds : ¬((cell.base : Int) + ↑(view.address index).offset + (offset.val : Int) < 0 ∨
      (cell.base : Int) + ↑(view.address index).offset + (offset.val : Int) ≥ ↑addressLimit) := by omega
  have lower : ¬((cell.base : Int) + ↑(view.address index).offset + (offset.val : Int) < ↑cell.base) := by omega
  have position : ((cell.base : Int) + ↑(view.address index).offset + (offset.val : Int)).toNat - cell.base =
      (view.address index).offset + offset.val := by omega
  rw [slice, sliceElementPointer_in_bounds state writable byte (view.address index) 4 offset.val (by decide) offset.isLt]
  simp only [elementPointer, offsetPointer, byte, Ty.layout, Ty.leafLayout, Nat.reduceEqDiff, ↓reduceIte, start,
    bind, Except.bind, Bool.false_eq_true, Nat.mul_one, if_neg rawBounds, if_neg lower,
    position, atEnd, pointerCast, pointerCompatible, decide_true, Bool.true_or,
    Bool.not_true, atElement, pointer, atByte]
  cases writable <;> rfl

/-- The actual primitive sequence used by a word-to-byte slice preserves the
source word address and its four-byte bound, without successful-operation
premises. Alignment remains a checked operand of the first operation. -/
theorem cast_slice_element (state : State) (view : View) (index alignment : Nat) (offset : Fin 4) (writable : Bool)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length)
    (supported : alignment = 1 ∨ alignment = 2 ∨ alignment = 4) :
    (do let raw ← cast state writable true alignment (view.pointer index)
        let bytes ← makeSlice state (.slice writable byte) raw 4
        sliceElementPointer state bytes offset.val) =
      .ok (pointer writable false (atByte (view.address index) offset)) := by
  rw [cast_array state view index alignment writable true initial cap inside supported]
  simp only [bind, Except.bind]
  rw [make_byte_slice state view index writable initial cap inside]
  exact byte_element state view index offset writable initial cap inside

theorem read_alias (order : WordBytes.Order) (state : State) (address : Address)
    (writable₁ many₁ writable₂ many₂ : Bool) :
    read order state (pointer writable₁ many₁ address) = read order state (pointer writable₂ many₂ address) := rfl

end Compiler.ZigAir.Memory.ByteAccess
