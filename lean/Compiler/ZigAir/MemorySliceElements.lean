/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordArrayWrites
import Compiler.ZigAir.MemoryAirLaws

namespace Compiler.ZigAir.Memory

theorem sliceElementPointer_in_bounds (state : State) (writable : Bool) (child : Ty)
    (address : Address) (length index : Nat) (width : length < addressLimit) (inside : index < length) :
    sliceElementPointer state (.slice (.slice writable child) address length) index =
      elementPointer state (.pointer (.pointer writable true child) address) index := by
  simp [sliceElementPointer, Nat.not_le.mpr width, inside]

/-- A larger allocation never widens the slice's original bound. -/
theorem sliceElementPointer_out_of_bounds (state : State) (writable : Bool) (child : Ty)
    (address : Address) (length index : Nat) (width : length < addressLimit) (outside : length ≤ index) :
    sliceElementPointer state (.slice (.slice writable child) address length) index = .error .sourceBounds := by
  simp [sliceElementPointer, Nat.not_le.mpr width, Nat.not_lt.mpr outside]

theorem sliceElementPointer_address (state : State) (writable : Bool) (child : Ty)
    (address : Address) (length index : Nat) (result : Value)
    (success : sliceElementPointer state (.slice (.slice writable child) address length) index = .ok result) :
    length < addressLimit ∧ index < length ∧ ∃ layout, child.layout = some layout ∧ 0 < layout.bytes ∧
      result = .pointer (.pointer writable false child) { address with offset := address.offset + index * layout.bytes } := by
  by_cases width : length < addressLimit
  · by_cases inside : index < length
    · rw [sliceElementPointer_in_bounds state writable child address length index width inside] at success
      exact ⟨width, inside, elementPointer_address state writable child address index result success⟩
    · rw [sliceElementPointer_out_of_bounds state writable child address length index width (by omega)] at success
      contradiction
  · simp [sliceElementPointer, show length ≥ addressLimit by omega] at success

namespace WordArray

def View.slice (view : View) : Value := .slice (.slice true word) (view.address 0) view.length

theorem slice_element (state : State) (view : View) (index : Nat)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length) :
    sliceElementPointer state view.slice index = .ok (view.pointer index) := by
  rw [View.slice, sliceElementPointer_in_bounds state true word (view.address 0) view.length index
    (view_width state view initial cap) inside]
  exact element_pointer state view index initial cap inside

/-- The complete positive-length slice fits its live allocation. No successful
slice constructor or element access is assumed. -/
theorem make_slice (state : State) (view : View) (initial : state.valid = true) (cap : Writable state view)
    (positiveLength : 0 < view.length) : makeSlice state (.slice true word) view.buffer view.length = .ok view.slice := by
  have width := view_width state view initial cap
  obtain ⟨extent, cell, found, typed, _, bound⟩ := cap
  obtain ⟨_, positive, layout, shaped, aligned, bounded, limit⟩ := valid_lookup state view.allocation cell initial found
  rw [typed, array_layout] at shaped
  cases Option.some.inj shaped
  dsimp only at aligned bounded
  have alignment : (cell.base + view.first * 4) % 4 = 0 := by omega
  have checks : ¬(cell.base = 0 ∨ cell.base + extent * 4 > addressLimit ∨
      cell.base + view.first * 4 ≥ addressLimit ∨
      view.first * 4 + view.length * 4 > extent * 4 ∨ (cell.base + view.first * 4) % 4 ≠ 0) := by omega
  simp only [makeSlice, View.buffer, View.slice, View.address, Nat.add_zero, word, Ty.layout, Ty.leafLayout,
    Nat.reduceEqDiff, Bool.not_true, Bool.and_false, Bool.false_eq_true, ne_self_iff_false, or_false, Bool.false_and, ↓reduceIte,
    if_neg (Nat.not_le.mpr width), access, found, typed, array_layout, if_neg checks, bind, Except.bind]

theorem writable_allocate (state after : State) (view : View) (child : Ty) (pointer : Value)
    (initial : state.valid = true) (cap : Writable state view)
    (allocated : allocate state child = .ok (pointer, after)) : Writable after view := by
  obtain ⟨extent, cell, found, typed, writable, bound⟩ := cap
  have older := (valid_lookup state view.allocation cell initial found).1
  obtain ⟨layout, base, _, _, rfl⟩ := allocate_shape state child pointer after allocated
  exact ⟨extent, cell, by simp [Heap.lookup_cons, show state.nextId ≠ view.allocation by omega, found],
    typed, writable, bound⟩

theorem offset_zero (state : State) (view : View) (initial : state.valid = true)
    (cap : Writable state view) (positive : 0 < view.length) :
    offsetPointer state false view.buffer 0 = .ok view.buffer := by
  have element := element_pointer state view 0 initial cap positive
  cases moved : offsetPointer state false view.buffer 0 with
  | error fault =>
    simp only [elementPointer, moved, bind, Except.bind] at element
    simp [View.buffer] at element
  | ok shifted =>
    obtain ⟨layout, _, _, position⟩ := offsetPointer_add_address state true word (view.address 0) 0 shifted moved
    simpa only [Nat.zero_mul, Nat.add_zero, View.buffer] using congrArg Except.ok position

end WordArray
end Compiler.ZigAir.Memory
