/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryByteAccess
import Compiler.ZigAir.MemoryWordBytes
import Compiler.ZigAir.MemorySliceElements

namespace Compiler.ZigAir.Memory.ByteAccess
open WordArray

def atByte (address : Address) (offset : Fin 4) : Address :=
  { address with offset := address.offset + offset.val }

theorem number_valid (value : BitVec 8) : (number value).valid = true := by
  have bound := value.isLt
  simp [number, Value.valid, Scalar.Value.valid, Scalar.Ty.contains, Scalar.Ty.lower, Scalar.Ty.upper]
  omega

theorem number_typed (value : BitVec 8) : (number value).hasType byte = true := by
  simp [Value.hasType, number, Value.type, Scalar.Value.type, byte]
  exact number_valid value

theorem wordAddress_atByte (address : Address) (offset : Fin 4) (aligned : address.offset % 4 = 0) :
    wordAddress (atByte address offset) = address := by
  have bound := offset.isLt
  have same : (address.offset + offset.val) / 4 * 4 = address.offset := by omega
  cases address
  simp_all [wordAddress, atByte]

theorem atByte_lane (address : Address) (offset : Fin 4) (aligned : address.offset % 4 = 0) :
    (atByte address offset).offset % 4 = offset.val := by
  have bound := offset.isLt
  simp only [atByte]
  omega

theorem read_atByte (order : WordBytes.Order) (state : State) (address : Address) (offset : Fin 4)
    (writable many : Bool) (aligned : address.offset % 4 = 0) :
    read order state (pointer writable many (atByte address offset)) =
      (do let value ← WordByteView.read order state (.pointer (.pointer writable false word) address) offset.val
          .ok (number value)) := by
  simp only [read, pointer, byte, wordPointer, wordAddress_atByte address offset aligned,
    atByte_lane address offset aligned]

theorem write_atByte (order : WordBytes.Order) (state : State) (address : Address) (offset : Fin 4)
    (writable many : Bool) (value : BitVec 8) (aligned : address.offset % 4 = 0) :
    write order state (pointer writable many (atByte address offset)) (number value) =
      WordByteView.write order state (.pointer (.pointer writable false word) address) offset.val value := by
  have valid := number_valid value
  simp only [number] at valid
  simp only [write, pointer, byte, number, valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    wordPointer, wordAddress_atByte address offset aligned, atByte_lane address offset aligned]
  have encoded : BitVec.ofInt 8 (value.toNat : Int) = value := by simp
  rw [encoded]

/-- Checked cast preserves allocation identity, exact byte address, constness,
physical alignment and the existence of the original typed word subobject. -/
theorem cast_address (state : State) (writable many sourceWritable sourceMany : Bool) (alignment : Nat)
    (address : Address) (result : Value)
    (success : cast state writable many alignment (.pointer (.pointer sourceWritable sourceMany word) address) = .ok result) :
    (writable = true → sourceWritable = true) ∧ (alignment = 1 ∨ alignment = 2 ∨ alignment = 4) ∧
      ∃ cell, access state address ⟨4, 4⟩ false = .ok cell ∧ acceptsView cell.type address.offset word = true ∧
        (cell.base + address.offset) % alignment = 0 ∧ result = pointer writable many address := by
  simp only [cast, word] at success
  split at success
  · contradiction
  next permissions =>
    split at success
    · contradiction
    next supported =>
      cases accessed : access state address ⟨4, 4⟩ false with
      | error reason => simp [accessed, bind, Except.bind] at success
      | ok cell =>
        simp only [accessed, bind, Except.bind] at success
        split at success
        · contradiction
        next typed =>
          split at success
          · contradiction
          next aligned =>
            refine ⟨?_, by omega, cell, rfl, ?_, by omega, (Except.ok.inj success).symm⟩
            · cases writable <;> cases sourceWritable <;> simp_all
            · simpa using typed

/-- Valid array ownership discharges the cast's geometry without requiring
initialized contents or a successful cast as an input premise. -/
theorem cast_array (state : State) (view : View) (index alignment : Nat) (writable many : Bool)
    (initial : state.valid = true) (cap : Writable state view) (inside : index < view.length)
    (supported : alignment = 1 ∨ alignment = 2 ∨ alignment = 4) :
    cast state writable many alignment (view.pointer index) = .ok (pointer writable many (view.address index)) := by
  obtain ⟨extent, cell, _, typed, _, bound, accessed⟩ := element_access state view index 4 initial cap inside (by omega) false
  have aligned := (access_success_region state (view.address index) ⟨4, 4⟩ false cell accessed).2
  obtain ⟨_, _, _, _, _, _, aligned, _⟩ := aligned
  dsimp only at aligned
  have alignedTo : (cell.base + (view.address index).offset) % alignment = 0 := by
    rcases supported with rfl | rfl | rfl
    · exact Nat.mod_one _
    · omega
    · exact aligned
  have fits : acceptsView cell.type (view.address index).offset word = true := by
    rw [typed]
    exact array_view extent (view.first + index) (by omega)
  have admissible : ¬(alignment ≠ 1 ∧ alignment ≠ 2 ∧ alignment ≠ 4) := by omega
  simp only [cast, View.pointer, word, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    if_neg admissible, accessed, bind, Except.bind, fits, alignedTo, ne_self_iff_false]

theorem read_refines (order : WordBytes.Order) (state : State) (view : View) (items : List (BitVec 32))
    (index : Nat) (offset : Fin 4) (represented : Represents state view items) (inside : index < items.length) :
    read order state (pointer true false (atByte (view.address index) offset)) =
      .ok (number (WordBytes.read order items[index] offset)) := by
  rw [read_atByte order state (view.address index) offset true false (by simp [View.address])]
  have readback := WordByteView.read_word order state (view.pointer index) offset items[index] (represented.2 index inside)
  change WordByteView.read order state (.pointer (.pointer true false word) (view.address index)) offset.val = _ at readback
  rw [readback]
  rfl

/-- The byte address resolves to the existing initialized word, with the exact
list update and caller frame already proved for typed byte views. -/
theorem write_refines (order : WordBytes.Order) (state : State) (view : View) (items : List (BitVec 32))
    (index : Nat) (offset : Fin 4) (value : BitVec 8)
    (initial : state.valid = true) (cap : Writable state view) (represented : Represents state view items)
    (inside : index < items.length) :
    ∃ after, write order state (pointer true false (atByte (view.address index) offset)) (number value) = .ok after ∧
      after.valid = true ∧ Writable after view ∧
      Represents after view (items.set index (WordBytes.write order items[index] offset value)) ∧ Frame view state after := by
  rw [write_atByte order state (view.address index) offset true false value (by simp [View.address])]
  exact WordByteView.write_refines order state view items index offset value initial cap represented inside

end Compiler.ZigAir.Memory.ByteAccess
