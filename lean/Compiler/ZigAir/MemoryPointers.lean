/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryEffects

/-! Geometry of successful interpreted pointer operations. These laws retain
allocation identity and derive offsets from checked arithmetic; they do not
assert source validity or refine a native pointer representation. -/
namespace Compiler.ZigAir.Memory

/-- A narrower access at the same address retains the original region and
permission, including the zero-byte check used by pointer arithmetic. -/
theorem access_narrow (state : State) (address : Address) (layout : Layout) (bytes : Nat)
    (write : Bool) (cell : Allocation) (full : access state address layout write = .ok cell)
    (bounded : bytes ≤ layout.bytes) :
    access state address ⟨bytes, layout.alignment⟩ write = .ok cell := by
  obtain ⟨found, region, shaped, positive, bound, pointerBound, extent, aligned, permitted⟩ :=
    access_success_region state address layout write cell full
  have checks : ¬(cell.base = 0 ∨ cell.base + region.bytes > addressLimit ∨
      cell.base + address.offset ≥ addressLimit ∨ address.offset + bytes > region.bytes ∨
      (cell.base + address.offset) % layout.alignment ≠ 0) := by omega
  cases write <;> simp only [access, found, shaped, Bool.false_and, Bool.false_eq_true, ↓reduceIte, if_neg checks]
  simp only [permitted rfl, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte]

/-- Derive the actual many-pointer offset and element cast from checked
accesses, without an operation-success premise. Both native map components
consume this arithmetic; neither supplies an already selected entry pointer. -/
theorem elementPointer_of_access (state : State) (writable : Bool) (child : Ty)
    (address : Address) (index : Nat) (layout : Layout) (cell : Allocation)
    (shaped : child.layout = some layout) (positive : 0 < layout.bytes)
    (start : access state address ⟨0, layout.alignment⟩ false = .ok cell)
    (finish : access state ⟨address.allocation, address.offset + index * layout.bytes⟩ layout false = .ok cell) :
    elementPointer state (.pointer (.pointer writable true child) address) index =
      .ok (.pointer (.pointer writable false child) ⟨address.allocation, address.offset + index * layout.bytes⟩) := by
  have atEnd := access_narrow state _ layout 0 false cell finish (by omega)
  obtain ⟨_, _, _, _, _, pointerBound, _, _, _⟩ := access_success_region state _ layout false cell finish
  dsimp only at pointerBound
  have rawBounds : ¬((cell.base : Int) + ↑address.offset + ↑(index * layout.bytes) < 0 ∨
      (cell.base : Int) + ↑address.offset + ↑(index * layout.bytes) ≥ ↑addressLimit) := by omega
  have lower : ¬((cell.base : Int) + ↑address.offset + ↑(index * layout.bytes) < ↑cell.base) := by omega
  have offset : ((cell.base : Int) + ↑address.offset + ↑(index * layout.bytes)).toNat - cell.base =
      address.offset + index * layout.bytes := by omega
  have nonzero : layout.bytes ≠ 0 := by omega
  simp only [elementPointer, offsetPointer, shaped, nonzero, ↓reduceIte, start,
    bind, Except.bind, Bool.false_eq_true, if_neg rawBounds, if_neg lower, offset, atEnd,
    pointerCast, pointerCompatible, decide_true, Bool.true_or,
    Bool.not_true, finish]
  cases writable <;> rfl

theorem pointerCast_address (state : State) (target : Ty) (writable many : Bool)
    (child : Ty) (address : Address) (result : Value)
    (success : pointerCast state target (.pointer (.pointer writable many child) address) = .ok result) :
    result = .pointer target address := by
  cases target with
  | pointer destWritable destMany destChild =>
    simp only [pointerCast] at success
    split at success
    · contradiction
    · cases shaped : destChild.layout with
      | none => simp [shaped] at success
      | some layout =>
        simp only [shaped] at success
        cases accessed : access state address ⟨if destMany then 0 else layout.bytes, layout.alignment⟩ false with
        | error fault => simp [accessed, bind, Except.bind] at success
        | ok cell => simpa [accessed, bind, Except.bind] using success.symm
  | _ => simp [pointerCast] at success

theorem offsetPointer_add_address (state : State) (writable : Bool) (child : Ty)
    (address : Address) (count : Nat) (result : Value)
    (success : offsetPointer state false (.pointer (.pointer writable true child) address) count = .ok result) :
    ∃ layout, child.layout = some layout ∧ 0 < layout.bytes ∧
      result = .pointer (.pointer writable true child)
        { address with offset := address.offset + count * layout.bytes } := by
  unfold offsetPointer at success
  cases shaped : child.layout with
  | none => simp [shaped] at success
  | some layout =>
    simp only [shaped] at success
    by_cases zero : layout.bytes = 0
    · simp [zero] at success
    · simp only [zero, ↓reduceIte] at success
      cases accessed : access state address ⟨0, layout.alignment⟩ false with
      | error fault => simp [accessed, bind, Except.bind] at success
      | ok cell =>
        simp only [accessed, bind, Except.bind, Bool.false_eq_true, ↓reduceIte] at success
        split at success
        · contradiction
        · split at success
          · contradiction
          · have offset : ((cell.base : Int) + address.offset + ↑(count * layout.bytes)).toNat - cell.base =
                address.offset + count * layout.bytes := by omega
            cases checked : access state { address with offset := address.offset + count * layout.bytes }
                ⟨0, layout.alignment⟩ false with
            | error fault =>
              simp only [offset, checked] at success
              cases success
            | ok next =>
              refine ⟨layout, rfl, by omega, ?_⟩
              simpa only [offset, checked, bind, Except.bind, Except.ok.injEq] using success.symm

theorem elementPointer_address (state : State) (writable : Bool) (child : Ty)
    (address : Address) (index : Nat) (result : Value)
    (success : elementPointer state (.pointer (.pointer writable true child) address) index = .ok result) :
    ∃ layout, child.layout = some layout ∧ 0 < layout.bytes ∧
      result = .pointer (.pointer writable false child)
        { address with offset := address.offset + index * layout.bytes } := by
  cases moved : offsetPointer state false (.pointer (.pointer writable true child) address) index with
  | error fault => simp [elementPointer, moved, bind, Except.bind] at success
  | ok shifted =>
    obtain ⟨layout, shaped, positive, shiftedAddress⟩ :=
      offsetPointer_add_address state writable child address index shifted moved
    have casted : pointerCast state (.pointer writable false child) shifted = .ok result := by
      simpa only [elementPointer, moved, bind, Except.bind] using success
    rw [shiftedAddress] at casted
    exact ⟨layout, shaped, positive, pointerCast_address state _ writable true child _ result casted⟩

end Compiler.ZigAir.Memory
