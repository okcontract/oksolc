/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAllocationLaws

namespace Compiler.ZigAir.Memory

/-- Derive each element's checked access from a valid declared array. Positive
stride and its alignment multiple are separate captured-layout obligations. -/
theorem array_access_permitted (state : State) (id extent index bytes : Nat) (child : Ty)
    (layout : Layout) (cell : Allocation) (initial : state.valid = true)
    (found : state.heap.lookup id = some cell) (typed : cell.type = .array extent child)
    (shaped : child.layout = some layout)
    (positive : 0 < layout.bytes) (stride : layout.bytes % layout.alignment = 0)
    (inside : index < extent) (width : bytes ≤ layout.bytes) (write : Bool)
    (permitted : write = true → cell.writable = true) :
    access state ⟨id, index * layout.bytes⟩ ⟨bytes, layout.alignment⟩ write = .ok cell := by
  obtain ⟨_, basePositive, actual, actualShape, aligned, bounded, limit⟩ :=
    valid_lookup state id cell initial found
  have arrayShape : cell.type.layout = some ⟨extent * layout.bytes, layout.alignment⟩ := by
    simp only [typed, Ty.layout, shaped, bind, Option.bind]
  have same : actual = ⟨extent * layout.bytes, layout.alignment⟩ :=
    Option.some.inj (actualShape.symm.trans arrayShape)
  subst actual
  dsimp only at aligned bounded
  have elementEnd : index * layout.bytes + layout.bytes ≤ extent * layout.bytes := by
    calc
      index * layout.bytes + layout.bytes = (index + 1) * layout.bytes := by
        rw [Nat.add_mul, Nat.one_mul]
      _ ≤ extent * layout.bytes := Nat.mul_le_mul_right layout.bytes (by omega)
  have offsetInside : index * layout.bytes < extent * layout.bytes := by omega
  have offsetAligned : (cell.base + index * layout.bytes) % layout.alignment = 0 := by
    simp only [Nat.add_mod, Nat.mul_mod, aligned, stride, Nat.mul_zero, Nat.zero_mod, Nat.add_zero]
  have checks : ¬(cell.base = 0 ∨ cell.base + extent * layout.bytes > addressLimit ∨
      cell.base + index * layout.bytes ≥ addressLimit ∨ index * layout.bytes + bytes > extent * layout.bytes ∨
      (cell.base + index * layout.bytes) % layout.alignment ≠ 0) := by omega
  cases write <;>
    simp only [access, found, arrayShape, Bool.false_and, Bool.false_eq_true, ↓reduceIte, if_neg checks]
  simp only [permitted rfl, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte]

/-- The writable-array facade retains its existing interface. Readonly callers
use the permission law above without assuming that their storage is writable. -/
theorem array_access (state : State) (id extent index bytes : Nat) (child : Ty)
    (layout : Layout) (cell : Allocation) (initial : state.valid = true)
    (found : state.heap.lookup id = some cell) (typed : cell.type = .array extent child)
    (writable : cell.writable = true) (shaped : child.layout = some layout)
    (positive : 0 < layout.bytes) (stride : layout.bytes % layout.alignment = 0)
    (inside : index < extent) (width : bytes ≤ layout.bytes) (write : Bool) :
    access state ⟨id, index * layout.bytes⟩ ⟨bytes, layout.alignment⟩ write = .ok cell :=
  array_access_permitted state id extent index bytes child layout cell initial found typed shaped positive stride inside width write
    (by intro _; exact writable)

end Compiler.ZigAir.Memory
