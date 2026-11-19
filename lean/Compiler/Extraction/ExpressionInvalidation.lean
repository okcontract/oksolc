/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionDeinitProgram
import Compiler.Extraction.ExpressionFields
import Compiler.ZigAir.MemoryArrayGeometry
import Compiler.ZigAir.MemoryInvalidation

namespace Compiler.Extraction.Expression
open Compiler.ZigAir.Memory

/-- Typed-memory effect of Expression.deinit's final `self.* = undefined`.
Payload/item/argument destruction must precede this operation. Selecting the
last row and connecting the complete destructor/length rollback remain caller
obligations. No logical registry entry or allocation lifetime is removed here.

Zig 0.16 specifies no observable poison-byte pattern for undefined storage:
https://ziglang.org/documentation/0.16.0/#undefined. We forget initialization
evidence and reject subsequent reads until the same fields are initialized. -/
def invalidate (state : State) (descriptor : Address) : Except Fault State :=
  Compiler.ZigAir.Memory.invalidate state true allocationType descriptor

theorem invalidation_is_last : ExpressionDeinit.expressionDeinitCode.getLast? = some .invalidate := by rfl

theorem invalidate_root (state : State) (lifetime : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = allocationType) (writable : cell.writable = true) :
    invalidate state ⟨lifetime, 0⟩ = .ok { state with heap := (state.heap.replace lifetime
      { cell with cells := cell.cells.forget 0 32 }) } := by
  exact invalidate_of_access state allocationType ⟨lifetime, 0⟩ ⟨32, 8⟩ cell layout_checked
    (root_access state lifetime cell ⟨32, 8⟩ true initial found (typed ▸ layout_checked) (by decide) (by intro _; exact writable))
    (typed ▸ acceptsView_self allocationType)

/-- Invalidate one complete row at its actual byte offset. The same backing
allocation survives, including every earlier/later row and spare-capacity cell.
The success and validity are derived from initial geometry, not final reads. -/
theorem invalidate_array (state : State) (lifetime capacity index : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity allocationType) (writable : cell.writable = true)
    (inside : index < capacity) :
    ∃ after, invalidate state ⟨lifetime, index * 32⟩ = .ok after ∧ after.valid = true ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      after.heap.lookup lifetime = some { cell with cells := cell.cells.forget (index * 32) 32 } ∧
      (∀ other, other ≠ lifetime → after.heap.lookup other = state.heap.lookup other) := by
  have accessed := array_access state lifetime capacity index 32 allocationType ⟨32, 8⟩ cell
    initial found typed writable layout_checked (by decide) (by decide) inside (by decide) true
  have view : acceptsView cell.type (index * 32) allocationType = true := by
    simp [typed, acceptsView, layout_checked, inside]
    split <;> rfl
  have executed := invalidate_of_access state allocationType ⟨lifetime, index * 32⟩ ⟨32, 8⟩ cell layout_checked accessed view
  exact ⟨_, executed, invalidate_valid _ _ _ _ _ initial executed, rfl, rfl,
    Heap.lookup_replace _ _ _ _ found, (invalidate_frame _ _ _ _ _ executed).2.2⟩

end Compiler.Extraction.Expression
