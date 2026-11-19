/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayFields
import Compiler.Extraction.RepresentativeArrayTests

namespace Compiler.Extraction.RepresentativeArray.FieldTests
open Compiler.ZigAir.Memory

/-- Only the older descriptor is initialized. The following states are exact
expected observations of each checked store, not a supplied final snapshot. -/
def data : Allocation := Tests.backing (.array 3 Expression.allocationType) Expression.Tests.cells
def before : State := Tests.memory data
def item : Value := Expression.Tests.item
def arguments : Value := Expression.Tests.arguments
def id : Value := .scalar (.int false 32 1)
def sequence : Value := .scalar (.int false 32 29)
def fieldAddress (offset : Nat) (type : Ty) : Value := .pointer (.pointer true false type) ⟨2, 32 + offset⟩
def stateWith (cells : Cells) : State := { before with heap := before.heap.replace 2 { data with cells } }
def itemCells : Cells := data.cells.set 32 item
def withItem : State := stateWith itemCells
def argumentPointer : Value := .pointer (.pointer true true Expression.idType) ⟨1, 4⟩
def withArgumentPointer : State := stateWith (itemCells.set 40 argumentPointer)
def argumentCells : Cells := (itemCells.set 40 argumentPointer).set 48 (.scalar (.int false 64 2))
def withArguments : State := stateWith argumentCells
def withId : State := stateWith (argumentCells.set 56 id)
def after : State := stateWith ((argumentCells.set 56 id).set 60 sequence)

theorem initial_valid : before.valid = true := by decide

theorem source_element_selector :
    fieldPointer before (.pointer (.pointer false false Expression.allocationType) ⟨2, 32⟩) Expression.argumentsOffset =
      .ok (.pointer (.pointer false false Expression.argumentsType) ⟨2, 40⟩) :=
  element_fieldPointer before 2 3 1 data Expression.argumentsOffset Expression.argumentsType false
    initial_valid (by decide) rfl rfl (by decide) Expression.field_types_checked.2.1

theorem four_actual_stores : store before (fieldAddress Expression.itemOffset Expression.itemType) item = .ok withItem ∧
    store withItem (fieldAddress Expression.argumentsOffset Expression.argumentsType) arguments = .ok withArguments ∧
    store withArguments (fieldAddress Expression.idOffset Expression.idType) id = .ok withId ∧
    store withId (fieldAddress Expression.sequence_numberOffset Expression.idType) sequence = .ok after := by decide

/-- Instantiate the composed theorem from actual initial backing and stores.
The final representative pointer, validity, header read and fields are derived. -/
theorem source_bound_complete_observation : representativeFields after ⟨3, 0⟩ 1 = .ok (.ok [item, arguments, id, sequence]) :=
  representativeFields_after_stores before withItem withArguments withId after ⟨3, 0⟩ 2 3 2 data 1
    ⟨0, 0⟩ ⟨1, 4⟩ 2 29 initial_valid (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide)
    four_actual_stores.1 four_actual_stores.2.1 four_actual_stores.2.2.1 four_actual_stores.2.2.2

theorem nonzero_element_is_not_first : representativeFields after ⟨3, 0⟩ 0 =
    .ok (.ok [Expression.Tests.item, Expression.Tests.arguments, Expression.Tests.id, Expression.Tests.sequence]) ∧
    representativeFields after ⟨3, 0⟩ 1 ≠ representativeFields after ⟨3, 0⟩ 0 := by decide

theorem initialized_selector_does_not_initialize_payload :
    fieldPointer before (.pointer (.pointer false false Expression.allocationType) ⟨2, 32⟩) Expression.itemOffset =
      .ok (.pointer (.pointer false false Expression.itemType) ⟨2, 32⟩) ∧
    representativeFields before ⟨3, 0⟩ 1 = .error .uninitialized := by decide

theorem reached_prefix_is_not_complete : representativeFields withItem ⟨3, 0⟩ 1 = .error .uninitialized ∧
    representativeFields withArguments ⟨3, 0⟩ 1 = .error .uninitialized ∧
    representativeFields withId ⟨3, 0⟩ 1 = .error .uninitialized := by decide

theorem partial_slice_rejects : representativeFields withArgumentPointer ⟨3, 0⟩ 1 = .error .uninitialized := by decide

theorem older_descriptor_and_allocations_survive :
    Expression.readFields after false ⟨2, 0⟩ = .ok [Expression.Tests.item, Expression.Tests.arguments,
      Expression.Tests.id, Expression.Tests.sequence] ∧
    after.heap.lookup 0 = before.heap.lookup 0 ∧ after.heap.lookup 1 = before.heap.lookup 1 := by decide

theorem offset_unsorted_borrow_keeps_identity :
    (do let result ← representativeFields after ⟨3, 0⟩ 1
        let .ok [_, view, _, _] := result | .error .malformed
        let first ← sliceElementPointer after view 0
        let second ← sliceElementPointer after view 1
        .ok [← load after first, ← load after second]) =
      .ok [.scalar (.int false 32 99), .scalar (.int false 32 1)] := by decide

theorem readonly_element_rejects_write :
    (do let result ← representative after ⟨3, 0⟩ 1
        let .ok pointer := result | .error .malformed
        let field ← fieldPointer after pointer Expression.idOffset
        store after field id) = .error .readOnly := by decide

theorem source_bound_precedes_field_reads : representativeFields after ⟨3, 0⟩ 2 = .ok (.error .invalidId) ∧
    representativeFields after ⟨3, 0⟩ 4294967295 = .ok (.error .invalidId) := by decide

theorem array_extent_rejects_field_selector : fieldPointer before
    (.pointer (.pointer false false Expression.allocationType) ⟨2, 96⟩) Expression.itemOffset = .error .memoryValidity := by decide

theorem stale_lifetime_rejects_complete_fields : representativeFields Tests.reused ⟨3, 0⟩ 1 = .error .unallocated := by decide

end Compiler.Extraction.RepresentativeArray.FieldTests
