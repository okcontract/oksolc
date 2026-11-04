/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArray
import Compiler.Extraction.ExpressionFieldTests

namespace Compiler.Extraction.RepresentativeArray.Tests
open Compiler.ZigAir.Memory
open Compiler.Algebraic

def descriptorCells : Cells := Expression.Tests.cells ++
  Expression.Tests.cells.map (fun (offset, value) => (offset + 32, value))
def backing (type : Ty := .array 3 Expression.allocationType) (cells : Cells := descriptorCells)
    (stack : Bool := false) : Allocation := ⟨512, type, cells, true, stack⟩
def items (data : Address := ⟨2, 0⟩) (length : Nat := 2) : Value := .slice itemsType data length
def capacity : Value := .scalar (.int false 64 3)
def headerCells (data : Address := ⟨2, 0⟩) (length : Nat := 2) : Cells :=
  (items data length).leaves itemsOffset ++ capacity.leaves capacityOffset
def header (cells : Cells := headerCells) : Allocation := ⟨608, allocationType, cells, true, false⟩
def memory (data : Allocation := backing) (cells : Cells := headerCells) : State :=
  ⟨[(3, header cells), (2, data), (1, Expression.Tests.argumentsAllocation),
    (0, Expression.Tests.itemAllocation)], 4, 632⟩
def resultPointer (index : Nat) : Value := .pointer (.pointer false false Expression.allocationType) ⟨2, index * 32⟩

theorem complete_valid : memory.valid = true := by decide

theorem header_reads_both_fields : readHeader memory ⟨3, 0⟩ = .ok (items, capacity) := by decide

theorem first_and_second_representatives : representative memory ⟨3, 0⟩ 0 = .ok (.ok (resultPointer 0)) ∧
    representative memory ⟨3, 0⟩ 1 = .ok (.ok (resultPointer 1)) := by decide

/-- The source-bound total pointer theorem is instantiated with the same live
allocation. No successful pointer/cast result is supplied as a premise. -/
theorem source_pointer_derivation : representative memory ⟨3, 0⟩ 1 = .ok (.ok (resultPointer 1)) :=
  representative_from_array memory ⟨3, 0⟩ 2 3 2 backing 1 complete_valid (by decide) (by decide)
    rfl rfl (by decide) (by decide)

theorem capacity_does_not_widen_length : representative memory ⟨3, 0⟩ 2 = .ok (.error .invalidId) ∧
    representative memory ⟨3, 0⟩ 3 = .ok (.error .invalidId) ∧
    representative memory ⟨3, 0⟩ 4294967295 = .ok (.error .invalidId) := by decide

theorem pointer_loads_complete_expression :
    (do let result ← representative memory ⟨3, 0⟩ 1
        match result with
        | .error _ => .error .malformed
        | .ok (.pointer _ address) => Expression.readFields memory false address
        | .ok _ => .error .malformed) =
      .ok [Expression.Tests.item, Expression.Tests.arguments, Expression.Tests.id, Expression.Tests.sequence] := by decide

theorem independent_unsorted_offset_borrow :
    (do let result ← representative memory ⟨3, 0⟩ 1
        let .ok (.pointer _ address) := result | .error .malformed
        let arguments ← Expression.readField memory false address Expression.argumentsOffset
        let first ← sliceElementPointer memory arguments 0
        let second ← sliceElementPointer memory arguments 1
        .ok [← load memory first, ← load memory second]) =
      .ok [.scalar (.int false 32 99), .scalar (.int false 32 1)] := by decide

theorem readonly_return_cannot_store :
    (do let result ← representative memory ⟨3, 0⟩ 1
        let .ok pointer := result | .error .malformed
        let field ← fieldPointer memory pointer Expression.idOffset
        store memory field (.scalar (.int false 32 9))) = .error .readOnly := by decide

def dangling : State := memory backing (headerCells ⟨97, 0⟩ 0)

theorem empty_sentinel_is_not_dereferenced : dangling.valid = true ∧
    representative dangling ⟨3, 0⟩ 0 = .ok (.error .invalidId) := by decide

theorem invalid_id_does_not_dereference : representative (memory backing (headerCells ⟨97, 0⟩ 2)) ⟨3, 0⟩ 2 =
    .ok (.error .invalidId) := by decide

theorem valid_id_needs_live_backing : representative (memory backing (headerCells ⟨97, 0⟩ 2)) ⟨3, 0⟩ 1 =
    .error .unallocated := by decide

theorem missing_header_pointer_rejects : representative (memory backing (capacity.leaves capacityOffset)) ⟨3, 0⟩ 0 =
    .error .uninitialized := by decide

theorem missing_header_length_rejects : representative
    (memory backing [(0, .pointer (.pointer true true elementType) ⟨2, 0⟩), (16, capacity)]) ⟨3, 0⟩ 0 =
    .error .uninitialized := by decide

theorem capacity_is_not_read_by_lookup : representative (memory backing (items.leaves itemsOffset)) ⟨3, 0⟩ 1 =
    .ok (.ok (resultPointer 1)) ∧ readHeader (memory backing (items.leaves itemsOffset)) ⟨3, 0⟩ =
    .error .uninitialized := by decide

theorem invalid_header_leaf_rejects : representative (memory backing [(0, .scalar (.int false 64 0))]) ⟨3, 0⟩ 0 =
    .error .malformed := by decide

theorem header_interior_and_extent_reject : representative memory ⟨3, 8⟩ 0 = .error .memoryValidity := by decide

theorem misaligned_data_rejects : representative (memory backing (headerCells ⟨2, 4⟩ 2)) ⟨3, 0⟩ 0 =
    .error .memoryValidity := by decide

theorem backing_extent_is_checked : representative (memory backing (headerCells ⟨2, 0⟩ 4)) ⟨3, 0⟩ 3 =
    .error .memoryValidity := by decide

theorem nominal_extent_is_not_complete_shape : representative
    (memory (backing (.array 3 elementType) [])) ⟨3, 0⟩ 1 = .error .unsupported := by decide

theorem foreign_same_extent_rejects : representative
    (memory (backing (.array 24 Expression.idType) [])) ⟨3, 0⟩ 1 = .error .unsupported := by decide

theorem omitted_expression_field_rejects : representative
    (memory (backing (.array 3 (.aggregate "src/libevmasm/expression_classes.zig::Expression" ⟨32, 8⟩
      [(0, .pointer true "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨224, 16⟩),
       (8, .slice true (.int false 32)), (24, .scalar (.int false 32))])) [])) ⟨3, 0⟩ 1 =
    .error .unsupported := by decide

theorem wrong_nominal_identity_rejects : recordView memory Expression.allocationType
    (.pointer (.pointer true false (.record "foreign" ⟨32, 8⟩)) ⟨2, 32⟩) = .error .unsupported := by decide

theorem wrong_nominal_layout_rejects : recordView memory Expression.allocationType
    (.pointer (.pointer true false (.record "src/libevmasm/expression_classes.zig::Expression" ⟨32, 4⟩)) ⟨2, 32⟩) =
    .error .unsupported := by decide

theorem record_view_preserves_constness : recordView memory Expression.allocationType
    (.pointer (.pointer false true elementType) ⟨2, 32⟩) =
    .ok (.pointer (.pointer false true Expression.allocationType) ⟨2, 32⟩) := by decide

theorem live_pointer_is_not_initialized_record : representative (memory (backing (.array 3 Expression.allocationType) []))
    ⟨3, 0⟩ 1 = .ok (.ok (resultPointer 1)) ∧
    Expression.readFields (memory (backing (.array 3 Expression.allocationType) [])) false ⟨2, 32⟩ =
    .error .uninitialized := by decide

theorem stale_backing_lifetime_rejects : representative
    (cleanup 2 (memory (backing (.array 3 Expression.allocationType) descriptorCells true))) ⟨3, 0⟩ 1 =
    .error .unallocated := by decide

def reused : State := { memory with
  heap := (4, backing) :: (memory.heap.filter (fun entry => entry.1 != 2)), nextId := 5 }

theorem same_address_new_lifetime_is_not_old_pointer : reused.valid = true ∧
    representative reused ⟨3, 0⟩ 1 = .error .unallocated := by decide

theorem source_header_store_derivation (state withItems after : State) (lifetime : Nat) (cell : Allocation)
    (data : Address) (length : Nat) (capacity : Int) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = allocationType)
    (storedItems : store state (.pointer (.pointer true false itemsType) ⟨lifetime, itemsOffset⟩)
      (.slice itemsType data length) = .ok withItems)
    (storedCapacity : store withItems (.pointer (.pointer true false usize) ⟨lifetime, capacityOffset⟩)
      (.scalar (.int false 64 capacity)) = .ok after) :
    readHeader after ⟨lifetime, 0⟩ = .ok (.slice itemsType data length, .scalar (.int false 64 capacity)) :=
  header_after_stores state withItems after lifetime cell data length capacity initial found typed storedItems storedCapacity

end Compiler.Extraction.RepresentativeArray.Tests
