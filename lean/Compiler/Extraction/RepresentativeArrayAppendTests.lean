/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayAppend
import Compiler.Extraction.RepresentativeArrayWriteTests

namespace Compiler.Extraction.RepresentativeArray.Append.Tests
open Compiler.ZigAir.Memory

def header : Allocation := RepresentativeArray.Tests.header (RepresentativeArray.Tests.headerCells ⟨2, 0⟩ 1)
def before : State := RepresentativeArray.Tests.memory FieldTests.data header.cells
def ready : State := { before with heap := before.heap.replace 3 { header with cells := header.cells.set 8 (.scalar (.int false 64 2)) } }
def newCells : Cells := (FieldTests.argumentCells.set 56 FieldTests.id).set 60 FieldTests.sequence
def after : State := { ready with heap := ready.heap.replace 2 { FieldTests.data with cells := newCells } }
def execute (state : State := before) (length : Nat := 2) (id : Int := 1) (sequence : Int := 29) : Except Fault State :=
  appendWithoutGrowth state ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩ length id sequence

theorem initial_header_and_missing_slot : before.valid = true ∧
    readHeader before ⟨3, 0⟩ = .ok (.slice itemsType ⟨2, 0⟩ 1, .scalar (.int false 64 3)) ∧
    representativeFields before ⟨3, 0⟩ 1 = .ok (.error .invalidId) := by decide

theorem actual_length_store : writeLength before ⟨3, 0⟩ 2 = .ok ready ∧
    store before (.pointer (.pointer true false usize) ⟨3, 8⟩) (.scalar (.int false 64 2)) = .ok ready := by decide

theorem length_increment_precedes_initialization : ready.valid = true ∧
    readHeader ready ⟨3, 0⟩ = .ok (.slice itemsType ⟨2, 0⟩ 2, .scalar (.int false 64 3)) ∧
    representativeFields ready ⟨3, 0⟩ 1 = .error .uninitialized ∧
    sliceElementPointer ready (.slice itemsType ⟨2, 0⟩ 1) 1 = .error .sourceBounds ∧
    sliceElementPointer ready (.slice itemsType ⟨2, 0⟩ 2) 1 = .ok (.pointer (.pointer true false elementType) ⟨2, 32⟩) := by decide

theorem actual_append : execute = .ok after := by decide

theorem append_without_store_premises :
    ∃ finalState, execute = .ok finalState ∧ finalState.valid = true ∧ before.heap.RetainsShape finalState.heap ∧
      readHeader finalState ⟨3, 0⟩ = .ok (.slice itemsType ⟨2, 0⟩ 2, .scalar (.int false 64 3)) ∧
      Expression.readFields finalState false ⟨2, 32⟩ = .ok [FieldTests.item, FieldTests.arguments, FieldTests.id, FieldTests.sequence] :=
  appendWithoutGrowth_verified before 3 2 3 1 header FieldTests.data ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29
    initial_header_and_missing_slot.1 (by decide) rfl rfl (by decide) rfl rfl
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem source_bound_append :
    ∃ finalState, execute = .ok finalState ∧ representativeFields finalState ⟨3, 0⟩ 1 =
      .ok (.ok [FieldTests.item, FieldTests.arguments, FieldTests.id, FieldTests.sequence]) :=
  representativeFields_after_append before 3 2 3 header FieldTests.data 1 29 ⟨0, 0⟩ ⟨1, 4⟩ 2
    initial_header_and_missing_slot.1 (by decide) rfl rfl (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)

theorem actual_source_bound_append : representativeFields after ⟨3, 0⟩ 1 =
    .ok (.ok [FieldTests.item, FieldTests.arguments, FieldTests.id, FieldTests.sequence]) := by
  obtain ⟨finalState, executed, observed⟩ := source_bound_append
  have same : finalState = after := Except.ok.inj (executed.symm.trans actual_append)
  exact same ▸ observed

theorem no_allocation_or_payload_change : after.nextId = before.nextId ∧ after.nextAddress = before.nextAddress ∧
    after.heap.lookup 0 = before.heap.lookup 0 ∧ after.heap.lookup 1 = before.heap.lookup 1 ∧
    Expression.readFields after false ⟨2, 0⟩ = .ok [Expression.Tests.item, Expression.Tests.arguments,
      Expression.Tests.id, Expression.Tests.sequence] := by decide

theorem source_length_stays_distinct_from_capacity : representativeFields after ⟨3, 0⟩ 2 = .ok (.error .invalidId) ∧
    representativeFields after ⟨3, 0⟩ 3 = .ok (.error .invalidId) := by decide

theorem offset_unsorted_arguments_after_append :
    (do let result ← representativeFields after ⟨3, 0⟩ 1
        let .ok [_, view, _, _] := result | .error .malformed
        let first ← sliceElementPointer after view 0
        let second ← sliceElementPointer after view 1
        .ok [← load after first, ← load after second]) = .ok [.scalar (.int false 32 99), .scalar (.int false 32 1)] := by decide

def exactlyEnough : State := RepresentativeArray.Tests.memory (RepresentativeArray.Tests.backing (.array 2 Expression.allocationType) Expression.Tests.cells)
  ((.slice itemsType ⟨2, 0⟩ 1 : Value).leaves ++ (.scalar (.int false 64 2) : Value).leaves 16)

theorem exact_capacity_is_enough : exactlyEnough.valid = true ∧
    (do let finalState ← execute exactlyEnough
        readHeader finalState ⟨3, 0⟩) = .ok (.slice itemsType ⟨2, 0⟩ 2, .scalar (.int false 64 2)) := by
  have valid : exactlyEnough.valid = true := by decide
  obtain ⟨finalState, executed, _, _, observed, _⟩ :=
    appendWithoutGrowth_verified exactlyEnough 3 2 2 1
      (RepresentativeArray.Tests.header ((.slice itemsType ⟨2, 0⟩ 1 : Value).leaves ++ (.scalar (.int false 64 2) : Value).leaves 16))
      (RepresentativeArray.Tests.backing (.array 2 Expression.allocationType) Expression.Tests.cells)
      ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29 valid rfl rfl (by decide) rfl rfl (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨valid, ?_⟩
  change (do let finalState ← appendWithoutGrowth exactlyEnough ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29
             readHeader finalState ⟨3, 0⟩) = _
  simpa only [executed, bind, Except.bind, nextLength, Nat.reduceAdd] using observed

def emptyReady : State := RepresentativeArray.Tests.memory (RepresentativeArray.Tests.backing (.array 3 Expression.allocationType) [])
  ((.slice itemsType ⟨2, 0⟩ 0 : Value).leaves ++ (.scalar (.int false 64 3) : Value).leaves 16)

theorem empty_ready_array_appends_first_slot : emptyReady.valid = true ∧
    ∃ finalState, execute emptyReady 2 0 = .ok finalState ∧ representativeFields finalState ⟨3, 0⟩ 0 =
      .ok (.ok [FieldTests.item, FieldTests.arguments, .scalar (.int false 32 0), FieldTests.sequence]) := by
  refine ⟨by decide, ?_⟩
  exact representativeFields_after_append emptyReady 3 2 3
    (RepresentativeArray.Tests.header ((.slice itemsType ⟨2, 0⟩ 0 : Value).leaves ++ (.scalar (.int false 64 3) : Value).leaves 16))
    (RepresentativeArray.Tests.backing (.array 3 Expression.allocationType) []) 0 29 ⟨0, 0⟩ ⟨1, 4⟩ 2
    (by decide) (by decide) rfl rfl (by decide) rfl rfl (by decide) (by decide) (by decide) (by decide)

def exhausted : State := RepresentativeArray.Tests.memory FieldTests.data (RepresentativeArray.Tests.headerCells ⟨2, 0⟩ 3)

theorem growth_is_scope_rejection : execute exhausted = .error .unsupported ∧ execute exhausted ≠ .error .outOfMemory := by decide

def readonlyHeader : State := { before with heap := before.heap.replace 3 { header with writable := false } }
def readonlyBacking : State := { before with heap := before.heap.replace 2 { FieldTests.data with writable := false } }

theorem readonly_header_or_backing_rejects : execute readonlyHeader = .error .readOnly ∧
    execute readonlyBacking = .error .readOnly := by decide

theorem stale_backing_rejects : execute RepresentativeArray.Tests.reused = .error .unallocated := by decide

theorem malformed_evaluated_fields_reject : execute before addressLimit = .error .malformed ∧
    execute before 2 (-1) = .error .malformed ∧ execute before 2 1 (2 ^ 32) = .error .malformed := by decide

end Compiler.Extraction.RepresentativeArray.Append.Tests
