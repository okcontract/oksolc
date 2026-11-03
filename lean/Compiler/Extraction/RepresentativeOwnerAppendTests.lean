/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeOwnerAppend
import Compiler.Extraction.RepresentativeGrowthTests

namespace Compiler.Extraction.RepresentativeArray.Owner.AppendTests
open Compiler.ZigAir.Memory

def oldCells : Cells := [(24, .scalar (.int false 64 1)), (32, .scalar (.int false 64 3)),
  (16, .pointer (.pointer true true elementType) ⟨2, 0⟩)]
def ownerCell (runtimeSafety writable stack : Bool) : Allocation := FieldTests.cell runtimeSafety writable stack oldCells
def before (runtimeSafety writable stack : Bool) : State :=
  ⟨[(3, ownerCell runtimeSafety writable stack), (2, RepresentativeArray.FieldTests.data),
    (1, Expression.Tests.argumentsAllocation), (0, Expression.Tests.itemAllocation)], 4, 608 + (layout runtimeSafety).bytes⟩
def ready (runtimeSafety stack : Bool) : State :=
  ⟨[(3, {ownerCell runtimeSafety true stack with cells := oldCells.set 24 (.scalar (.int false 64 2))}),
    (2, RepresentativeArray.FieldTests.data), (1, Expression.Tests.argumentsAllocation),
    (0, Expression.Tests.itemAllocation)], 4, 608 + (layout runtimeSafety).bytes⟩
def after (runtimeSafety stack : Bool) : State :=
  ⟨[(3, {ownerCell runtimeSafety true stack with cells := oldCells.set 24 (.scalar (.int false 64 2))}),
    (2, {RepresentativeArray.FieldTests.data with cells := Append.Tests.newCells}), (1, Expression.Tests.argumentsAllocation),
    (0, Expression.Tests.itemAllocation)], 4, 608 + (layout runtimeSafety).bytes⟩
def execute (runtimeSafety : Bool) (state : State) (owner : Address := ⟨3, 0⟩)
    (argumentsLength : Nat := 2) (id : Int := 1) : Except Fault State :=
  appendWithoutGrowth runtimeSafety state owner ⟨0, 0⟩ ⟨1, 4⟩ argumentsLength id 29

private theorem at_header (runtimeSafety : Bool) (state : State) (cell : Allocation) (argumentsLength : Nat) (id : Int)
    (initial : state.valid = true) (found : state.heap.lookup 3 = some cell) (typed : cell.type = viewType runtimeSafety) :
    execute runtimeSafety state ⟨3, 0⟩ argumentsLength id =
      Append.appendWithoutGrowth state ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ argumentsLength id 29 := by
  have selected : fieldPointer state (.pointer (.pointer true false (viewType runtimeSafety)) ⟨3, 0⟩) representativesOffset =
      .ok (.pointer (.pointer true false RepresentativeArray.allocationType) ⟨3, 16⟩) :=
    root_header_pointer runtimeSafety state 3 cell true initial found typed
  simp only [execute, appendWithoutGrowth, selected, bind, Except.bind]

theorem initial_owner_and_spare (runtimeSafety stack : Bool) : (before runtimeSafety true stack).valid = true ∧
    readHeader (before runtimeSafety true stack) ⟨3, 16⟩ =
      .ok (.slice itemsType ⟨2, 0⟩ 1, .scalar (.int false 64 3)) ∧
    representativeFields (before runtimeSafety true stack) ⟨3, 16⟩ 1 = .ok (.error .invalidId) := by
  cases runtimeSafety <;> cases stack <;> decide

theorem actual_length_store (runtimeSafety stack : Bool) :
    Append.writeLength (before runtimeSafety true stack) ⟨3, 16⟩ 2 = .ok (ready runtimeSafety stack) ∧
      store (before runtimeSafety true stack) (.pointer (.pointer true false usize) ⟨3, 24⟩)
        (.scalar (.int false 64 2)) = .ok (ready runtimeSafety stack) := by
  cases runtimeSafety <;> cases stack <;> constructor <;> rfl

theorem length_precedes_descriptor (runtimeSafety stack : Bool) :
    readHeader (ready runtimeSafety stack) ⟨3, 16⟩ =
      .ok (.slice itemsType ⟨2, 0⟩ 2, .scalar (.int false 64 3)) ∧
    representativeFields (ready runtimeSafety stack) ⟨3, 16⟩ 1 = .error .uninitialized := by
  cases runtimeSafety <;> cases stack <;> decide

theorem actual_append (runtimeSafety stack : Bool) :
    execute runtimeSafety (before runtimeSafety true stack) = .ok (after runtimeSafety stack) := by
  rw [at_header runtimeSafety (before runtimeSafety true stack) (ownerCell runtimeSafety true stack) 2 1
    (initial_owner_and_spare runtimeSafety stack).1 rfl rfl]
  cases runtimeSafety <;> cases stack <;> rfl

theorem append_without_final_premises (runtimeSafety stack : Bool) :
    ∃ finalState, execute runtimeSafety (before runtimeSafety true stack) = .ok finalState ∧
      finalState.valid = true ∧ (before runtimeSafety true stack).heap.RetainsShape finalState.heap ∧
      readHeader finalState ⟨3, 16⟩ = .ok (.slice itemsType ⟨2, 0⟩ 2, .scalar (.int false 64 3)) ∧
      Expression.readFields finalState false ⟨2, 32⟩ = .ok [RepresentativeArray.FieldTests.item,
        RepresentativeArray.FieldTests.arguments, RepresentativeArray.FieldTests.id, RepresentativeArray.FieldTests.sequence] ∧
      finalState.nextId = (before runtimeSafety true stack).nextId ∧
      finalState.nextAddress = (before runtimeSafety true stack).nextAddress ∧
      (∀ other, other ≠ 3 → other ≠ 2 → finalState.heap.lookup other = (before runtimeSafety true stack).heap.lookup other) := by
  obtain ⟨finalState, ran, valid, shape, header, fields, nextId, nextAddress, frame, _⟩ :=
    appendWithoutGrowth_framed runtimeSafety (before runtimeSafety true stack) 3 2 3 1
    (ownerCell runtimeSafety true stack) RepresentativeArray.FieldTests.data ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29
    (initial_owner_and_spare runtimeSafety stack).1 rfl rfl rfl rfl rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨finalState, ran, valid, shape, header, fields, nextId, nextAddress, frame⟩

theorem derived_readback (runtimeSafety stack : Bool) :
    (after runtimeSafety stack).valid = true ∧
      readHeader (after runtimeSafety stack) ⟨3, 16⟩ = .ok (.slice itemsType ⟨2, 0⟩ 2, .scalar (.int false 64 3)) ∧
      Expression.readFields (after runtimeSafety stack) false ⟨2, 32⟩ = .ok [RepresentativeArray.FieldTests.item,
        RepresentativeArray.FieldTests.arguments, RepresentativeArray.FieldTests.id, RepresentativeArray.FieldTests.sequence] := by
  obtain ⟨finalState, executed, valid, _, loaded, fields, _⟩ := append_without_final_premises runtimeSafety stack
  have same := Except.ok.inj (executed.symm.trans (actual_append runtimeSafety stack))
  exact same ▸ ⟨valid, loaded, fields⟩

theorem source_bound_and_older_descriptor (runtimeSafety stack : Bool) :
    representativeFields (after runtimeSafety stack) ⟨3, 16⟩ 1 = .ok (.ok [RepresentativeArray.FieldTests.item,
      RepresentativeArray.FieldTests.arguments, RepresentativeArray.FieldTests.id, RepresentativeArray.FieldTests.sequence]) ∧
    representativeFields (after runtimeSafety stack) ⟨3, 16⟩ 0 = representativeFields (before runtimeSafety true stack) ⟨3, 16⟩ 0 ∧
    representativeFields (after runtimeSafety stack) ⟨3, 16⟩ 2 = .ok (.error .invalidId) := by
  cases runtimeSafety <;> cases stack <;> decide

def source : WordArray.View := ⟨1, 1, 2⟩
theorem parent_contents (runtimeSafety stack : Bool) : WordArray.Represents (before runtimeSafety true stack) source [99, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have choices : index = 0 ∨ index = 1 := by change index < 2 at inside; omega
  rcases choices with rfl | rfl <;> cases runtimeSafety <;> cases stack <;> rfl

theorem parent_survives_same_append (runtimeSafety stack : Bool) :
    (after runtimeSafety stack).heap.lookup 1 = some Expression.Tests.argumentsAllocation ∧
      WordArray.Represents (after runtimeSafety stack) source [99, 1] := by
  obtain ⟨finalState, executed, _, found, represented, _⟩ := append_parent_borrow runtimeSafety
    (before runtimeSafety true stack) 3 2 3 1 (ownerCell runtimeSafety true stack) RepresentativeArray.FieldTests.data
    ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29 source [99, 1] 4 Expression.Tests.argumentsAllocation
    (initial_owner_and_spare runtimeSafety stack).1 rfl rfl rfl rfl rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl)
    (by decide) (by decide) (by decide) (by decide) rfl rfl (parent_contents runtimeSafety stack)
  have same := Except.ok.inj (executed.symm.trans (actual_append runtimeSafety stack))
  exact same ▸ ⟨found, represented⟩

theorem owner_metadata_and_lifetimes (runtimeSafety stack : Bool) :
    (after runtimeSafety stack).heap.lookup 3 = some
      {ownerCell runtimeSafety true stack with cells := oldCells.set 24 (.scalar (.int false 64 2))} ∧
      (after runtimeSafety stack).nextId = (before runtimeSafety true stack).nextId ∧
      (after runtimeSafety stack).nextAddress = (before runtimeSafety true stack).nextAddress := by
  cases runtimeSafety <;> cases stack <;> constructor <;> try constructor <;> rfl

theorem readonly_owner_rejects (runtimeSafety stack : Bool) :
    execute runtimeSafety (before runtimeSafety false stack) = .error .readOnly := by
  rw [at_header runtimeSafety (before runtimeSafety false stack) (ownerCell runtimeSafety false stack) 2 1
    (by cases runtimeSafety <;> cases stack <;> decide) rfl rfl]
  cases runtimeSafety <;> cases stack <;> rfl

theorem readonly_backing_rejects (runtimeSafety stack : Bool) :
    execute runtimeSafety {before runtimeSafety true stack with
      heap := (before runtimeSafety true stack).heap.replace 2 {RepresentativeArray.FieldTests.data with writable := false}} = .error .readOnly := by
  rw [at_header runtimeSafety _ (ownerCell runtimeSafety true stack) 2 1
    (by cases runtimeSafety <;> cases stack <;> decide) rfl rfl]
  cases runtimeSafety <;> cases stack <;> rfl

theorem owner_lifetime_and_location_checked (runtimeSafety stack : Bool) :
    execute runtimeSafety (before runtimeSafety true stack) ⟨99, 0⟩ = .error .unallocated ∧
      execute runtimeSafety (before runtimeSafety true stack) ⟨3, 8⟩ = .error .memoryValidity ∧
      execute runtimeSafety (before runtimeSafety true stack) ⟨3, 16⟩ = .error .memoryValidity := by
  cases runtimeSafety <;> cases stack <;> decide

theorem standalone_header_is_not_owner (runtimeSafety : Bool) :
    execute runtimeSafety Append.Tests.before = .error .memoryValidity := by cases runtimeSafety <;> decide

theorem stale_backing_rejects (runtimeSafety stack : Bool) :
    execute runtimeSafety {before runtimeSafety true stack with heap := (before runtimeSafety true stack).heap.filter (fun entry => entry.1 != 2)} =
      .error .unallocated := by
  rw [at_header runtimeSafety _ (ownerCell runtimeSafety true stack) 2 1
    (by cases runtimeSafety <;> cases stack <;> decide) rfl rfl]
  cases runtimeSafety <;> cases stack <;> rfl

theorem missing_header_leaf_rejects (runtimeSafety stack : Bool) :
    execute runtimeSafety {before runtimeSafety true stack with
      heap := (before runtimeSafety true stack).heap.replace 3
        (FieldTests.cell runtimeSafety true stack [(16, .pointer (.pointer true true elementType) ⟨2, 0⟩), (32, .scalar (.int false 64 3))])} =
      .error .uninitialized := by
  rw [at_header runtimeSafety _ (FieldTests.cell runtimeSafety true stack
    [(16, .pointer (.pointer true true elementType) ⟨2, 0⟩), (32, .scalar (.int false 64 3))]) 2 1
    (by cases runtimeSafety <;> cases stack <;> decide) rfl rfl]
  cases runtimeSafety <;> cases stack <;> rfl

theorem invalid_evaluated_fields_reject (runtimeSafety stack : Bool) :
    execute runtimeSafety (before runtimeSafety true stack) ⟨3, 0⟩ addressLimit = .error .malformed ∧
      execute runtimeSafety (before runtimeSafety true stack) ⟨3, 0⟩ 2 (-1) = .error .malformed := by
  rw [at_header runtimeSafety _ (ownerCell runtimeSafety true stack) addressLimit 1
      (initial_owner_and_spare runtimeSafety stack).1 rfl rfl,
    at_header runtimeSafety _ (ownerCell runtimeSafety true stack) 2 (-1)
      (initial_owner_and_spare runtimeSafety stack).1 rfl rfl]
  cases runtimeSafety <;> cases stack <;> constructor <;> try constructor <;> rfl

theorem full_capacity_is_scope_rejection (runtimeSafety stack : Bool) :
    execute runtimeSafety {before runtimeSafety true stack with
      heap := (before runtimeSafety true stack).heap.replace 3
        {ownerCell runtimeSafety true stack with cells := oldCells.set 32 (.scalar (.int false 64 1))}} = .error .unsupported := by
  rw [at_header runtimeSafety _ {ownerCell runtimeSafety true stack with cells := oldCells.set 32 (.scalar (.int false 64 1))} 2 1
    (by cases runtimeSafety <;> cases stack <;> decide) rfl rfl]
  cases runtimeSafety <;> cases stack <;> rfl

end Compiler.Extraction.RepresentativeArray.Owner.AppendTests
