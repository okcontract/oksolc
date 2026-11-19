/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeOwnerWrites
import Compiler.Extraction.RepresentativeOwnerTests

namespace Compiler.Extraction.RepresentativeArray.Owner.FieldTests
open Compiler.ZigAir.Memory

def cell (runtimeSafety writable stack : Bool) (cells : Cells := []) : Allocation :=
  ⟨608, viewType runtimeSafety, cells, writable, stack⟩
def before (runtimeSafety writable stack : Bool) : State :=
  { RepresentativeArray.Tests.memory with
    heap := RepresentativeArray.Tests.memory.heap.replace 3 (cell runtimeSafety writable stack)
    nextAddress := 608 + (layout runtimeSafety).bytes }
def items : Value := .slice itemsType ⟨2, 0⟩ 2
def capacity : Value := .scalar (.int false 64 3)
def itemCells : Cells := (items.leaves (representativesOffset + itemsOffset)).reverse
def completedCells : Cells := itemCells.set (representativesOffset + capacityOffset) capacity
def withItems (runtimeSafety stack : Bool) : State :=
  { before runtimeSafety true stack with
    heap := (before runtimeSafety true stack).heap.replace 3 (cell runtimeSafety true stack itemCells) }
def after (runtimeSafety stack : Bool) : State :=
  { before runtimeSafety true stack with
    heap := (before runtimeSafety true stack).heap.replace 3 (cell runtimeSafety true stack completedCells) }
def execute (runtimeSafety : Bool) (state : State) (owner : Address := ⟨3, 0⟩) (data : Address := ⟨2, 0⟩)
    (length : Nat := 2) (capacity : Int := 3) : Except Fault State :=
  initializeHeader runtimeSafety state owner data length capacity

theorem initial_valid (runtimeSafety writable stack : Bool) : (before runtimeSafety writable stack).valid = true := by
  cases runtimeSafety <;> cases writable <;> cases stack <;> decide

private theorem selected (runtimeSafety writable stack : Bool) :
    fieldPointer (before runtimeSafety writable stack) (.pointer (.pointer true false (viewType runtimeSafety)) ⟨3, 0⟩)
      representativesOffset = .ok (.pointer (.pointer true false RepresentativeArray.allocationType) (headerAddress ⟨3, 0⟩)) :=
  root_header_pointer runtimeSafety (before runtimeSafety writable stack) 3 (cell runtimeSafety writable stack) true
    (initial_valid runtimeSafety writable stack) rfl rfl

theorem nominal_owner_resolves_complete_fields (runtimeSafety writable stack : Bool) :
    recordView (before runtimeSafety writable stack) (viewType runtimeSafety)
      (.pointer (.pointer writable false (allocationType runtimeSafety)) ⟨3, 0⟩) =
        .ok (.pointer (.pointer writable false (viewType runtimeSafety)) ⟨3, 0⟩) :=
  root_owner_view runtimeSafety (before runtimeSafety writable stack) 3 (cell runtimeSafety writable stack) writable
    (initial_valid runtimeSafety writable stack) rfl rfl

theorem embedded_selection_preserves_permission (runtimeSafety writable stack : Bool) :
    fieldPointer (before runtimeSafety writable stack) (.pointer (.pointer writable false (viewType runtimeSafety)) ⟨3, 0⟩)
      representativesOffset = .ok (.pointer (.pointer writable false RepresentativeArray.allocationType) ⟨3, 16⟩) :=
  root_header_pointer runtimeSafety (before runtimeSafety writable stack) 3 (cell runtimeSafety writable stack) writable
    (initial_valid runtimeSafety writable stack) rfl rfl

theorem header_selection_does_not_initialize (runtimeSafety : Bool) :
    readHeader (before runtimeSafety true true) (headerAddress ⟨3, 0⟩) = .error .uninitialized := by
  cases runtimeSafety <;> decide

theorem actual_two_header_stores (runtimeSafety stack : Bool) :
    store (before runtimeSafety true stack) (.pointer (.pointer true false itemsType) ⟨3, 16⟩) items = .ok (withItems runtimeSafety stack) ∧
      store (withItems runtimeSafety stack) (.pointer (.pointer true false usize) ⟨3, 32⟩) capacity = .ok (after runtimeSafety stack) := by
  cases runtimeSafety <;> cases stack <;> constructor <;> rfl

theorem actual_header_assignment (runtimeSafety stack : Bool) :
    execute runtimeSafety (before runtimeSafety true stack) = .ok (after runtimeSafety stack) := by
  have pointer := selected runtimeSafety true stack
  have written := actual_two_header_stores runtimeSafety stack
  simp only [execute, initializeHeader, pointer, bind, Except.bind, headerAddress, Nat.zero_add]
  change (do let next ← store (before runtimeSafety true stack) (.pointer (.pointer true false itemsType) ⟨3, 16⟩) items
             store next (.pointer (.pointer true false usize) ⟨3, 32⟩) capacity) = _
  simpa only [written.1, bind, Except.bind] using written.2

theorem header_assignment_without_store_premises (runtimeSafety stack : Bool) :
    ∃ finalState, execute runtimeSafety (before runtimeSafety true stack) = .ok finalState ∧
      finalState.valid = true ∧ (before runtimeSafety true stack).heap.RetainsShape finalState.heap ∧
      readHeader finalState ⟨3, 16⟩ = .ok (items, capacity) ∧
      finalState.nextId = (before runtimeSafety true stack).nextId ∧
      finalState.nextAddress = (before runtimeSafety true stack).nextAddress ∧
      (∀ other, other ≠ 3 → finalState.heap.lookup other = (before runtimeSafety true stack).heap.lookup other) :=
  initializeHeader_verified runtimeSafety (before runtimeSafety true stack) 3 (cell runtimeSafety true stack) ⟨2, 0⟩ 2 3
    (initial_valid runtimeSafety true stack) rfl rfl rfl (by decide) (by decide)

theorem readonly_readback_from_assignment (runtimeSafety stack : Bool) :
    readHeader (after runtimeSafety stack) ⟨3, 16⟩ = .ok (items, capacity) ∧
      (after runtimeSafety stack).valid = true := by
  obtain ⟨finalState, executed, valid, _, readback, _⟩ := header_assignment_without_store_premises runtimeSafety stack
  have same : finalState = after runtimeSafety stack := Except.ok.inj (executed.symm.trans (actual_header_assignment runtimeSafety stack))
  exact same ▸ ⟨readback, valid⟩

theorem source_bound_complete_representative (runtimeSafety : Bool) :
    representativeFields (after runtimeSafety true) ⟨3, 16⟩ 1 =
      .ok (.ok [Expression.Tests.item, Expression.Tests.arguments, Expression.Tests.id, Expression.Tests.sequence]) := by
  cases runtimeSafety <;> decide

theorem ordinary_source_bound_is_retained (runtimeSafety : Bool) :
    representative (after runtimeSafety true) ⟨3, 16⟩ 2 = .ok (.error .invalidId) := by
  cases runtimeSafety <;> decide

theorem reached_prefix_keeps_capacity_uninitialized (runtimeSafety : Bool) :
    readItems (withItems runtimeSafety true) ⟨3, 16⟩ = .ok items ∧
      readHeader (withItems runtimeSafety true) ⟨3, 16⟩ = .error .uninitialized := by
  cases runtimeSafety <;> decide

theorem partial_nested_slice_rejects (runtimeSafety : Bool) :
    let state := { before runtimeSafety true true with
      heap := (before runtimeSafety true true).heap.replace 3
        (cell runtimeSafety true true [(16, .pointer (.pointer true true elementType) ⟨2, 0⟩)]) }
    readHeader state ⟨3, 16⟩ = .error .uninitialized := by cases runtimeSafety <;> decide

theorem unrelated_storage_and_lifetimes_survive (runtimeSafety stack : Bool) :
    (after runtimeSafety stack).heap.lookup 1 = (before runtimeSafety true stack).heap.lookup 1 ∧
      (after runtimeSafety stack).heap.lookup 2 = (before runtimeSafety true stack).heap.lookup 2 ∧
      (after runtimeSafety stack).nextId = (before runtimeSafety true stack).nextId ∧
      (after runtimeSafety stack).nextAddress = (before runtimeSafety true stack).nextAddress := by
  obtain ⟨finalState, executed, _, _, _, ids, addresses, frame⟩ := header_assignment_without_store_premises runtimeSafety stack
  have same : finalState = after runtimeSafety stack := Except.ok.inj (executed.symm.trans (actual_header_assignment runtimeSafety stack))
  exact same ▸ ⟨frame 1 (by decide), frame 2 (by decide), ids, addresses⟩

theorem readonly_owner_cannot_store (runtimeSafety stack : Bool) :
    execute runtimeSafety (before runtimeSafety false stack) = .error .readOnly := by
  simp only [execute, initializeHeader, selected runtimeSafety false stack, bind, Except.bind, headerAddress, Nat.zero_add]
  cases runtimeSafety <;> cases stack <;> rfl

theorem malformed_evaluated_header_rejects (runtimeSafety : Bool) :
    execute runtimeSafety (before runtimeSafety true true) ⟨3, 0⟩ ⟨2, 0⟩ addressLimit = .error .malformed ∧
      execute runtimeSafety (before runtimeSafety true true) ⟨3, 0⟩ ⟨2, 0⟩ 2 (-1) = .error .malformed := by
  simp only [execute, initializeHeader, selected runtimeSafety true true, bind, Except.bind, headerAddress, Nat.zero_add]
  cases runtimeSafety <;> constructor <;> rfl

theorem opaque_fields_and_whole_owner_are_unsupported (runtimeSafety : Bool) :
    load (after runtimeSafety true) (.pointer (.pointer false false (viewType runtimeSafety)) ⟨3, 0⟩) = .error .unsupported ∧
      load (after runtimeSafety true) (.pointer (.pointer false false (.record "mem.Allocator" allocatorLayout)) ⟨3, 0⟩) = .error .unsupported := by
  have valid := (readonly_readback_from_assignment runtimeSafety true).2
  have accessed := root_access (after runtimeSafety true) 3 (cell runtimeSafety true true completedCells) (layout runtimeSafety) false
    valid rfl (view_layout_checked runtimeSafety) (by cases runtimeSafety <;> decide) (by simp)
  have allocatorAccess := access_subregion (after runtimeSafety true) ⟨3, 0⟩ (layout runtimeSafety) allocatorLayout allocatorOffset false
    (cell runtimeSafety true true completedCells) accessed (by decide) (by cases runtimeSafety <;> decide) (by decide)
    (by cases runtimeSafety <;> decide)
  change access (after runtimeSafety true) ⟨3, 0⟩ allocatorLayout false = .ok (cell runtimeSafety true true completedCells) at allocatorAccess
  have allocatorShape : (Ty.record "mem.Allocator" allocatorLayout).layout = some allocatorLayout := by decide
  constructor
  · simp only [load, view_layout_checked, accessed, bind, Except.bind, readCell]
    exact Cells.read_aggregate_unsupported _ _ _ _ _ _
  · simp only [load, allocatorShape, allocatorAccess, bind, Except.bind, readCell]
    exact Cells.read_record_unsupported _ _ _ _ _

theorem wrong_mode_owner_is_not_the_same_type :
    execute true (before false true true) = .error .memoryValidity ∧
      execute false (before true true true) = .error .unsupported := by decide

theorem omitted_owner_field_does_not_supply_complete_view (runtimeSafety : Bool) :
    let incomplete := match viewType runtimeSafety with
      | .aggregate name layout fields => .aggregate name layout (fields.take 2)
      | type => type
    let state := { before runtimeSafety true true with
      heap := (before runtimeSafety true true).heap.replace 3 { cell runtimeSafety true true with type := incomplete } }
    execute runtimeSafety state = .error .unsupported := by cases runtimeSafety <;> decide

theorem stale_owner_and_cleanup_reject (runtimeSafety : Bool) :
    execute runtimeSafety (before runtimeSafety true true) ⟨4, 0⟩ = .error .unallocated ∧
      execute runtimeSafety (cleanup 3 (before runtimeSafety true true)) = .error .unallocated ∧
      (cleanup 3 (before runtimeSafety true true)).nextId = (before runtimeSafety true true).nextId := by
  cases runtimeSafety <;> decide

def arrayCell (runtimeSafety writable : Bool) : Allocation := ⟨8, .array 2 (viewType runtimeSafety), [], writable, true⟩
-- Header-only offset fixture: referenced backing is not represented or dereferenced.
def arrayState (runtimeSafety writable : Bool) : State := ⟨[(7, arrayCell runtimeSafety writable)], 8, 8 + 2 * (layout runtimeSafety).bytes⟩

theorem nonzero_readonly_owner_selection (runtimeSafety writable : Bool) :
    fieldPointer (arrayState runtimeSafety writable)
      (.pointer (.pointer writable false (viewType runtimeSafety)) ⟨7, (layout runtimeSafety).bytes⟩) representativesOffset =
        .ok (.pointer (.pointer writable false RepresentativeArray.allocationType) ⟨7, (layout runtimeSafety).bytes + 16⟩) := by
  simpa only [Nat.one_mul] using
    array_header_pointer runtimeSafety (arrayState runtimeSafety writable) 7 2 1 (arrayCell runtimeSafety writable) writable
      (by cases runtimeSafety <;> cases writable <;> decide) rfl rfl (by decide)

theorem nonzero_header_assignment_and_readback (runtimeSafety : Bool) :
    let owner : Address := ⟨7, (layout runtimeSafety).bytes⟩
    (do let finalState ← execute runtimeSafety (arrayState runtimeSafety true) owner
        readHeader finalState (headerAddress owner)) = .ok (items, capacity) := by
  have pointer := nonzero_readonly_owner_selection runtimeSafety true
  simp only [execute, initializeHeader, pointer, bind, Except.bind]
  cases runtimeSafety <;> rfl

def firstHeaderCells : Cells :=
  (.slice itemsType ⟨9, 0⟩ 0 : Value).leaves 16 ++ (.scalar (.int false 64 4) : Value).leaves 32
def firstInitialized (runtimeSafety : Bool) : State :=
  { arrayState runtimeSafety true with heap := [(7, { arrayCell runtimeSafety true with cells := firstHeaderCells })] }

theorem nonzero_assignment_preserves_first_header (runtimeSafety : Bool) :
    (do let finalState ← execute runtimeSafety (firstInitialized runtimeSafety) ⟨7, (layout runtimeSafety).bytes⟩
        readHeader finalState ⟨7, 16⟩) = .ok (.slice itemsType ⟨9, 0⟩ 0, .scalar (.int false 64 4)) := by
  have pointer := array_header_pointer runtimeSafety (firstInitialized runtimeSafety) 7 2 1
    { arrayCell runtimeSafety true with cells := firstHeaderCells } true
    (by cases runtimeSafety <;> decide) rfl rfl (by decide)
  simp only [execute, initializeHeader, Nat.one_mul] at pointer ⊢
  rw [pointer]
  cases runtimeSafety <;> rfl

theorem enclosing_array_extent_is_retained (runtimeSafety : Bool) :
    execute runtimeSafety (arrayState runtimeSafety true) ⟨7, 2 * (layout runtimeSafety).bytes⟩ = .error .memoryValidity := by
  cases runtimeSafety <;> decide

theorem owner_is_not_representative_backing (runtimeSafety : Bool) :
    (do let finalState ← execute runtimeSafety (before runtimeSafety true true) ⟨3, 0⟩ ⟨3, 0⟩
        representative finalState ⟨3, 16⟩ 0) = .error .unsupported := by
  simp only [execute, initializeHeader, selected runtimeSafety true true, bind, Except.bind, headerAddress, Nat.zero_add]
  cases runtimeSafety <;> rfl

end Compiler.Extraction.RepresentativeArray.Owner.FieldTests
