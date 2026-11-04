/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeOwnerFields
import Compiler.ZigAir.MemoryAllocationShape

namespace Compiler.Extraction.RepresentativeArray.Owner
open Compiler.ZigAir.Memory

/-- Derived from the existing complete captured header, with no independent
layout table or object store. Inputs to the assignment have already been evaluated. -/
private def headerSlots : List (Nat × Ty) := match RepresentativeArray.allocationType with
  | .aggregate _ _ fields => fields.map (fun field => (field.1, field.2.type))
  | _ => []

private theorem slot_geometry (offset : Nat) (type : Ty) (member : (offset, type) ∈ headerSlots) :
    ∃ region, type.layout = some region ∧ 0 < region.bytes ∧
      offset + region.bytes ≤ representativesLayout.bytes ∧ offset % region.alignment = 0 ∧
      representativesLayout.alignment % region.alignment = 0 := by
  simp only [headerSlots, RepresentativeArray.allocationType, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false, Field.type, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, rfl, by decide⟩

private theorem slot_view (runtimeSafety : Bool) (offset : Nat) (value : Value)
    (member : (offset, value.type) ∈ headerSlots) (valid : value.valid = true) :
    acceptsView (viewType runtimeSafety) (representativesOffset + offset) value.type = true ∧
      (∀ entry ∈ value.leaves 0,
        leafType (viewType runtimeSafety) (representativesOffset + offset + entry.1) = some entry.2.type) := by
  have views := header_value_views_checked runtimeSafety
  have leaves := header_leaf_types_checked runtimeSafety
  simp only [headerSlots, RepresentativeArray.allocationType, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false, Field.type, Prod.mk.injEq] at member
  rcases member with ⟨rfl, typed⟩ | ⟨rfl, typed⟩
  all_goals cases value with
    | optionalScalar _ _ | optionalObject _ _ _ => cases typed
    | scalar value =>
      simp only [Value.type] at typed
      all_goals try contradiction
      all_goals cases value <;> simp_all [Value.type, Compiler.ZigAir.Scalar.Value.type, Value.valid,
        Value.leaves, itemsType, elementType, usize, representativesOffset, itemsOffset, capacityOffset]
    | pointer type address =>
      simp only [Value.type] at typed
      all_goals subst type
      all_goals simp_all [Value.valid]
    | slice type address length =>
      simp only [Value.type] at typed
      all_goals subst type
      all_goals simp_all [Value.type, Value.valid, Value.leaves, Compiler.ZigAir.Scalar.Value.type,
        itemsType, elementType, usize, representativesOffset, itemsOffset, capacityOffset]

/-- Valid header members initialize their actual region inside a declared live
owner. Access, permission and leaf types come from the captured containing owner
and header, rather than a successful-store or initialized-destination premise. -/
theorem header_store_total (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (offset : Nat) (value : Value) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = viewType runtimeSafety)
    (writable : cell.writable = true) (member : (offset, value.type) ∈ headerSlots) (valid : value.valid = true) :
    ∃ after, store state (.pointer (.pointer true false value.type) ⟨lifetime, representativesOffset + offset⟩) value = .ok after := by
  obtain ⟨region, shaped, positive, bounded, aligned, divided⟩ := slot_geometry offset value.type member
  have parent := root_access state lifetime cell (layout runtimeSafety) true initial found (typed ▸ view_layout_checked runtimeSafety)
    (by cases runtimeSafety <;> decide) (by intro _; exact writable)
  have header := header_region_access runtimeSafety state ⟨lifetime, 0⟩ cell true parent
  have accessed := access_subregion state (headerAddress ⟨lifetime, 0⟩) representativesLayout region offset true cell
    header positive bounded aligned divided
  have declared := slot_view runtimeSafety offset value member valid
  exact store_subobject_total state ⟨lifetime, representativesOffset + offset⟩ region cell value valid shaped accessed
    (typed.symm ▸ declared.1) (typed.symm ▸ declared.2)

/-- Refine the assignment of the already evaluated header into its sparse typed
leaves. Selection checks the complete owner before either store. This does not
describe native allocator/cache initialization or Zig initializer evaluation. -/
def initializeHeader (runtimeSafety : Bool) (state : State) (owner data : Address) (length : Nat) (capacity : Int) : Except Fault State := do
  let selected ← fieldPointer state (.pointer (.pointer true false (viewType runtimeSafety)) owner) representativesOffset
  let .pointer _ header := selected | .error .malformed
  let withItems ← store state (.pointer (.pointer true false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩)
    (.slice itemsType data length)
  store withItems (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + capacityOffset⟩)
    (.scalar (.int false 64 capacity))

theorem initializeHeader_verified (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (data : Address) (length : Nat) (capacity : Int) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = viewType runtimeSafety)
    (writable : cell.writable = true) (lengthValid : length < addressLimit)
    (capacityValid : (Compiler.ZigAir.Scalar.Ty.int false 64).contains capacity = true) :
    ∃ after, initializeHeader runtimeSafety state ⟨lifetime, 0⟩ data length capacity = .ok after ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after (headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType data length, .scalar (.int false 64 capacity)) ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ other, other ≠ lifetime → after.heap.lookup other = state.heap.lookup other) := by
  obtain ⟨withItems, storedItems⟩ := header_store_total runtimeSafety state lifetime cell itemsOffset
    (.slice itemsType data length) initial found typed writable (by simp only [Value.type]; decide)
    (by simpa only [Value.valid, itemsType, decide_eq_true_eq] using lengthValid)
  change store state (.pointer (.pointer true false itemsType) ⟨lifetime, representativesOffset + itemsOffset⟩)
    (.slice itemsType data length) = .ok withItems at storedItems
  have validItems := store_preserves_valid _ _ _ _ initial storedItems
  obtain ⟨itemCell, foundItems, shapeItems⟩ := store_retains_shape _ _ _ _ storedItems lifetime cell found
  obtain ⟨after, storedCapacity⟩ := header_store_total runtimeSafety withItems lifetime itemCell capacityOffset
    (.scalar (.int false 64 capacity)) validItems foundItems (shapeItems.2.1.trans typed) (shapeItems.2.2.1.trans writable)
    (by simp only [Value.type, Compiler.ZigAir.Scalar.Value.type]; decide) capacityValid
  change store withItems (.pointer (.pointer true false usize) ⟨lifetime, representativesOffset + capacityOffset⟩)
    (.scalar (.int false 64 capacity)) = .ok after at storedCapacity
  have selected := root_header_pointer runtimeSafety state lifetime cell true initial found typed
  have fields := root_header_fields runtimeSafety state lifetime cell false initial found typed
  refine ⟨after, ?_, store_preserves_valid _ _ _ _ validItems storedCapacity,
    (store_retains_shape _ _ _ _ storedItems).trans (store_retains_shape _ _ _ _ storedCapacity), ?_, ?_, ?_, ?_⟩
  · simp only [initializeHeader, selected, bind, Except.bind, headerAddress, Nat.zero_add, storedItems, storedCapacity]
  · exact header_after_subobject_stores state withItems after (headerAddress ⟨lifetime, 0⟩) data length capacity
      fields.1 fields.2 storedItems storedCapacity
  · exact (store_keeps_counters _ _ _ _ storedCapacity).1.trans (store_keeps_counters _ _ _ _ storedItems).1
  · exact (store_keeps_counters _ _ _ _ storedCapacity).2.trans (store_keeps_counters _ _ _ _ storedItems).2
  · intro other different
    exact (heap_after_store_other _ true false usize _ _ _ storedCapacity other different).trans
      (heap_after_store_other _ true false itemsType _ _ _ storedItems other different)

end Compiler.Extraction.RepresentativeArray.Owner
