/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayPublication
import Compiler.Extraction.RepresentativeOwnerWrites
import Compiler.ZigAir.MemoryWordArrayWrites

namespace Compiler.Extraction.RepresentativeArray.Publication
open Compiler.ZigAir.Memory

theorem owner_pointer_selector (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (writable : Bool) (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) :
    fieldPointer state (.pointer (.pointer writable false itemsType) ⟨lifetime, Owner.representativesOffset + itemsOffset⟩) 0 =
      .ok (.pointer (.pointer writable false pointerType) ⟨lifetime, Owner.representativesOffset + itemsOffset⟩) := by
  have parent := root_access state lifetime cell (Owner.layout runtimeSafety) false initial found
    (typed ▸ Owner.view_layout_checked runtimeSafety) (by cases runtimeSafety <;> decide) (by simp)
  have header := Owner.header_region_access runtimeSafety state ⟨lifetime, 0⟩ cell false parent
  have items := access_subregion state (Owner.headerAddress ⟨lifetime, 0⟩) Owner.representativesLayout ⟨16, 8⟩ itemsOffset
    false cell header (by decide) (by decide) (by decide) (by decide)
  have declared : acceptsView cell.type (Owner.representativesOffset + itemsOffset) itemsType = true :=
    typed ▸ (Owner.header_value_views_checked runtimeSafety).1
  simpa only [Nat.add_zero] using fieldPointer_of_access state
    ⟨lifetime, Owner.representativesOffset + itemsOffset⟩ cell itemsType pointerType ⟨16, 8⟩ 0 writable false rfl
    items declared pointer_field_checked

/-- The pointer leaf's view and geometry come from the captured containing
owner. No initialized destination or successful-store premise is required. -/
theorem owner_pointer_store_total (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (data : Address) (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) (writable : cell.writable = true) :
    ∃ after, store state (.pointer (.pointer true false pointerType) ⟨lifetime, Owner.representativesOffset + itemsOffset⟩)
      (.pointer pointerType data) = .ok after := by
  have parent := root_access state lifetime cell (Owner.layout runtimeSafety) true initial found
    (typed ▸ Owner.view_layout_checked runtimeSafety) (by cases runtimeSafety <;> decide) (by intro _; exact writable)
  have header := Owner.header_region_access runtimeSafety state ⟨lifetime, 0⟩ cell true parent
  have pointer := access_subregion state (Owner.headerAddress ⟨lifetime, 0⟩) Owner.representativesLayout ⟨8, 8⟩ itemsOffset
    true cell header (by decide) (by decide) (by decide) (by decide)
  apply store_subobject_total state ⟨lifetime, Owner.representativesOffset + itemsOffset⟩ ⟨8, 8⟩ cell
    (.pointer pointerType data) rfl rfl pointer
  · rw [typed]
    change acceptsView (Owner.viewType runtimeSafety) (Owner.representativesOffset + itemsOffset) pointerType = true
    cases runtimeSafety <;> decide
  · intro entry member
    simp only [Value.leaves, List.mem_cons, List.not_mem_nil, or_false] at member
    subst entry
    simpa only [Nat.add_zero, Value.type, typed, pointerType] using (Owner.header_leaf_types_checked runtimeSafety).1

theorem run_of_stores (state middle after : State) (header data : Address) (capacity : Int)
    (selectedItems : fieldPointer state (.pointer (.pointer true false allocationType) header) itemsOffset =
      .ok (.pointer (.pointer true false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩))
    (selectedPointer : fieldPointer state
      (.pointer (.pointer true false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩) 0 =
      .ok (.pointer (.pointer true false pointerType) ⟨header.allocation, header.offset + itemsOffset⟩))
    (selectedCapacity : fieldPointer state (.pointer (.pointer true false allocationType) header) capacityOffset =
      .ok (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + capacityOffset⟩))
    (storedPointer : store state (.pointer (.pointer true false pointerType) ⟨header.allocation, header.offset + itemsOffset⟩)
      (.pointer pointerType data) = .ok middle)
    (storedCapacity : store middle (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + capacityOffset⟩)
      (.scalar (.int false 64 capacity)) = .ok after) :
    run state header data capacity = (.ok (), after) := by
  have selected := fieldPointer_after_store state middle _ (.pointer pointerType data) true false allocationType header capacityOffset storedPointer
  simp only [run, program, steps, write, itemsDataPointer, selectedItems, selectedPointer, bind, Except.bind, storedPointer,
    selected, selectedCapacity, storedCapacity]

/-- Readback follows the actual pointer-only store followed by capacity.
The original initialized length is retained through both assignments. -/
theorem header_after_pointer_capacity_stores (state middle after : State) (header beforeData data : Address)
    (length : Nat) (capacity : Int)
    (selectedItems : fieldPointer state (.pointer (.pointer false false allocationType) header) itemsOffset =
      .ok (.pointer (.pointer false false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩))
    (selectedCapacity : fieldPointer state (.pointer (.pointer false false allocationType) header) capacityOffset =
      .ok (.pointer (.pointer false false usize) ⟨header.allocation, header.offset + capacityOffset⟩))
    (loaded : readItems state header = .ok (.slice itemsType beforeData length))
    (storedPointer : store state (.pointer (.pointer true false pointerType) ⟨header.allocation, header.offset + itemsOffset⟩)
      (.pointer pointerType data) = .ok middle)
    (storedCapacity : store middle (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + capacityOffset⟩)
      (.scalar (.int false 64 capacity)) = .ok after) :
    readHeader after header = .ok (.slice itemsType data length, .scalar (.int false 64 capacity)) := by
  have selectors (offset : Nat) : fieldPointer after (.pointer (.pointer false false allocationType) header) offset =
      fieldPointer state (.pointer (.pointer false false allocationType) header) offset :=
    (fieldPointer_after_store _ _ _ _ false false _ _ offset storedCapacity).trans
      (fieldPointer_after_store _ _ _ _ false false _ _ offset storedPointer)
  have raw : load state (.pointer (.pointer false false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩) =
      .ok (.slice itemsType beforeData length) := by
    simpa only [readItems, readField, selectedItems, bind, Except.bind] using loaded
  have pointerRead := load_slice_after_pointer_store state middle ⟨header.allocation, header.offset + itemsOffset⟩ beforeData data
    false false true elementType length raw storedPointer
  have frame := load_disjoint_after_store middle true false usize ⟨header.allocation, header.offset + capacityOffset⟩
    (.scalar (.int false 64 capacity)) after false false itemsType (header.offset + itemsOffset) storedCapacity
    (by simp [Ty.readOffsets, itemsType, Value.leaves, itemsOffset, capacityOffset])
  have itemsRead := frame.trans pointerRead
  have capacityRead := load_alias_after_store _ true false _ _ _ _ false false storedCapacity
  simp only [readHeader, readItems, readField, selectors, selectedItems, selectedCapacity, bind, Except.bind, itemsRead, capacityRead]
  rfl

/-- Derive both assignments in a live writable captured owner from its current
slice read and evaluated new pointer/capacity. Backing ownership and its copied
contents are separate caller obligations; the header update supplies neither. -/
theorem run_verified (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (beforeData data : Address) (length capacity : Nat)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) (writable : cell.writable = true)
    (loaded : readItems state (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType beforeData length))
    (bounded : capacity < addressLimit) :
    ∃ after, run state (Owner.headerAddress ⟨lifetime, 0⟩) data capacity = (.ok (), after) ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType data length, .scalar (.int false 64 capacity)) ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ id, id ≠ lifetime → after.heap.lookup id = state.heap.lookup id) := by
  have header : Owner.headerAddress ⟨lifetime, 0⟩ = ⟨lifetime, Owner.representativesOffset⟩ := rfl
  rw [header] at loaded ⊢
  obtain ⟨middle, storedPointer⟩ := owner_pointer_store_total runtimeSafety state lifetime cell data initial found typed writable
  have validMiddle := store_preserves_valid _ _ _ _ initial storedPointer
  obtain ⟨middleCell, middleFound, shape⟩ := store_retains_shape _ _ _ _ storedPointer lifetime cell found
  obtain ⟨after, storedCapacity⟩ := Owner.header_store_total runtimeSafety middle lifetime middleCell capacityOffset
    (.scalar (.int false 64 capacity)) validMiddle middleFound (shape.2.1.trans typed) (shape.2.2.1.trans writable)
    (by simp only [Value.type, Compiler.ZigAir.Scalar.Value.type]; decide) (Value.usize_valid capacity bounded)
  have writes := Owner.root_header_fields runtimeSafety state lifetime cell true initial found typed
  have reads := Owner.root_header_fields runtimeSafety state lifetime cell false initial found typed
  rw [header] at writes reads
  have pointerSelected := owner_pointer_selector runtimeSafety state lifetime cell true initial found typed
  have executed : run state ⟨lifetime, Owner.representativesOffset⟩ data capacity = (.ok (), after) :=
    run_of_stores state middle after ⟨lifetime, Owner.representativesOffset⟩ data capacity
      writes.1 pointerSelected writes.2 storedPointer storedCapacity
  have storage := run_storage state ⟨lifetime, Owner.representativesOffset⟩ data capacity initial
  rw [executed] at storage
  exact ⟨after, executed, storage.1, storage.2.1,
    header_after_pointer_capacity_stores state middle after ⟨lifetime, Owner.representativesOffset⟩ beforeData data length capacity
      reads.1 reads.2 loaded storedPointer storedCapacity,
    storage.2.2.1, storage.2.2.2.1, storage.2.2.2.2⟩

theorem run_parent_borrow (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (data : Address) (capacity : Int) (parent : WordArray.View) (values : List (BitVec 32))
    (extent : Nat) (parentCell : Allocation) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (parentFound : state.heap.lookup parent.allocation = some parentCell)
    (parentType : parentCell.type = .array extent WordArray.word) (represented : WordArray.Represents state parent values) :
    (run state (Owner.headerAddress ⟨lifetime, 0⟩) data capacity).2.heap.lookup parent.allocation = some parentCell ∧
      WordArray.Represents (run state (Owner.headerAddress ⟨lifetime, 0⟩) data capacity).2 parent values := by
  have separate := state.heap.lookup_ne_of_type_ne parent.allocation lifetime parentCell cell parentFound found
    (by simp [parentType, typed, Owner.viewType])
  have frame := (run_storage state (Owner.headerAddress ⟨lifetime, 0⟩) data capacity initial).2.2.2.2 parent.allocation separate
  refine ⟨frame.trans parentFound, represented.1, ?_⟩
  intro index inside
  exact (load_eq_of_lookup state _ true false WordArray.word (parent.address index) frame).trans (represented.2 index inside)

end Compiler.Extraction.RepresentativeArray.Publication
