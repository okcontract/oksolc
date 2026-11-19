/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeOwnerFields
import Compiler.ZigAir.MemoryAllocationShape

namespace Compiler.Extraction.ExpressionMap
open Compiler.ZigAir.Memory
open RepresentativeArray

/-- Both native selectors retain the containing allocation and its permissions. -/
def cacheFieldPointer (runtimeSafety : Bool) (state : State) (owner : Address) (writable : Bool) (offset : Nat) : Except Fault Value := do
  let cache ← fieldPointer state (.pointer (.pointer writable false (Owner.viewType runtimeSafety)) owner) (Owner.expressionsOffset runtimeSafety)
  fieldPointer state cache offset

def sizePointer (runtimeSafety : Bool) (state : State) (owner : Address) (writable : Bool) : Except Fault Value :=
  cacheFieldPointer runtimeSafety state owner writable (sizeOffset runtimeSafety)

def readSize (runtimeSafety : Bool) (state : State) (owner : Address) : Except Fault Value := do
  let pointer ← sizePointer runtimeSafety state owner false
  load state pointer

/-- The pinned get/getContext/getAdapted/getIndex path returns null immediately
when size is zero, before hashing or inspecting metadata. Evaluating the caller's
key is outside this operation. Nonempty probing is explicitly unsupported. -/
def getEmptyFrom (read : Except Fault Value) (_key : α) : Except Fault (Option Compiler.Algebraic.NodeId) := do
  let size ← read
  if size = .scalar (.int false 32 0) then .ok none else .error .unsupported

def getEmpty (runtimeSafety : Bool) (state : State) (owner : Address) (key : α) : Except Fault (Option Compiler.Algebraic.NodeId) :=
  getEmptyFrom (readSize runtimeSafety state owner) key

def initializeSize (runtimeSafety : Bool) (state : State) (owner : Address) : Except Fault State := do
  let pointer ← sizePointer runtimeSafety state owner true
  store state pointer (.scalar (.int false 32 0))

theorem owner_cache_view (runtimeSafety : Bool) :
    acceptsView (Owner.viewType runtimeSafety) (Owner.expressionsOffset runtimeSafety) (allocationType runtimeSafety) = true := by
  cases runtimeSafety <;> decide +kernel

theorem root_field_pointer (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (writable : Bool)
    (offset : Nat) (child : Ty)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety)
    (field : fieldType (allocationType runtimeSafety) offset = some child) :
    cacheFieldPointer runtimeSafety state ⟨lifetime, 0⟩ writable offset =
      .ok (.pointer (.pointer writable false child) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + offset⟩) := by
  have selected := root_fieldPointer state lifetime cell (Owner.viewType runtimeSafety) (allocationType runtimeSafety)
    (Owner.layout runtimeSafety) (Owner.expressionsOffset runtimeSafety) writable false initial found typed (Owner.view_layout_checked runtimeSafety)
    (by cases runtimeSafety <;> decide) (by cases runtimeSafety <;> rfl)
  have parent := root_access state lifetime cell (Owner.layout runtimeSafety) false initial found
    (typed ▸ Owner.view_layout_checked runtimeSafety) (by cases runtimeSafety <;> decide) (by simp)
  have accessed := access_subregion state ⟨lifetime, 0⟩ (Owner.layout runtimeSafety) (Owner.expressionsLayout runtimeSafety)
    (Owner.expressionsOffset runtimeSafety) false cell parent (by cases runtimeSafety <;> decide)
    (by cases runtimeSafety <;> decide) (by cases runtimeSafety <;> decide) (by cases runtimeSafety <;> decide)
  have inner := fieldPointer_of_access state ⟨lifetime, (Owner.expressionsOffset runtimeSafety)⟩ cell (allocationType runtimeSafety) child
    (Owner.expressionsLayout runtimeSafety) offset writable false (by cases runtimeSafety <;> decide)
    (by simpa only [Nat.zero_add] using accessed) (typed.symm ▸ owner_cache_view runtimeSafety) field
  simpa only [cacheFieldPointer, selected, bind, Except.bind] using inner

theorem root_size_pointer (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (writable : Bool)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) :
    sizePointer runtimeSafety state ⟨lifetime, 0⟩ writable =
      .ok (.pointer (.pointer writable false countType) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (sizeOffset runtimeSafety)⟩) :=
  root_field_pointer runtimeSafety state lifetime cell writable (sizeOffset runtimeSafety) countType initial found typed
    (by cases runtimeSafety <;> rfl)

theorem empty_get (runtimeSafety : Bool) (state : State) (owner : Address) (key : α)
    (loaded : readSize runtimeSafety state owner = .ok (.scalar (.int false 32 0))) :
    getEmpty runtimeSafety state owner key = .ok none := by simp only [getEmpty, getEmptyFrom, loaded, bind, Except.bind, ↓reduceIte]

/-- A store's access and typed leaves follow from the captured containing owner.
Neither an initialized count nor a successful write is a premise. Metadata and
lock contents are deliberately not manufactured by this refinement. -/
theorem initialize_verified (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) (writable : cell.writable = true) :
    ∃ after, initializeSize runtimeSafety state ⟨lifetime, 0⟩ = .ok after ∧
      store state (.pointer (.pointer true false countType) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (sizeOffset runtimeSafety)⟩)
        (.scalar (.int false 32 0)) = .ok after ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readSize runtimeSafety after ⟨lifetime, 0⟩ = .ok (.scalar (.int false 32 0)) ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ other, other ≠ lifetime → after.heap.lookup other = state.heap.lookup other) := by
  have parent := root_access state lifetime cell (Owner.layout runtimeSafety) true initial found
    (typed ▸ Owner.view_layout_checked runtimeSafety) (by cases runtimeSafety <;> decide) (by intro _; exact writable)
  have accessed := access_subregion state ⟨lifetime, 0⟩ (Owner.layout runtimeSafety) ⟨4, 4⟩
    ((Owner.expressionsOffset runtimeSafety) + (sizeOffset runtimeSafety)) true cell parent (by decide)
    (by cases runtimeSafety <;> decide) (by cases runtimeSafety <;> decide) (by cases runtimeSafety <;> decide)
  obtain ⟨after, stored⟩ := store_subobject_total state ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (sizeOffset runtimeSafety)⟩ ⟨4, 4⟩ cell
    (.scalar (.int false 32 0)) (by decide) rfl (by simpa only [Nat.zero_add] using accessed) (by rw [typed]; cases runtimeSafety <;> rfl)
    (by intro entry member; simp only [Value.leaves, List.mem_singleton] at member; subst entry
        rw [typed]; cases runtimeSafety <;> rfl)
  have valid := store_preserves_valid _ _ _ _ initial stored
  obtain ⟨finalCell, finalFound, shape⟩ := store_retains_shape _ _ _ _ stored lifetime cell found
  refine ⟨after, ?_, stored, valid, store_retains_shape _ _ _ _ stored, ?_,
    (store_keeps_counters _ _ _ _ stored).1, (store_keeps_counters _ _ _ _ stored).2,
    heap_after_store_other _ true false countType _ _ _ stored⟩
  · simp only [initializeSize, root_size_pointer runtimeSafety state lifetime cell true initial found typed, bind, Except.bind]
    exact stored
  · simp only [readSize, root_size_pointer runtimeSafety after lifetime finalCell false valid finalFound (shape.2.1.trans typed),
      bind, Except.bind]
    exact load_alias_after_store state true false countType _ _ after false false stored

/-- A store disjoint from both captured header fields preserves their complete
readback, including uninitialized or exceptional observations. -/
theorem header_frame_of_store (runtimeSafety : Bool) (state after : State) (lifetime : Nat) (cell : Allocation)
    (value : Value) (offset : Nat)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety)
    (stored : store state (.pointer (.pointer true false value.type) ⟨lifetime, offset⟩) value = .ok after)
    (apartItems : ∀ position ∈ itemsType.readOffsets (Owner.representativesOffset + itemsOffset),
      ∀ entry ∈ value.leaves offset, position ≠ entry.1)
    (apartCapacity : ∀ position ∈ usize.readOffsets (Owner.representativesOffset + capacityOffset),
      ∀ entry ∈ value.leaves offset, position ≠ entry.1) :
    RepresentativeArray.readHeader after (Owner.headerAddress ⟨lifetime, 0⟩) =
      RepresentativeArray.readHeader state (Owner.headerAddress ⟨lifetime, 0⟩) := by
  have fields := Owner.root_header_fields runtimeSafety state lifetime cell false initial found typed
  have selector := fun offset => fieldPointer_after_store state after _ _ false false RepresentativeArray.allocationType
    (Owner.headerAddress ⟨lifetime, 0⟩) offset stored
  have items := load_disjoint_after_store state true false value.type _ _ after false false RepresentativeArray.itemsType
    (Owner.representativesOffset + RepresentativeArray.itemsOffset) stored apartItems
  have capacity := load_disjoint_after_store state true false value.type _ _ after false false usize
    (Owner.representativesOffset + RepresentativeArray.capacityOffset) stored apartCapacity
  simp only [RepresentativeArray.readHeader, RepresentativeArray.readItems, RepresentativeArray.readField,
    selector, fields.1, fields.2, bind, Except.bind, items, capacity]

theorem header_frame (runtimeSafety : Bool) (state after : State) (lifetime : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety)
    (stored : store state (.pointer (.pointer true false countType) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (sizeOffset runtimeSafety)⟩)
      (.scalar (.int false 32 0)) = .ok after) :
    RepresentativeArray.readHeader after (Owner.headerAddress ⟨lifetime, 0⟩) =
      RepresentativeArray.readHeader state (Owner.headerAddress ⟨lifetime, 0⟩) :=
  header_frame_of_store runtimeSafety state after lifetime cell (.scalar (.int false 32 0))
    ((Owner.expressionsOffset runtimeSafety) + (sizeOffset runtimeSafety)) initial found typed stored (by cases runtimeSafety <;> decide) (by cases runtimeSafety <;> decide)

end Compiler.Extraction.ExpressionMap
