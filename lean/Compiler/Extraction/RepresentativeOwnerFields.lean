/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeOwner

namespace Compiler.Extraction.RepresentativeArray.Owner
open Compiler.ZigAir.Memory

theorem view_layout_checked (runtimeSafety : Bool) : (viewType runtimeSafety).layout = some (layout runtimeSafety) := by
  cases runtimeSafety <;> decide

theorem header_field_checked (runtimeSafety : Bool) :
    fieldType (viewType runtimeSafety) representativesOffset = some RepresentativeArray.allocationType := by
  cases runtimeSafety <;> decide

theorem header_view_checked (runtimeSafety : Bool) :
    acceptsView (viewType runtimeSafety) representativesOffset RepresentativeArray.allocationType = true := by
  cases runtimeSafety <;> decide

theorem header_value_views_checked (runtimeSafety : Bool) :
    acceptsView (viewType runtimeSafety) (representativesOffset + itemsOffset) itemsType = true ∧
      acceptsView (viewType runtimeSafety) (representativesOffset + capacityOffset) usize = true := by
  cases runtimeSafety <;> decide

theorem header_leaf_types_checked (runtimeSafety : Bool) :
    leafType (viewType runtimeSafety) (representativesOffset + itemsOffset) = some (.pointer true true elementType) ∧
      leafType (viewType runtimeSafety) (representativesOffset + itemsOffset + 8) = some usize ∧
      leafType (viewType runtimeSafety) (representativesOffset + capacityOffset) = some usize := by
  cases runtimeSafety <;> decide

/-- Selection uses the complete captured owner and the existing allocation.
The access/type premises contain no initialized cells or successful selector. -/
theorem header_pointer (runtimeSafety : Bool) (state : State) (owner : Address) (cell : Allocation) (writable : Bool)
    (accessed : access state owner (layout runtimeSafety) false = .ok cell)
    (declared : acceptsView cell.type owner.offset (viewType runtimeSafety) = true) :
    fieldPointer state (.pointer (.pointer writable false (viewType runtimeSafety)) owner) representativesOffset =
      .ok (.pointer (.pointer writable false RepresentativeArray.allocationType) (headerAddress owner)) :=
  fieldPointer_of_access state owner cell (viewType runtimeSafety) RepresentativeArray.allocationType
    (layout runtimeSafety) representativesOffset writable false (view_layout_checked runtimeSafety)
    accessed declared (header_field_checked runtimeSafety)

theorem root_header_pointer (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (writable : Bool)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = viewType runtimeSafety) :
    fieldPointer state (.pointer (.pointer writable false (viewType runtimeSafety)) ⟨lifetime, 0⟩) representativesOffset =
      .ok (.pointer (.pointer writable false RepresentativeArray.allocationType) (headerAddress ⟨lifetime, 0⟩)) :=
  root_fieldPointer state lifetime cell (viewType runtimeSafety) RepresentativeArray.allocationType
    (layout runtimeSafety) representativesOffset writable false initial found typed (view_layout_checked runtimeSafety)
    (by cases runtimeSafety <;> decide) (header_field_checked runtimeSafety)

/-- A native nominal owner reference resolves only against its complete declared
owner in the same live allocation. Identity/extent alone never supplies fields. -/
theorem root_owner_view (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (writable : Bool)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = viewType runtimeSafety) :
    recordView state (viewType runtimeSafety) (.pointer (.pointer writable false (allocationType runtimeSafety)) ⟨lifetime, 0⟩) =
      .ok (.pointer (.pointer writable false (viewType runtimeSafety)) ⟨lifetime, 0⟩) :=
  recordView_root state lifetime cell _ _ _ writable false initial found typed (view_layout_checked runtimeSafety)
    (by cases runtimeSafety <;> decide)

/-- A nested owner at a nonzero array offset retains its enclosing lifetime and
stride. Only the declared in-bounds owner is selected; contents are not supplied. -/
theorem array_header_pointer (runtimeSafety : Bool) (state : State) (lifetime extent index : Nat) (cell : Allocation) (writable : Bool)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array extent (viewType runtimeSafety)) (inside : index < extent) :
    fieldPointer state (.pointer (.pointer writable false (viewType runtimeSafety)) ⟨lifetime, index * (layout runtimeSafety).bytes⟩)
      representativesOffset = .ok (.pointer (.pointer writable false RepresentativeArray.allocationType)
        (headerAddress ⟨lifetime, index * (layout runtimeSafety).bytes⟩)) := by
  have accessed := array_access_permitted state lifetime extent index (layout runtimeSafety).bytes (viewType runtimeSafety)
    (layout runtimeSafety) cell initial found typed (view_layout_checked runtimeSafety)
    (by cases runtimeSafety <;> decide) (by cases runtimeSafety <;> decide) inside (by simp) false (by simp)
  have declared : acceptsView cell.type (index * (layout runtimeSafety).bytes) (viewType runtimeSafety) = true := by
    rw [typed, acceptsView_array, view_layout_checked runtimeSafety]
    have positive : 0 < (layout runtimeSafety).bytes := by cases runtimeSafety <;> decide
    simp [Nat.mul_div_cancel index positive, positive, inside]
  exact header_pointer runtimeSafety state _ cell writable accessed declared

/-- The same enclosing root derives both embedded header selectors before any
payload is initialized. Readonly allocation metadata is retained unchanged. -/
theorem root_header_fields (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (writable : Bool)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = viewType runtimeSafety) :
    fieldPointer state (.pointer (.pointer writable false RepresentativeArray.allocationType) (headerAddress ⟨lifetime, 0⟩)) itemsOffset =
      .ok (.pointer (.pointer writable false itemsType) ⟨lifetime, representativesOffset + itemsOffset⟩) ∧
    fieldPointer state (.pointer (.pointer writable false RepresentativeArray.allocationType) (headerAddress ⟨lifetime, 0⟩)) capacityOffset =
      .ok (.pointer (.pointer writable false usize) ⟨lifetime, representativesOffset + capacityOffset⟩) := by
  have parent := root_access state lifetime cell (layout runtimeSafety) false initial found (typed ▸ view_layout_checked runtimeSafety)
    (by cases runtimeSafety <;> decide) (by simp)
  have accessed := header_region_access runtimeSafety state ⟨lifetime, 0⟩ cell false parent
  have declared : acceptsView cell.type (headerAddress ⟨lifetime, 0⟩).offset RepresentativeArray.allocationType = true := by
    simpa only [typed, headerAddress, Nat.zero_add] using header_view_checked runtimeSafety
  exact ⟨fieldPointer_of_access state (headerAddress ⟨lifetime, 0⟩) cell RepresentativeArray.allocationType itemsType
      representativesLayout itemsOffset writable false header_layout_checked accessed declared field_types_checked.1,
    fieldPointer_of_access state (headerAddress ⟨lifetime, 0⟩) cell RepresentativeArray.allocationType usize
      representativesLayout capacityOffset writable false header_layout_checked accessed declared field_types_checked.2⟩

end Compiler.Extraction.RepresentativeArray.Owner
