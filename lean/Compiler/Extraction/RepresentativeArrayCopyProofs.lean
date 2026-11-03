/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayCopyFrame
import Compiler.ZigAir.MemoryWordArrayWrites

namespace Compiler.Extraction.RepresentativeArray.Copy
open Compiler.ZigAir.Memory

theorem field_store_readback (state after : State) (target capacity index offset : Nat) (cell : Allocation)
    (type : Ty) (value : Value) (initial : state.valid = true) (found : state.heap.lookup target = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : index < capacity) (member : (offset, type) ∈ expressionSlots)
    (stored : store state (.pointer (.pointer true false type) ⟨target, index * 32 + offset⟩) value = .ok after) :
    Expression.readField after false ⟨target, index * 32⟩ offset = .ok value := by
  have selected := element_fieldPointer state target capacity index cell offset type false initial found typed writable inside
    (slot_declared offset type member)
  have retained := fieldPointer_after_store state after _ value false false Expression.allocationType ⟨target, index * 32⟩ offset stored
  simpa only [Expression.readField, retained, selected, bind, Except.bind] using
    load_alias_after_store state true false type ⟨target, index * 32 + offset⟩ value after false false stored

/-- Every requested captured field is copied from the same source observation.
Checked source reads derive value typing; live writable target geometry derives
all stores. No successful-copy or initialized-target premise is supplied. -/
theorem fields_verified (slots : List (Nat × Ty)) (state : State) (source target capacity index : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup target = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : index < capacity) (separate : source ≠ target)
    (declared : ∀ slot ∈ slots, slot ∈ expressionSlots) (unique : (slots.map Prod.fst).Nodup)
    (ready : ∀ slot ∈ slots, ∃ value, Expression.readField state false ⟨source, index * 32⟩ slot.1 = .ok value) :
    ∃ after, fields slots ⟨source, index * 32⟩ ⟨target, index * 32⟩ state = (.ok (), after) ∧
      ∀ slot ∈ slots, Expression.readField after false ⟨target, index * 32⟩ slot.1 =
        Expression.readField state false ⟨source, index * 32⟩ slot.1 := by
  induction slots generalizing state cell with
  | nil => exact ⟨state, rfl, by simp⟩
  | cons slot tail ih =>
    rcases slot with ⟨offset, type⟩
    have headMember := declared (offset, type) (by simp)
    have tailDeclared := fun slot member => declared slot (List.mem_cons_of_mem (offset, type) member)
    have distinct := List.nodup_cons.mp unique
    obtain ⟨value, loaded⟩ := ready (offset, type) (by simp)
    have valueTyped := readField_hasType state ⟨source, index * 32⟩ offset type value (slot_declared _ _ headMember) loaded
    simp only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] at valueTyped
    obtain ⟨middle, stored⟩ := field_store_total state target capacity index cell offset value initial found typed writable inside
      (by simpa only [valueTyped.1] using headMember) valueTyped.2
    rw [valueTyped.1] at stored
    have middleValid := store_preserves_valid _ _ _ _ initial stored
    obtain ⟨middleCell, middleFound, shape⟩ := store_retains_shape _ _ _ _ stored target cell found
    have sourceFrame (slot : Nat × Ty) (member : slot ∈ tail) :
        Expression.readField middle false ⟨source, index * 32⟩ slot.1 =
          Expression.readField state false ⟨source, index * 32⟩ slot.1 :=
      readField_after_slot_store state middle source target index index offset slot.1 slot.2 type value
        (tailDeclared slot member) headMember stored (Or.inl separate)
    obtain ⟨after, executed, copied⟩ := ih middle middleCell middleValid middleFound (shape.2.1.trans typed)
      (shape.2.2.1.trans writable) tailDeclared distinct.2 (fun slot member => by
        obtain ⟨value, read⟩ := ready slot (List.mem_cons_of_mem _ member)
        exact ⟨value, (sourceFrame slot member).trans read⟩)
    refine ⟨after, ?_, ?_⟩
    · simp only [fields, loaded, stored, executed]
    · intro slot member
      rcases List.mem_cons.mp member with same | member
      · subst slot
        have frame := fields_read_frame tail ⟨source, index * 32⟩ target index target index offset type middle headMember
          tailDeclared (fun slot member => Or.inr (Or.inr (by
            intro same
            apply distinct.1
            exact List.mem_map.mpr ⟨slot, member, same.symm⟩)))
        rw [executed] at frame
        exact frame.trans ((field_store_readback state middle target capacity index offset cell type value
          initial found typed writable inside headMember stored).trans loaded.symm)
      · exact (copied slot member).trans (sourceFrame slot member)

theorem captured_slots_unique : (expressionSlots.map Prod.fst).Nodup := by decide

/-- Copy any finite initialized prefix into live writable backing. Recursive
calls retain the source observations and prior destination elements. -/
theorem copyFrom_verified (remaining index : Nat) (state : State) (source target capacity : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup target = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (extent : index + remaining ≤ capacity) (separate : source ≠ target)
    (ready : ∀ other, index ≤ other → other < index + remaining → ∀ slot ∈ expressionSlots,
      ∃ value, Expression.readField state false ⟨source, other * 32⟩ slot.1 = .ok value) :
    ∃ after, copyFrom source target remaining index state = (.ok (), after) ∧
      ∀ other, index ≤ other → other < index + remaining → ∀ slot ∈ expressionSlots,
        Expression.readField after false ⟨target, other * 32⟩ slot.1 =
          Expression.readField state false ⟨source, other * 32⟩ slot.1 := by
  induction remaining generalizing index state cell with
  | zero => exact ⟨state, rfl, by intros; omega⟩
  | succ remaining ih =>
    obtain ⟨middle, copiedHead, headValues⟩ := fields_verified expressionSlots state source target capacity index cell
      initial found typed writable (by omega) separate (fun _ member => member) captured_slots_unique
      (ready index (by omega) (by omega))
    have middleStorage := fields_storage expressionSlots ⟨source, index * 32⟩ ⟨target, index * 32⟩ state initial
    rw [copiedHead] at middleStorage
    obtain ⟨middleCell, middleFound, shape⟩ := middleStorage.2.1 target cell found
    have sourceFrame (other : Nat) (slot : Nat × Ty) (member : slot ∈ expressionSlots) :
        Expression.readField middle false ⟨source, other * 32⟩ slot.1 =
          Expression.readField state false ⟨source, other * 32⟩ slot.1 := by
      have frame := fields_read_frame expressionSlots ⟨source, index * 32⟩ target index source other slot.1 slot.2 state
        member (fun _ member => member) (fun _ _ => Or.inl separate)
      simpa only [copiedHead] using frame
    obtain ⟨after, copiedTail, tailValues⟩ := ih (index + 1) middle middleCell middleStorage.1 middleFound
      (shape.2.1.trans typed) (shape.2.2.1.trans writable) (by omega) (fun other lower upper slot member => by
        obtain ⟨value, read⟩ := ready other (by omega) (by omega) slot member
        exact ⟨value, (sourceFrame other slot member).trans read⟩)
    refine ⟨after, ?_, ?_⟩
    · simp only [copyFrom, copiedHead, copiedTail]
    · intro other lower upper slot member
      by_cases same : other = index
      · subst other
        have frame := copyFrom_read_frame source target remaining (index + 1) target index slot.1 slot.2 middle member
          (Or.inr (Or.inl (by omega)))
        rw [copiedTail] at frame
        exact frame.trans (headValues slot member)
      · exact (tailValues other (by omega) (by omega) slot member).trans (sourceFrame other slot member)

theorem run_empty (state : State) (source target : Nat) : run state source target 0 = (.ok (), state) := by simp [run]

theorem run_verified (state : State) (source target capacity length : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup target = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (extent : length ≤ capacity) (separate : length = 0 ∨ source ≠ target)
    (ready : ∀ index, index < length → ∀ slot ∈ expressionSlots,
      ∃ value, Expression.readField state false ⟨source, index * 32⟩ slot.1 = .ok value) :
    ∃ after, run state source target length = (.ok (), after) ∧ after.valid = true ∧
      state.heap.RetainsShape after.heap ∧ after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ id, id ≠ target → after.heap.lookup id = state.heap.lookup id) ∧
      (∀ index, index < length → ∀ slot ∈ expressionSlots,
        Expression.readField after false ⟨target, index * 32⟩ slot.1 =
          Expression.readField state false ⟨source, index * 32⟩ slot.1) := by
  by_cases empty : length = 0
  · subst length
    exact ⟨state, run_empty _ _ _, initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl, by intros; omega⟩
  · have apart : source ≠ target := separate.resolve_left empty
    obtain ⟨after, copied, values⟩ := copyFrom_verified length 0 state source target capacity cell initial found typed writable
      (by simpa only [Nat.zero_add] using extent) apart (fun index _ upper => ready index (by simpa only [Nat.zero_add] using upper))
    have executed : run state source target length = (.ok (), after) := by simp only [run, if_neg empty, if_neg apart, copied]
    have storage := run_storage state source target length initial
    rw [executed] at storage
    exact ⟨after, executed, storage.1, storage.2.1, storage.2.2.1, storage.2.2.2.1, storage.2.2.2.2,
      fun index upper => values index (Nat.zero_le _) (by simpa only [Nat.zero_add] using upper)⟩

theorem readFields_eq_of_slots (state after : State) (source target : Address)
    (copied : ∀ slot ∈ expressionSlots, Expression.readField after false target slot.1 =
      Expression.readField state false source slot.1) :
    Expression.readFields after false target = Expression.readFields state false source := by
  unfold Expression.readFields
  rw [copied (Expression.itemOffset, Expression.itemType) (by decide),
    copied (Expression.argumentsOffset, Expression.argumentsType) (by decide),
    copied (Expression.idOffset, Expression.idType) (by decide),
    copied (Expression.sequence_numberOffset, Expression.idType) (by decide)]

/-- Independent parent argument storage is retained for every copy outcome.
Its declared word-array type derives separation from representative backing. -/
theorem run_parent_borrow (state : State) (source target capacity length : Nat) (targetCell : Allocation)
    (parent : WordArray.View) (values : List (BitVec 32)) (extent : Nat) (parentCell : Allocation)
    (initial : state.valid = true) (targetFound : state.heap.lookup target = some targetCell)
    (targetType : targetCell.type = .array capacity Expression.allocationType)
    (parentFound : state.heap.lookup parent.allocation = some parentCell)
    (parentType : parentCell.type = .array extent WordArray.word)
    (represented : WordArray.Represents state parent values) :
    (run state source target length).2.heap.lookup parent.allocation = some parentCell ∧
      WordArray.Represents (run state source target length).2 parent values := by
  have separate := state.heap.lookup_ne_of_type_ne parent.allocation target parentCell targetCell parentFound targetFound
    (by simp [parentType, targetType, Expression.allocationType, WordArray.word])
  have frame := (run_storage state source target length initial).2.2.2.2 parent.allocation separate
  refine ⟨frame.trans parentFound, represented.1, ?_⟩
  intro index inside
  exact (load_eq_of_lookup state _ true false WordArray.word (parent.address index) frame).trans (represented.2 index inside)

end Compiler.Extraction.RepresentativeArray.Copy
