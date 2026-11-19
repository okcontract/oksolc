/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayCopy

namespace Compiler.Extraction.RepresentativeArray.Copy
open Compiler.ZigAir.Memory

theorem slot_offsets_apart (left right first second : Nat) (readType writeType : Ty)
    (readSlot : (first, readType) ∈ expressionSlots) (writeSlot : (second, writeType) ∈ expressionSlots)
    (apart : left ≠ right ∨ first ≠ second) (position entry : Nat)
    (readPosition : position ∈ readType.readOffsets (left * 32 + first))
    (writePosition : entry ∈ writeType.readOffsets (right * 32 + second)) : position ≠ entry := by
  simp only [expressionSlots, Expression.allocationType, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, Field.type, Prod.mk.injEq] at readSlot writeSlot
  rcases readSlot with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rcases writeSlot with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp only [Ty.readOffsets, List.mem_cons, List.not_mem_nil, or_false] at readPosition writePosition
  all_goals omega

/-- Field reads preserve their exact result outside the stored leaves, including
uninitialized and invalid reads. The complete nominal selector is retained. -/
theorem readField_after_store (state after : State) (writeType readType : Ty) (writeAddress readAddress : Address)
    (offset : Nat) (value : Value)
    (declared : fieldType Expression.allocationType offset = some readType)
    (stored : store state (.pointer (.pointer true false writeType) writeAddress) value = .ok after)
    (apart : readAddress.allocation ≠ writeAddress.allocation ∨
      ∀ position ∈ readType.readOffsets (readAddress.offset + offset),
        ∀ entry ∈ value.leaves writeAddress.offset, position ≠ entry.1) :
    Expression.readField after false readAddress offset = Expression.readField state false readAddress offset := by
  have selector := fieldPointer_after_store state after _ value false false Expression.allocationType readAddress offset stored
  unfold Expression.readField
  rw [selector]
  cases selected : fieldPointer state (.pointer (.pointer false false Expression.allocationType) readAddress) offset with
  | error fault => rfl
  | ok pointer =>
    obtain ⟨field, shaped, rfl⟩ := fieldPointer_address state false false Expression.allocationType readAddress offset pointer selected
    have same : field = readType := Option.some.inj (shaped.symm.trans declared)
    subst field
    dsimp only [bind, Except.bind]
    by_cases same : readAddress.allocation = writeAddress.allocation
    · rcases apart with impossible | apart
      · contradiction
      · have framed := load_disjoint_after_store state true false writeType writeAddress value after false false readType
          (readAddress.offset + offset) stored apart
        simpa only [same] using framed
    · exact load_other_after_store state true false writeType writeAddress value after false false readType
        ⟨readAddress.allocation, readAddress.offset + offset⟩ stored same

/-- Writes to another descriptor or another captured field preserve this field.
The slice's pointer and length leaves are both included in the separation check. -/
theorem readField_after_slot_store (state after : State) (source target index other offset fieldOffset : Nat)
    (readType writeType : Ty) (value : Value)
    (readSlot : (fieldOffset, readType) ∈ expressionSlots) (writeSlot : (offset, writeType) ∈ expressionSlots)
    (stored : store state (.pointer (.pointer true false writeType) ⟨target, index * 32 + offset⟩) value = .ok after)
    (apart : source ≠ target ∨ other ≠ index ∨ fieldOffset ≠ offset) :
    Expression.readField after false ⟨source, other * 32⟩ fieldOffset =
      Expression.readField state false ⟨source, other * 32⟩ fieldOffset := by
  apply readField_after_store state after writeType readType ⟨target, index * 32 + offset⟩ ⟨source, other * 32⟩
    fieldOffset value (slot_declared _ _ readSlot) stored
  rcases apart with separate | apart
  · exact Or.inl separate
  · refine Or.inr ?_
    intro position readPosition entry present
    obtain ⟨_, _, _, _, _, _, pointer, typed, _⟩ := store_success state _ value after stored
    cases pointer
    simp only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] at typed
    have leafPosition : entry.1 ∈ (value.leaves (index * 32 + offset)).map Prod.fst :=
      List.mem_map.mpr ⟨entry, present, rfl⟩
    rw [Value.leaf_offsets value (index * 32 + offset) typed.2, typed.1] at leafPosition
    exact slot_offsets_apart other index fieldOffset offset readType writeType readSlot writeSlot apart
      position entry.1 readPosition leafPosition

/-- Every prefix, including a rejected copy, keeps unrelated field observations. -/
theorem fields_read_frame (slots : List (Nat × Ty)) (source : Address) (target index otherLifetime otherIndex offset : Nat)
    (type : Ty) (state : State) (readSlot : (offset, type) ∈ expressionSlots)
    (declared : ∀ slot ∈ slots, slot ∈ expressionSlots)
    (apart : ∀ slot ∈ slots, otherLifetime ≠ target ∨ otherIndex ≠ index ∨ offset ≠ slot.1) :
    Expression.readField (fields slots source ⟨target, index * 32⟩ state).2 false ⟨otherLifetime, otherIndex * 32⟩ offset =
      Expression.readField state false ⟨otherLifetime, otherIndex * 32⟩ offset := by
  induction slots generalizing state with
  | nil => rfl
  | cons slot tail ih =>
    rcases slot with ⟨fieldOffset, fieldType⟩
    simp only [fields]
    cases loaded : Expression.readField state false source fieldOffset with
    | error fault => rfl
    | ok value =>
      dsimp only
      cases stored : store state (.pointer (.pointer true false fieldType) ⟨target, index * 32 + fieldOffset⟩) value with
      | error fault => rfl
      | ok middle =>
        exact (ih middle (fun slot member => declared slot (List.mem_cons_of_mem _ member))
          (fun slot member => apart slot (List.mem_cons_of_mem _ member))).trans
          (readField_after_slot_store state middle otherLifetime target index otherIndex fieldOffset offset type fieldType value
            readSlot (declared (fieldOffset, fieldType) (by simp)) stored (apart (fieldOffset, fieldType) (by simp)))

theorem copyFrom_read_frame (source target remaining index otherLifetime otherIndex offset : Nat) (type : Ty)
    (state : State) (readSlot : (offset, type) ∈ expressionSlots)
    (apart : otherLifetime ≠ target ∨ otherIndex < index ∨ index + remaining ≤ otherIndex) :
    Expression.readField (copyFrom source target remaining index state).2 false ⟨otherLifetime, otherIndex * 32⟩ offset =
      Expression.readField state false ⟨otherLifetime, otherIndex * 32⟩ offset := by
  induction remaining generalizing index state with
  | zero => rfl
  | succ remaining ih =>
    have first := fields_read_frame expressionSlots ⟨source, index * 32⟩ target index otherLifetime otherIndex offset type
      state readSlot (fun _ member => member) (fun _ _ => by
        rcases apart with separate | before | after
        · exact Or.inl separate
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inl (by omega)))
    cases executed : fields expressionSlots ⟨source, index * 32⟩ ⟨target, index * 32⟩ state with
    | mk result middle =>
      rw [executed] at first
      simp only [copyFrom, executed]
      cases result with
      | error fault => exact first
      | ok value =>
        have tailApart : otherLifetime ≠ target ∨ otherIndex < index + 1 ∨ index + 1 + remaining ≤ otherIndex := by
          rcases apart with separate | other
          · exact Or.inl separate
          · exact Or.inr (by omega)
        exact (ih (index + 1) middle tailApart).trans first

/-- Captured fields outside the copied prefix retain their exact result on
success and fault, including uninitialized spare descriptor fields. -/
theorem run_read_frame (state : State) (source target length otherLifetime otherIndex offset : Nat) (type : Ty)
    (readSlot : (offset, type) ∈ expressionSlots)
    (apart : otherLifetime ≠ target ∨ length ≤ otherIndex) :
    Expression.readField (run state source target length).2 false ⟨otherLifetime, otherIndex * 32⟩ offset =
      Expression.readField state false ⟨otherLifetime, otherIndex * 32⟩ offset := by
  unfold run
  split
  · rfl
  · split
    · rfl
    · exact copyFrom_read_frame source target length 0 otherLifetime otherIndex offset type state readSlot
        (apart.elim Or.inl (fun outside => Or.inr (Or.inr (by omega))))

end Compiler.Extraction.RepresentativeArray.Copy
