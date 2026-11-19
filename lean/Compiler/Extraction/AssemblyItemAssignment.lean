/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemMembers

namespace Compiler.Extraction.AssemblyItem.Fields
open Compiler.ZigAir.Memory

/-- The complete evaluated right-hand side, indexed by the existing immutable
member selectors. This is a register value, not another heap or native layout. -/
abbrev Values := Member → Value

def Values.Typed (values : Values) : Prop := ∀ selected, (values selected).hasType selected.type = true

theorem item_record_valid :
    (match viewType with | .aggregate _ layout fields => Ty.aggregateValid layout fields | _ => false) = true := by decide
theorem debug_record_valid :
    (match debugDataType with | .aggregate _ layout fields => Ty.aggregateValid layout fields | _ => false) = true := by decide
theorem location_record_valid :
    (match sourceLocationType with | .aggregate _ layout fields => Ty.aggregateValid layout fields | _ => false) = true := by decide

def locationValue (values : Values) (origin : Bool) : ObjectValue := .fields [
  (source_location_source_nameOffset, .leaf (values (if origin then .originSource else .nativeSource))),
  (source_location_startOffset, .leaf (values (if origin then .originStart else .nativeStart))),
  (source_location_endOffset, .leaf (values (if origin then .originEnd else .nativeEnd)))]

def debugValue (values : Values) : ObjectValue := .fields [
  (debug_data_native_locationOffset, locationValue values false),
  (debug_data_origin_locationOffset, locationValue values true),
  (debug_data_ast_idOffset, .leaf (values .astId))]

/-- Reify the evaluated members in the existing complete record vocabulary.
Nested geometry and physical ordering come from the captured declaration. -/
def objectValue (values : Values) : ObjectValue := .fields [
  (data_valueOffset, .leaf (values .data)), (pushed_valueOffset, .leaf (values .pushed)),
  (verbatimOffset, .leaf (values .verbatim)), (debug_dataOffset, debugValue values),
  (immutable_occurrencesOffset, .leaf (values .immutable)), (modifier_depthOffset, .leaf (values .modifier)),
  (item_typeOffset, .leaf (values .kind)), (jump_typeOffset, .leaf (values .jump)),
  (instruction_valueOffset, .leaf (values .instruction))]

theorem objectValue_typed (values : Values) :
    (objectValue values).hasType viewType = true ↔ values.Typed := by
  have itemGeometry := item_record_valid
  have debugGeometry := debug_record_valid
  have locationGeometry := location_record_valid
  dsimp only [viewType, debugDataType, sourceLocationType] at itemGeometry debugGeometry locationGeometry
  simp [objectValue, debugValue, locationValue, viewType, debugDataType, sourceLocationType,
    ObjectValue.hasType, objectFieldsTyped, Field.type, itemGeometry, debugGeometry, locationGeometry,
    data_valueOffset, pushed_valueOffset, verbatimOffset, debug_dataOffset, immutable_occurrencesOffset,
    modifier_depthOffset, item_typeOffset, jump_typeOffset, instruction_valueOffset,
    debug_data_native_locationOffset, debug_data_origin_locationOffset, debug_data_ast_idOffset,
    source_location_source_nameOffset, source_location_startOffset, source_location_endOffset]
  constructor
  · intro all selected
    have complete : ∀ field, (values field).type = field.type ∧ (values field).valid = true := by
      rcases all with ⟨data, pushed, verbatim, ⟨⟨nativeSource, nativeStart, nativeEnd⟩,
        ⟨originSource, originStart, originEnd⟩, astId⟩, immutable, modifier, kind, jump, instruction⟩
      intro field
      cases field <;> assumption
    simpa only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] using complete selected
  · intro all
    have complete (field : Member) : (values field).type = field.type ∧ (values field).valid = true := by
      simpa only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] using all field
    exact ⟨complete .data, complete .pushed, complete .verbatim,
      ⟨⟨complete .nativeSource, complete .nativeStart, complete .nativeEnd⟩,
        ⟨complete .originSource, complete .originStart, complete .originEnd⟩, complete .astId⟩,
      complete .immutable, complete .modifier, complete .kind, complete .jump, complete .instruction⟩

def members : List Member := [.kind, .instruction, .data, .verbatim, .pushed, .immutable, .modifier, .jump,
  .nativeStart, .nativeEnd, .nativeSource, .originStart, .originEnd, .originSource, .astId]

theorem members_complete (selected : Member) : selected ∈ members := by cases selected <;> decide
theorem members_unique : members.Nodup := by decide

theorem Member.offset_injective (left right : Member) (same : left.offset = right.offset) : left = right := by
  cases left <;> cases right <;> first | rfl | contradiction

theorem Member.read_offsets (selected : Member) : selected.type.readOffsets selected.offset = [selected.offset] := by
  cases selected <;> rfl

/-- A checked store frames every other captured atomic member. Complete owner
geometry is retained, and the shared leaf-level frame rule checks disjointness. -/
theorem member_store_frame (state after : State) (id : Nat) (cell : Allocation) (written selected : Member)
    (value : Value) (valueTyped : value.hasType written.type = true)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType)
    (stored : store state (.pointer (.pointer true false written.type) ⟨id, written.offset⟩) value = .ok after)
    (apart : selected ≠ written) : member after ⟨id, 0⟩ selected = member state ⟨id, 0⟩ selected := by
  obtain ⟨valueType, valueValid⟩ := (by simpa only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] using valueTyped :
    value.type = written.type ∧ value.valid = true)
  obtain ⟨finalCell, finalFound, shape⟩ := store_retains_shape state _ value after stored id cell found
  have finalValid := store_preserves_valid state _ value after valid stored
  rw [member, member, readTyped_from_root after id selected.offset finalCell selected.type finalValid finalFound
    (shape.2.1.trans typed), readTyped_from_root state id selected.offset cell selected.type valid found typed]
  apply load_disjoint_after_store state true false written.type ⟨id, written.offset⟩ value after false false
    selected.type selected.offset stored
  intro position positionMember entry entryMember
  rw [selected.read_offsets, List.mem_singleton] at positionMember
  rw [Value.leaves_shift, value.leaves_atomic valueValid (valueType ▸ written.geometry.atomic)] at entryMember
  simp only [List.map_cons, List.map_nil, List.mem_singleton] at entryMember
  subst position; subst entry
  simp only [Nat.add_zero]
  exact fun same => apart (Member.offset_injective selected written same)

/-- A native aggregate assignment has no intervening external effects. This
sequence realizes its complete typed-field effect; under initial geometry and
typed values every store succeeds. Rejected memory is an admission fault. -/
def writeMembers (values : Values) (id : Nat) : List Member → State → Except Fault State
  | [], state => .ok state
  | selected :: rest, state => do
    let after ← store state (.pointer (.pointer true false selected.type) ⟨id, selected.offset⟩) (values selected)
    writeMembers values id rest after

structure Written (values : Values) (id : Nat) (selected : List Member) (before after : State) : Prop where
  valid : after.valid = true
  shape : before.heap.RetainsShape after.heap
  reads : ∀ field, member after ⟨id, 0⟩ field =
    if field ∈ selected then .ok (values field) else member before ⟨id, 0⟩ field
  frame : ∀ other, other ≠ id → after.heap.lookup other = before.heap.lookup other
  nextId : after.nextId = before.nextId
  nextAddress : after.nextAddress = before.nextAddress

theorem writeMembers_total (values : Values) (id : Nat) (selected : List Member) (state : State) (cell : Allocation)
    (valuesTyped : values.Typed) (valid : state.valid = true) (found : state.heap.lookup id = some cell)
    (typed : cell.type = viewType) (writable : cell.writable = true) :
    ∃ after, writeMembers values id selected state = .ok after ∧ Written values id selected state after := by
  induction selected generalizing state cell with
  | nil => exact ⟨state, rfl, valid, Heap.RetainsShape.refl _, by simp, by simp, rfl, rfl⟩
  | cons selected rest ih =>
    obtain ⟨middle, stored, middleValid, loaded⟩ := member_store state id cell selected (values selected)
      (valuesTyped selected) valid found typed writable
    have shape := store_retains_shape state _ _ middle stored
    obtain ⟨middleCell, middleFound, middleShape⟩ := shape id cell found
    obtain ⟨after, tail, post⟩ := ih middle middleCell middleValid middleFound
      (middleShape.2.1.trans typed) (middleShape.2.2.1.trans writable)
    refine ⟨after, by simp only [writeMembers, stored, bind, Except.bind, tail], post.valid,
      shape.trans post.shape, ?_, ?_, ?_, ?_⟩
    · intro field
      rw [post.reads]
      by_cases inside : field ∈ rest
      · simp [inside]
      · by_cases same : field = selected
        · subst field; simpa [inside] using loaded
        · simpa [inside, same] using member_store_frame state middle id cell selected field (values selected)
            (valuesTyped selected) valid found typed stored same
    · intro other apart
      exact (post.frame other apart).trans
        (heap_after_store_other state true false selected.type ⟨id, selected.offset⟩ _ middle stored other apart)
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := store_success state _ _ middle stored
      exact post.nextId
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := store_success state _ _ middle stored
      exact post.nextAddress

/-- Validate the complete evaluated value and nominal owner before materializing
the assignment. These are model-admission checks, not added native branches. -/
def assign (values : Values) (id : Nat) (state : State) : Except Fault State := do
  if !(members.all fun selected => (values selected).hasType selected.type) then .error .malformed else
  let _ ← recordView state viewType (.pointer (.pointer true false allocationType) ⟨id, 0⟩)
  writeMembers values id members state

theorem assign_total (values : Values) (id : Nat) (state : State) (cell : Allocation)
    (valuesTyped : values.Typed) (valid : state.valid = true) (found : state.heap.lookup id = some cell)
    (typed : cell.type = viewType) (writable : cell.writable = true) :
    ∃ after, assign values id state = .ok after ∧ Written values id members state after ∧
      ∀ selected, member after ⟨id, 0⟩ selected = .ok (values selected) := by
  obtain ⟨after, assigned, post⟩ := writeMembers_total values id members state cell valuesTyped valid found typed writable
  have checked : (members.all fun selected => (values selected).hasType selected.type) = true := by
    simp only [List.all_eq_true]
    exact fun selected _ => valuesTyped selected
  refine ⟨after, ?_, post, fun selected => by simpa only [members_complete, if_true] using post.reads selected⟩
  simp only [assign, checked, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    root_view state id cell true valid found typed, bind, Except.bind, assigned]

/-- Complete item writes preserve the existing ownership registry and all
represented argument buffers. Array/item separation follows from registry
types, rather than a caller-supplied disjointness assumption. -/
theorem Written.session (values : Values) (allocator id : Nat) (selected : List Member)
    (before : Compiler.Extraction.Memory.Arguments.Normalization.Session σ) (after : State)
    (post : Written values id selected before.memory after)
    (valid : Compiler.Extraction.Memory.Arguments.Normalization.Valid before) (owned : Owned allocator id before) :
    Compiler.Extraction.Memory.Arguments.Normalization.Valid { before with memory := after } ∧
      Owned allocator id { before with memory := after } :=
  session_frame allocator id before after post.valid post.shape post.frame valid owned

end Compiler.Extraction.AssemblyItem.Fields
