/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemCreation
import Compiler.ZigAir.MemoryRecordViews
import Compiler.ZigAir.MemoryRecordWrites
import Compiler.ZigAir.MemoryOptionalScalar

namespace Compiler.Extraction.AssemblyItem.Fields
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

theorem scalar_fields_checked :
    fieldType viewType item_typeOffset = some (.scalar (.int true 32)) ∧
    fieldType viewType jump_typeOffset = some (.scalar (.int true 32)) ∧
    fieldType viewType data_valueOffset = some (.scalar (.int false 256)) ∧
    fieldType viewType modifier_depthOffset = some usize := by decide

/-- Resolve the existing nominal item pointer against the complete declaration.
This checks provenance/geometry only and cannot initialize any field. -/
theorem root_view (state : State) (id : Nat) (cell : Allocation) (writable : Bool)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType) :
    recordView state viewType (.pointer (.pointer writable false allocationType) ⟨id, 0⟩) =
      .ok (.pointer (.pointer writable false viewType) ⟨id, 0⟩) :=
  recordView_root state id cell _ _ _ writable false valid found typed Creation.view_layout_captured (by decide)

theorem root_field (state : State) (id offset : Nat) (cell : Allocation) (type : Ty) (writable : Bool)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType)
    (declared : fieldType viewType offset = some type) :
    fieldPointer state (.pointer (.pointer writable false viewType) ⟨id, 0⟩) offset =
      .ok (.pointer (.pointer writable false type) ⟨id, offset⟩) :=
  root_fieldPointer state id cell viewType type Creation.layout offset writable false valid found typed
    Creation.view_layout_captured (by decide) declared

/-- Use the same native nominal pointer, allocation lifetime and field offset.
An offset at the start of a nested object selects that whole object; use
`readTyped` when the native member path selects a leaf at the same offset. -/
def read (state : State) (address : Address) (offset : Nat) : Except Fault Value := do
  let item ← recordView state viewType (.pointer (.pointer false false allocationType) address)
  let field ← fieldPointer state item offset
  load state field

/-- Exact typed subobject selection follows the same complete declaration walk
as every load. This retains nested leaves at an enclosing object's offset zero;
it grants no view into an optional's payload bytes. -/
def readTyped (state : State) (address : Address) (offset : Nat) (type : Ty) : Except Fault Value := do
  let .pointer _ root ← recordView state viewType (.pointer (.pointer false false allocationType) address)
    | .error .malformed
  load state (.pointer (.pointer false false type) { root with offset := root.offset + offset })

theorem view_frame (before after : State) (address : Address)
    (same : after.heap.lookup address.allocation = before.heap.lookup address.allocation) :
    recordView after viewType (.pointer (.pointer false false allocationType) address) =
      recordView before viewType (.pointer (.pointer false false allocationType) address) := by
  simp only [recordView, allocationType, viewType, access, same]

theorem read_frame (before after : State) (address : Address) (offset : Nat)
    (same : after.heap.lookup address.allocation = before.heap.lookup address.allocation) :
    read after address offset = read before address offset := by
  have viewed := view_frame before after address same
  cases called : recordView before viewType (.pointer (.pointer false false allocationType) address) with
  | error fault => simp only [read, viewed, called, bind, Except.bind]
  | ok result =>
    have resultAddress := recordView_address before viewType false false _ _ address result called
    subst result
    have fieldFrame := fieldPointer_eq_of_lookup before after false false viewType address offset same
    cases selected : fieldPointer before (.pointer (.pointer false false viewType) address) offset with
    | error fault => simp only [read, viewed, called, fieldFrame, selected, bind, Except.bind]
    | ok field =>
      obtain ⟨type, _, rfl⟩ := fieldPointer_address before false false viewType address offset field selected
      simp only [read, viewed, called, fieldFrame, selected, bind, Except.bind]
      exact load_eq_of_lookup before after false false type _ same

theorem readTyped_parts (state : State) (address : Address) (offset : Nat) (type : Ty) (value : Value)
    (read : readTyped state address offset type = .ok value) :
    recordView state viewType (.pointer (.pointer false false allocationType) address) =
      .ok (.pointer (.pointer false false viewType) address) ∧
    load state (.pointer (.pointer false false type) { address with offset := address.offset + offset }) = .ok value := by
  cases viewed : recordView state viewType (.pointer (.pointer false false allocationType) address) with
  | error fault => simp [readTyped, viewed, bind, Except.bind] at read
  | ok result =>
    have same := recordView_address state viewType false false _ _ address result viewed
    subst result
    exact ⟨rfl, by simpa only [readTyped, viewed, bind, Except.bind] using read⟩

theorem readTyped_typed (state : State) (address : Address) (offset : Nat) (type : Ty) (value : Value)
    (read : readTyped state address offset type = .ok value) : value.hasType type = true :=
  load_hasType state false false type _ value (readTyped_parts state address offset type value read).2

theorem readTyped_frame (before after : State) (address : Address) (offset : Nat) (type : Ty)
    (same : after.heap.lookup address.allocation = before.heap.lookup address.allocation) :
    readTyped after address offset type = readTyped before address offset type := by
  have viewed := view_frame before after address same
  cases called : recordView before viewType (.pointer (.pointer false false allocationType) address) with
  | error fault => simp only [readTyped, viewed, called, bind, Except.bind]
  | ok result =>
    have resultAddress := recordView_address before viewType false false _ _ address result called
    subst result
    simp only [readTyped, viewed, called, bind, Except.bind]
    exact load_eq_of_lookup before after false false type _ same

/-- Invalid enum representations reject the typed model; this is not an added
native branch or a recoverable Zig error. The domain is the captured enum. -/
def tag (state : State) (address : Address) (offset : Nat) (values : List Int) : Except Fault Int := do
  let .scalar (.int true 32 value) ← read state address offset | .error .malformed
  if value ∈ values then .ok value else .error .malformed

def kind (state : State) (address : Address) := tag state address item_typeOffset itemTagValues
def jump (state : State) (address : Address) := tag state address jump_typeOffset jumpTagValues

theorem instruction_field_checked : fieldType viewType instruction_valueOffset = some OptionalScalar.byte := by decide

/-- The three captured optional scalar fields share one checked store rule.
Verbatim and debug data are outside this vocabulary. -/
inductive OptionalField where
  | instruction | pushed | immutable
  deriving DecidableEq, Repr

def OptionalField.bits : OptionalField → Nat
  | .instruction => 8 | .pushed => 256 | .immutable => 64
def OptionalField.offset : OptionalField → Nat
  | .instruction => instruction_valueOffset | .pushed => pushed_valueOffset | .immutable => immutable_occurrencesOffset
def OptionalField.layout : OptionalField → Layout
  | .instruction => ⟨2, 1⟩ | .pushed => ⟨48, 16⟩ | .immutable => ⟨16, 8⟩

def optional (state : State) (address : Address) (field : OptionalField) : Except Fault (Option (BitVec field.bits)) := do
  let value ← read state address field.offset
  OptionalScalar.unsignedPayload field.bits value

/-- Preserve None for the source caller's conditional unwrap. Unsupported,
uninitialized and malformed reads remain distinct memory rejections. -/
def instruction (state : State) (address : Address) : Except Fault (Option (BitVec 8)) :=
  optional state address .instruction

theorem optional_fields_checked (field : OptionalField) :
    fieldType viewType field.offset = some (OptionalScalar.unsigned field.bits) ∧
    leafType viewType field.offset = some (OptionalScalar.unsigned field.bits) ∧
    (OptionalScalar.unsigned field.bits).layout = some field.layout ∧
    0 < field.layout.bytes ∧ field.offset + field.layout.bytes ≤ Creation.layout.bytes ∧
    field.offset % field.layout.alignment = 0 ∧ Creation.layout.alignment % field.layout.alignment = 0 := by
  cases field <;> decide

theorem read_from_root (state : State) (id offset : Nat) (cell : Allocation) (type : Ty)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType)
    (declared : fieldType viewType offset = some type) :
    read state ⟨id, 0⟩ offset = load state (.pointer (.pointer false false type) ⟨id, offset⟩) := by
  simp only [read, root_view state id cell false valid found typed,
    root_field state id offset cell type false valid found typed declared, bind, Except.bind]

/-- Readback follows from the actual checked store. No final field value or
successful reader is a premise; shape retention supplies the reached view. -/
theorem read_after_store (state after : State) (id offset : Nat) (cell : Allocation) (type : Ty) (value : Value)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType)
    (declared : fieldType viewType offset = some type)
    (stored : store state (.pointer (.pointer true false type) ⟨id, offset⟩) value = .ok after) :
    read after ⟨id, 0⟩ offset = .ok value := by
  obtain ⟨finalCell, finalFound, shape⟩ := store_retains_shape state _ value after stored id cell found
  have finalTyped := shape.2.1.trans typed
  have finalValid := store_preserves_valid state _ value after valid stored
  rw [read_from_root after id offset finalCell type finalValid finalFound finalTyped declared]
  exact load_alias_after_store state true false type ⟨id, offset⟩ value after false false stored

theorem instruction_after_store (state after : State) (id : Nat) (cell : Allocation) (payload : Option (BitVec 8))
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType)
    (stored : store state (.pointer (.pointer true false OptionalScalar.byte) ⟨id, instruction_valueOffset⟩)
      (OptionalScalar.byteValue payload) = .ok after) :
    instruction after ⟨id, 0⟩ = .ok payload := by
  rw [instruction, optional, OptionalField.offset, read_after_store state after id instruction_valueOffset cell OptionalScalar.byte
    (OptionalScalar.byteValue payload) valid found typed instruction_field_checked stored]
  exact OptionalScalar.bytePayload_value payload

structure LeafGeometry (offset : Nat) (type : Ty) (layout : Layout) : Prop where
  view : acceptsView viewType offset type = true
  leaf : leafType viewType offset = some type
  atomic : leafType type 0 = some type
  shaped : type.layout = some layout
  positive : 0 < layout.bytes
  inside : offset + layout.bytes ≤ Creation.layout.bytes
  aligned : offset % layout.alignment = 0
  divided : Creation.layout.alignment % layout.alignment = 0

theorem readTyped_from_root (state : State) (id offset : Nat) (cell : Allocation) (type : Ty)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType) :
    readTyped state ⟨id, 0⟩ offset type = load state (.pointer (.pointer false false type) ⟨id, offset⟩) := by
  simp only [readTyped, root_view state id cell false valid found typed, bind, Except.bind, Nat.zero_add]

/-- One store derivation for every captured atomic item member, including
nested leaves. Geometry is checked from the declaration, not final contents. -/
theorem leaf_store (state : State) (id : Nat) (cell : Allocation) (offset : Nat) (type : Ty) (layout : Layout)
    (value : Value) (geometry : LeafGeometry offset type layout) (valueTyped : value.hasType type = true)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType)
    (writable : cell.writable = true) :
    ∃ after, store state (.pointer (.pointer true false type) ⟨id, offset⟩) value = .ok after ∧ after.valid = true ∧
      readTyped after ⟨id, 0⟩ offset type = .ok value := by
  obtain ⟨valueType, valueValid⟩ := (by simpa only [Value.hasType, Bool.and_eq_true, decide_eq_true_eq] using valueTyped :
    value.type = type ∧ value.valid = true)
  have parent := root_access state id cell Creation.layout true valid found (typed ▸ Creation.view_layout_captured)
    (by decide) (fun _ => writable)
  have accessed := access_subregion state ⟨id, 0⟩ Creation.layout layout offset true cell parent
    geometry.positive geometry.inside geometry.aligned geometry.divided
  simp only [Nat.zero_add] at accessed
  have view : acceptsView cell.type offset value.type = true := by rw [typed, valueType]; exact geometry.view
  have leaves : ∀ entry ∈ value.leaves 0, leafType cell.type (offset + entry.1) = some entry.2.type := by
    intro entry member
    rw [value.leaves_atomic valueValid (valueType ▸ geometry.atomic), List.mem_singleton] at member
    subst entry
    simpa only [Nat.add_zero, typed, valueType] using geometry.leaf
  obtain ⟨after, stored⟩ := store_subobject_total state ⟨id, offset⟩ layout cell value valueValid
    (valueType ▸ geometry.shaped) accessed view leaves
  rw [valueType] at stored
  have finalValid := store_preserves_valid state _ value after valid stored
  obtain ⟨finalCell, finalFound, shape⟩ := store_retains_shape state _ value after stored id cell found
  refine ⟨after, stored, finalValid, ?_⟩
  rw [readTyped_from_root after id offset finalCell type finalValid finalFound (shape.2.1.trans typed)]
  exact load_alias_after_store state true false type ⟨id, offset⟩ value after false false stored

/-- Initial complete writable geometry and an evaluated optional derive the
actual store and exact readback. No initialized field or successful store is
assumed. This initializes one selected field, not the complete native item. -/
theorem optional_store (state : State) (id : Nat) (cell : Allocation) (field : OptionalField)
    (payload : Option (BitVec field.bits))
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType)
    (writable : cell.writable = true) :
    ∃ after, store state (.pointer (.pointer true false (OptionalScalar.unsigned field.bits)) ⟨id, field.offset⟩)
      (OptionalScalar.unsignedValue field.bits payload) = .ok after ∧ after.valid = true ∧
      optional after ⟨id, 0⟩ field = .ok payload := by
  have geometry : LeafGeometry field.offset (OptionalScalar.unsigned field.bits) field.layout := by
    cases field <;> constructor <;> decide
  obtain ⟨after, stored, finalValid, _⟩ := leaf_store state id cell field.offset (OptionalScalar.unsigned field.bits)
    field.layout (OptionalScalar.unsignedValue field.bits payload) geometry (OptionalScalar.unsignedValue_typed field.bits payload)
    valid found typed writable
  refine ⟨after, stored, finalValid, ?_⟩
  have declared := (optional_fields_checked field).1
  rw [optional, read_after_store state after id field.offset cell _ _ valid found typed declared stored]
  exact OptionalScalar.unsignedPayload_value field.bits payload

theorem instruction_store (state : State) (id : Nat) (cell : Allocation) (payload : Option (BitVec 8))
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType)
    (writable : cell.writable = true) :
    ∃ after, store state (.pointer (.pointer true false OptionalScalar.byte) ⟨id, instruction_valueOffset⟩)
      (OptionalScalar.byteValue payload) = .ok after ∧ after.valid = true ∧ instruction after ⟨id, 0⟩ = .ok payload :=
  optional_store state id cell .instruction payload valid found typed writable

theorem tag_of_read (state : State) (address : Address) (offset : Nat) (values : List Int) (value : Int)
    (loaded : read state address offset = .ok (.scalar (.int true 32 value))) :
    tag state address offset values = if value ∈ values then .ok value else .error .malformed := by
  simp only [tag, loaded, bind, Except.bind]

end Compiler.Extraction.AssemblyItem.Fields
