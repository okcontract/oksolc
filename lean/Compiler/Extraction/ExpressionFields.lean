/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionLayout
import Compiler.Extraction.AssemblyItemLayout
import Compiler.ZigAir.MemoryRecordFields

namespace Compiler.Extraction.Expression
open Compiler.ZigAir.Memory

/-- These types and offsets are checked against every native Expression field.
The item pointer targets the existing admitted item allocation type. Its payload
and the representative container's native correspondence remain separate work. -/
def itemType : Ty := .pointer true false Compiler.Extraction.AssemblyItem.allocationType
def argumentsType : Ty := .slice true (.scalar (.int false 32))
def idType : Ty := .scalar (.int false 32)

theorem layout_checked : allocationType.layout = some ⟨32, 8⟩ := by decide

theorem field_types_checked :
    fieldType allocationType itemOffset = some itemType ∧
    fieldType allocationType argumentsOffset = some argumentsType ∧
    fieldType allocationType idOffset = some idType ∧
    fieldType allocationType sequence_numberOffset = some idType := by decide

/-- Project a captured descriptor field using the existing typed heap. No
logical node, fresh buffer, default value or query observation is manufactured. -/
def readField (state : State) (writable : Bool) (descriptor : Address) (offset : Nat) : Except Fault Value := do
  let field ← fieldPointer state (.pointer (.pointer writable false allocationType) descriptor) offset
  load state field

theorem readField_frame (before after : State) (writable : Bool) (descriptor : Address) (offset : Nat)
    (same : after.heap.lookup descriptor.allocation = before.heap.lookup descriptor.allocation) :
    readField after writable descriptor offset = readField before writable descriptor offset := by
  have selected := fieldPointer_eq_of_lookup before after writable false allocationType descriptor offset same
  cases called : fieldPointer before (.pointer (.pointer writable false allocationType) descriptor) offset with
  | error fault => simp only [readField, selected, called, bind, Except.bind]
  | ok pointer =>
    obtain ⟨field, _, rfl⟩ := fieldPointer_address before writable false allocationType descriptor offset pointer called
    simp only [readField, selected, called, bind, Except.bind]
    exact load_eq_of_lookup before after writable false field _ same

def readFields (state : State) (writable : Bool) (descriptor : Address) : Except Fault (List Value) := do
  let item ← readField state writable descriptor itemOffset
  let arguments ← readField state writable descriptor argumentsOffset
  let id ← readField state writable descriptor idOffset
  let sequence ← readField state writable descriptor sequence_numberOffset
  .ok [item, arguments, id, sequence]

/-- A complete read exposes each actual field read in source order. This does
not infer pointee contents or ownership from a stored pointer. -/
theorem readFields_parts (state : State) (writable : Bool) (descriptor : Address) (item arguments id sequence : Value)
    (read : readFields state writable descriptor = .ok [item, arguments, id, sequence]) :
    readField state writable descriptor itemOffset = .ok item ∧
      readField state writable descriptor argumentsOffset = .ok arguments ∧
      readField state writable descriptor idOffset = .ok id ∧
      readField state writable descriptor sequence_numberOffset = .ok sequence := by
  cases first : readField state writable descriptor itemOffset with
  | error fault => simp only [readFields, first, bind, Except.bind, reduceCtorEq] at read
  | ok actualItem =>
    cases second : readField state writable descriptor argumentsOffset with
    | error fault => simp only [readFields, first, second, bind, Except.bind, reduceCtorEq] at read
    | ok actualArguments =>
      cases third : readField state writable descriptor idOffset with
      | error fault => simp only [readFields, first, second, third, bind, Except.bind, reduceCtorEq] at read
      | ok actualId =>
        cases fourth : readField state writable descriptor sequence_numberOffset with
        | error fault => simp only [readFields, first, second, third, fourth, bind, Except.bind, reduceCtorEq] at read
        | ok actualSequence =>
          simp only [readFields, first, second, third, fourth, bind, Except.bind, Except.ok.injEq, List.cons.injEq,
            and_true] at read
          rcases read with ⟨rfl, rfl, rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl⟩

theorem root_selector (state : State) (id : Nat) (cell : Allocation) (offset : Nat) (field : Ty)
    (writable : Bool) (initial : state.valid = true) (found : state.heap.lookup id = some cell)
    (typed : cell.type = allocationType) (selected : fieldType allocationType offset = some field) :
    fieldPointer state (.pointer (.pointer writable false allocationType) ⟨id, 0⟩) offset =
      .ok (.pointer (.pointer writable false field) ⟨id, offset⟩) :=
  root_fieldPointer state id cell allocationType field ⟨32, 8⟩ offset writable false
    initial found typed layout_checked (by decide) selected

/-- Read a field after its actual store. Selection and readback are derived
through the checked memory operations; final initialization is not a premise. -/
theorem read_after_store (state after : State) (writable : Bool) (descriptor : Address)
    (offset : Nat) (pointer value : Value)
    (selected : fieldPointer state (.pointer (.pointer writable false allocationType) descriptor) offset = .ok pointer)
    (stored : store state pointer value = .ok after) :
    readField after writable descriptor offset = .ok value :=
  field_load_after_store state after writable false allocationType descriptor offset pointer value selected stored

/-- A live descriptor's payload reads follow the exact allocation/offset view;
copying the descriptor does not change the argument slice's allocation identity. -/
theorem read_from_root (state : State) (id : Nat) (cell : Allocation) (offset : Nat) (field : Ty)
    (writable : Bool) (initial : state.valid = true) (found : state.heap.lookup id = some cell)
    (typed : cell.type = allocationType) (selected : fieldType allocationType offset = some field) :
    readField state writable ⟨id, 0⟩ offset = load state (.pointer (.pointer writable false field) ⟨id, offset⟩) := by
  simp only [readField, root_selector state id cell offset field writable initial found typed selected,
    bind, Except.bind]

/-- Complete descriptor readback follows the same four reached stores at any
derived subobject address, including a representative-array element. Readonly
field loads use the stored leaves without upgrading their pointer permission.
The initial selector must be derived from the declared live parent geometry. -/
theorem fields_after_subobject_stores (state withItem withArguments withId after : State)
    (descriptor : Address) (writable : Bool) (itemAddress argumentsAddress : Address) (length : Nat) (id sequence : Int)
    (selected : ∀ offset field, fieldType allocationType offset = some field →
      fieldPointer state (.pointer (.pointer writable false allocationType) descriptor) offset =
        .ok (.pointer (.pointer writable false field) ⟨descriptor.allocation, descriptor.offset + offset⟩))
    (storedItem : store state (.pointer (.pointer true false itemType) ⟨descriptor.allocation, descriptor.offset + itemOffset⟩)
      (.pointer itemType itemAddress) = .ok withItem)
    (storedArguments : store withItem (.pointer (.pointer true false argumentsType) ⟨descriptor.allocation, descriptor.offset + argumentsOffset⟩)
      (.slice argumentsType argumentsAddress length) = .ok withArguments)
    (storedId : store withArguments (.pointer (.pointer true false idType) ⟨descriptor.allocation, descriptor.offset + idOffset⟩)
      (.scalar (.int false 32 id)) = .ok withId)
    (storedSequence : store withId (.pointer (.pointer true false idType) ⟨descriptor.allocation, descriptor.offset + sequence_numberOffset⟩)
      (.scalar (.int false 32 sequence)) = .ok after) :
    readFields after writable descriptor = .ok [.pointer itemType itemAddress,
      .slice argumentsType argumentsAddress length, .scalar (.int false 32 id), .scalar (.int false 32 sequence)] := by
  have selectors (offset : Nat) :
      fieldPointer after (.pointer (.pointer writable false allocationType) descriptor) offset =
        fieldPointer state (.pointer (.pointer writable false allocationType) descriptor) offset :=
    (fieldPointer_after_store _ _ _ _ writable false _ _ offset storedSequence).trans
      ((fieldPointer_after_store _ _ _ _ writable false _ _ offset storedId).trans
        ((fieldPointer_after_store _ _ _ _ writable false _ _ offset storedArguments).trans
          (fieldPointer_after_store _ _ _ _ writable false _ _ offset storedItem)))
  have selectItem := selected itemOffset itemType field_types_checked.1
  have selectArguments := selected argumentsOffset argumentsType field_types_checked.2.1
  have selectId := selected idOffset idType field_types_checked.2.2.1
  have selectSequence := selected sequence_numberOffset idType field_types_checked.2.2.2
  have itemAfterArguments := load_disjoint_after_store withItem true false argumentsType ⟨descriptor.allocation, descriptor.offset + argumentsOffset⟩
    (.slice argumentsType argumentsAddress length) withArguments writable false itemType (descriptor.offset + itemOffset) storedArguments
    (by simp [Ty.readOffsets, itemType, Value.leaves, argumentsType, itemOffset, argumentsOffset] <;> omega)
  have itemAfterId := load_disjoint_after_store withArguments true false idType ⟨descriptor.allocation, descriptor.offset + idOffset⟩
    (.scalar (.int false 32 id)) withId writable false itemType (descriptor.offset + itemOffset) storedId
    (by simp [Ty.readOffsets, itemType, Value.leaves, itemOffset, idOffset] <;> omega)
  have itemAfterSequence := load_disjoint_after_store withId true false idType ⟨descriptor.allocation, descriptor.offset + sequence_numberOffset⟩
    (.scalar (.int false 32 sequence)) after writable false itemType (descriptor.offset + itemOffset) storedSequence
    (by simp [Ty.readOffsets, itemType, Value.leaves, itemOffset, sequence_numberOffset] <;> omega)
  have argumentsAfterId := load_disjoint_after_store withArguments true false idType ⟨descriptor.allocation, descriptor.offset + idOffset⟩
    (.scalar (.int false 32 id)) withId writable false argumentsType (descriptor.offset + argumentsOffset) storedId
    (by simp [Ty.readOffsets, argumentsType, Value.leaves, argumentsOffset, idOffset] <;> omega)
  have argumentsAfterSequence := load_disjoint_after_store withId true false idType ⟨descriptor.allocation, descriptor.offset + sequence_numberOffset⟩
    (.scalar (.int false 32 sequence)) after writable false argumentsType (descriptor.offset + argumentsOffset) storedSequence
    (by simp [Ty.readOffsets, argumentsType, Value.leaves, argumentsOffset, sequence_numberOffset] <;> omega)
  have idAfterSequence := load_disjoint_after_store withId true false idType ⟨descriptor.allocation, descriptor.offset + sequence_numberOffset⟩
    (.scalar (.int false 32 sequence)) after writable false idType (descriptor.offset + idOffset) storedSequence
    (by simp [Ty.readOffsets, idType, Value.leaves, idOffset, sequence_numberOffset] <;> omega)
  have itemRead := itemAfterSequence.trans (itemAfterId.trans
    (itemAfterArguments.trans (load_alias_after_store _ true false _ _ _ _ writable false storedItem)))
  have argumentsRead := argumentsAfterSequence.trans (argumentsAfterId.trans (load_alias_after_store _ true false _ _ _ _ writable false storedArguments))
  have idRead := idAfterSequence.trans (load_alias_after_store _ true false _ _ _ _ writable false storedId)
  have sequenceRead := load_alias_after_store _ true false _ _ _ _ writable false storedSequence
  simp only [readFields, readField, selectors, selectItem, selectArguments, selectId, selectSequence,
    bind, Except.bind, itemRead, argumentsRead, idRead, sequenceRead]

/-- Complete descriptor initialization follows the four reached stores in the
same heap. In particular a slice's pointer/length leaves and the item pointer
cannot be omitted. This is the field-store connection, not an append/map or
native graph correspondence theorem. -/
theorem fields_after_stores (state withItem withArguments withId after : State) (lifetime : Nat)
    (cell : Allocation) (itemAddress argumentsAddress : Address) (length : Nat) (id sequence : Int)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell) (typed : cell.type = allocationType)
    (storedItem : store state (.pointer (.pointer true false itemType) ⟨lifetime, itemOffset⟩)
      (.pointer itemType itemAddress) = .ok withItem)
    (storedArguments : store withItem (.pointer (.pointer true false argumentsType) ⟨lifetime, argumentsOffset⟩)
      (.slice argumentsType argumentsAddress length) = .ok withArguments)
    (storedId : store withArguments (.pointer (.pointer true false idType) ⟨lifetime, idOffset⟩)
      (.scalar (.int false 32 id)) = .ok withId)
    (storedSequence : store withId (.pointer (.pointer true false idType) ⟨lifetime, sequence_numberOffset⟩)
      (.scalar (.int false 32 sequence)) = .ok after) :
    readFields after true ⟨lifetime, 0⟩ = .ok [.pointer itemType itemAddress,
      .slice argumentsType argumentsAddress length, .scalar (.int false 32 id), .scalar (.int false 32 sequence)] := by
  have selected (offset : Nat) (field : Ty) (chosen : fieldType allocationType offset = some field) :=
    root_selector state lifetime cell offset field true initial found typed chosen
  simpa only [Nat.zero_add] using fields_after_subobject_stores state withItem withArguments withId after
    ⟨lifetime, 0⟩ true itemAddress argumentsAddress length id sequence
    (by simpa only [Nat.zero_add] using selected) storedItem storedArguments storedId storedSequence

end Compiler.Extraction.Expression
