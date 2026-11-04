/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemFields
import Compiler.ZigAir.MemoryOptionalObject

namespace Compiler.Extraction.AssemblyItem.Fields
open Compiler.ZigAir.Memory

/-- All atomic members of the captured complete declaration. Optional verbatim
and source-name payloads stay atomic; debug data has seven declared leaves. -/
inductive Member where
  | kind | instruction | data | verbatim | pushed | immutable | modifier | jump
  | nativeStart | nativeEnd | nativeSource | originStart | originEnd | originSource | astId
  deriving DecidableEq, Repr

def Member.type : Member → Ty
  | .kind | .jump | .nativeStart | .nativeEnd | .originStart | .originEnd => .scalar (.int true 32)
  | .instruction => OptionalScalar.byte
  | .data => .scalar (.int false 256)
  | .verbatim => verbatimOptionalType
  | .pushed => OptionalScalar.unsigned 256
  | .immutable => OptionalScalar.unsigned 64
  | .modifier => usize
  | .nativeSource | .originSource => sourceNameType
  | .astId => .optionalScalar (.int true 64)

def Member.offset : Member → Nat
  | .kind => item_typeOffset
  | .instruction => OptionalField.instruction.offset
  | .data => data_valueOffset
  | .verbatim => verbatimOffset
  | .pushed => OptionalField.pushed.offset
  | .immutable => OptionalField.immutable.offset
  | .modifier => modifier_depthOffset
  | .jump => jump_typeOffset
  | .nativeStart => debug_dataOffset + debug_data_native_locationOffset + source_location_startOffset
  | .nativeEnd => debug_dataOffset + debug_data_native_locationOffset + source_location_endOffset
  | .nativeSource => debug_dataOffset + debug_data_native_locationOffset + source_location_source_nameOffset
  | .originStart => debug_dataOffset + debug_data_origin_locationOffset + source_location_startOffset
  | .originEnd => debug_dataOffset + debug_data_origin_locationOffset + source_location_endOffset
  | .originSource => debug_dataOffset + debug_data_origin_locationOffset + source_location_source_nameOffset
  | .astId => debug_dataOffset + debug_data_ast_idOffset

def Member.layout : Member → Layout
  | .kind | .jump | .nativeStart | .nativeEnd | .originStart | .originEnd => ⟨4, 4⟩
  | .instruction => ⟨2, 1⟩
  | .data => ⟨32, 16⟩
  | .verbatim => ⟨40, 8⟩
  | .pushed => ⟨48, 16⟩
  | .immutable | .astId | .nativeSource | .originSource => ⟨16, 8⟩
  | .modifier => ⟨8, 8⟩

theorem Member.geometry (member : Member) : LeafGeometry member.offset member.type member.layout := by
  cases member <;> constructor <;> decide

def member (state : State) (address : Address) (selected : Member) : Except Fault Value :=
  readTyped state address selected.offset selected.type

/-- Complete initial allocation geometry derives each native member's store,
validity and exact typed readback; no initialized-field premise is assumed. -/
theorem member_store (state : State) (id : Nat) (cell : Allocation) (selected : Member) (value : Value)
    (valueTyped : value.hasType selected.type = true)
    (valid : state.valid = true) (found : state.heap.lookup id = some cell) (typed : cell.type = viewType)
    (writable : cell.writable = true) :
    ∃ after, store state (.pointer (.pointer true false selected.type) ⟨id, selected.offset⟩) value = .ok after ∧
      after.valid = true ∧ member after ⟨id, 0⟩ selected = .ok value :=
  leaf_store state id cell selected.offset selected.type selected.layout value selected.geometry valueTyped
    valid found typed writable

def verbatim (state : State) (address : Address) : Except Fault (Option ObjectValue) := do
  let value ← member state address .verbatim
  OptionalObject.payload verbatimType ⟨40, 8⟩ value

def sourceName (state : State) (address : Address) (origin : Bool) : Except Fault (Option ObjectValue) := do
  let value ← member state address (if origin then .originSource else .nativeSource)
  OptionalObject.payload (.slice false (.scalar (.int false 8))) ⟨16, 8⟩ value

end Compiler.Extraction.AssemblyItem.Fields
