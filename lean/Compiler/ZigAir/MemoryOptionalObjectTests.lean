/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryOptionalObject
import Compiler.ZigAir.MemoryRelease

namespace Compiler.ZigAir.Memory.OptionalObject.Tests

def bytes : Ty := .slice false (.scalar (.int false 8))
def record : Ty := .aggregate "OptionalPayload" ⟨32, 8⟩
  [(0, .scalar (.int false 64)), (8, .scalar (.int false 64)), (16, .object bytes)]
def type : Ty := .optionalObject record ⟨40, 8⟩
def cell : Allocation := ⟨16, type, [], true, false⟩
def before : State := ⟨[(0, cell), (1, ⟨56, usize, [(0, .scalar (.int false 64 7))], true, false⟩)], 2, 64⟩
def pointer (writable : Bool := true) (offset : Nat := 0) : Value :=
  .pointer (.pointer writable false type) ⟨0, offset⟩
def value (contents : Option ObjectValue) : Value := .optionalObject record ⟨40, 8⟩ contents
def saved (contents : Option ObjectValue) : State := (store before (pointer) (value contents)).toOption.getD before
def get (state : State) : Except Fault (Option ObjectValue) := do
  let result ← load state (pointer false)
  payload record ⟨40, 8⟩ result
def fields (count : Int) (address : Address) (length : Nat) : List (Nat × ObjectValue) :=
  [(0, .leaf (.scalar (.int false 64 count))), (8, .leaf (.scalar (.int false 64 2))),
   (16, .leaf (.slice bytes address length))]
def contents : ObjectValue := .fields (fields 3 ⟨99, 5⟩ 4)

theorem initial_valid_and_layout : before.valid = true ∧ type.layout = some ⟨40, 8⟩ := ⟨by decide, rfl⟩

theorem write_result (contents : Option ObjectValue) (typed : Typed record contents) :
    store before (pointer) (value contents) = .ok (saved contents) := by
  obtain ⟨after, stored, _, _⟩ := store_root before 0 cell record ⟨40, 8⟩ contents typed
    initial_valid_and_layout.1 rfl rfl rfl rfl (by decide)
  have executed : store before (pointer) (value contents) = .ok after := stored
  simp only [saved, executed, Except.toOption, Option.getD]

theorem every_payload (contents : Option ObjectValue) (typed : Typed record contents) :
    (saved contents).valid = true ∧ get (saved contents) = .ok contents :=
  ⟨store_preserves_valid before (pointer) (value contents) (saved contents)
    initial_valid_and_layout.1 (write_result contents typed),
   read_after_store before (saved contents) ⟨0, 0⟩ record ⟨40, 8⟩ contents typed (write_result contents typed)⟩

theorem missing_null_and_present : get before = .error .uninitialized ∧
    get (saved none) = .ok none ∧ get (saved (some contents)) = .ok (some contents) :=
  ⟨by rfl', by rfl', by rfl'⟩
theorem address_offset_length_identity : get (saved (some contents)) =
    .ok (some (.fields (fields 3 ⟨99, 5⟩ 4))) := by rfl'
theorem copying_is_not_pointee_liveness : (saved (some contents)).valid = true ∧
    load (saved (some contents)) (.pointer (.pointer false true (.scalar (.int false 8))) ⟨99, 5⟩) =
      .error .unallocated := ⟨by decide, by rfl'⟩
theorem independent_word : load (saved (some contents)) (.pointer (.pointer false false usize) ⟨1, 0⟩) =
    .ok (.scalar (.int false 64 7)) := by rfl'

def erasedPayload := (store (saved (some contents)) (pointer) (value none)).toOption.getD before
theorem overwrite_clears_payload : get erasedPayload = .ok none ∧
    (erasedPayload.heap.lookup 0).map (fun cell => cell.cells.length) = some 1 := ⟨by rfl', by rfl'⟩

theorem complete_ordered_fields_required :
    store before (pointer) (value (some (.fields (fields 3 ⟨99, 5⟩ 4).tail))) = .error .malformed ∧
    store before (pointer) (value (some (.fields (fields 3 ⟨99, 5⟩ 4 ++ [(32, .leaf (.scalar (.int false 64 0)))])))) = .error .malformed ∧
    store before (pointer) (value (some (.fields (fields 3 ⟨99, 5⟩ 4).reverse))) = .error .malformed ∧
    store before (pointer) (value (some (.fields ((0, .leaf (.scalar (.int false 64 3))) :: fields 3 ⟨99, 5⟩ 4)))) = .error .malformed :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩
theorem exact_offsets_required :
    payload record ⟨40, 8⟩ (value (some (.fields
      [(0, .leaf (.scalar (.int false 64 3))), (9, .leaf (.scalar (.int false 64 2))),
       (16, .leaf (.slice bytes ⟨99, 5⟩ 4))]))) = .error .malformed := by rfl'
theorem field_type_and_range_required :
    store before (pointer) (value (some (.fields (fields (-1) ⟨99, 5⟩ 4)))) = .error .malformed ∧
    store before (pointer) (value (some (.fields (fields (2^64) ⟨99, 5⟩ 4)))) = .error .malformed ∧
    payload record ⟨40, 8⟩ (value (some (.fields
      [(0, .leaf (.scalar (.int true 64 3))), (8, .leaf (.scalar (.int false 64 2))),
       (16, .leaf (.slice bytes ⟨99, 5⟩ 4))]))) = .error .malformed := ⟨by rfl', by rfl', by rfl'⟩
theorem length_range_required : store before (pointer)
    (value (some (.fields (fields 3 ⟨99, 5⟩ (2^64))))) = .error .malformed := by rfl'
theorem exact_optional_type_required :
    payload record ⟨40, 8⟩ (.optionalObject (.aggregate "Wrong" ⟨32, 8⟩
      [(0, .scalar (.int false 64)), (8, .scalar (.int false 64)), (16, .object bytes)]) ⟨40, 8⟩ none) = .error .malformed ∧
    payload record ⟨40, 8⟩ (.optionalObject record ⟨48, 8⟩ none) = .error .malformed ∧
    payload record ⟨40, 8⟩ (.optionalObject bytes ⟨40, 8⟩ none) = .error .malformed := ⟨by rfl', by rfl', by rfl'⟩

theorem no_byte_projection : fieldType type 0 = none ∧ fieldType type 32 = none ∧
    load (saved (some contents)) (.pointer (.pointer false false usize) ⟨0, 0⟩) = .error .unsupported ∧
    load (saved (some contents)) (.pointer (.pointer false false record) ⟨0, 0⟩) = .error .unsupported :=
  ⟨rfl, rfl, by rfl', by rfl'⟩
theorem readonly_misaligned_outside_and_dead :
    store before (pointer false) (value none) = .error .readOnly ∧
    store { before with heap := [(0, { cell with writable := false })] } (pointer) (value none) = .error .readOnly ∧
    load { before with heap := [(0, { cell with type := .array 2 type })], nextAddress := 96 }
      (pointer false 1) = .error .memoryValidity ∧
    load (saved none) (pointer false 40) = .error .memoryValidity ∧
    get (erase (saved (some contents)) 0) = .error .unallocated := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem invalid_geometry_rejects :
    (Ty.optionalObject record ⟨24, 8⟩).layout = none ∧
    (Ty.optionalObject record ⟨40, 0⟩).layout = none ∧
    (Ty.optionalObject record ⟨40, 4⟩).layout = none ∧
    (Ty.optionalObject record ⟨41, 8⟩).layout = none ∧
    (Ty.optionalObject (.aggregate "Bad" ⟨16, 8⟩ [(8, .object bytes)]) ⟨40, 8⟩).layout = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem unsupported_child_rejects :
    (Ty.optionalObject usize ⟨16, 8⟩).layout = none ∧
    (Ty.optionalObject (.array 2 usize) ⟨24, 8⟩).layout = none ∧
    allocate before (.optionalObject (.record "Opaque" ⟨32, 8⟩) ⟨40, 8⟩) = .error .unsupported := ⟨rfl, rfl, by rfl'⟩

def array : State := ⟨[(0, ⟨16, .array 2 type, [], true, false⟩)], 1, 96⟩
theorem array_stride_and_bounds :
    sliceElementPointer array (.slice (.slice true type) ⟨0, 0⟩ 2) 1 = .ok (pointer true 40) ∧
    sliceElementPointer array (.slice (.slice true type) ⟨0, 0⟩ 2) 2 = .error .sourceBounds := ⟨by rfl', by rfl'⟩

def sliceType : Ty := .optionalObject bytes ⟨16, 8⟩
def sliceBefore : State := ⟨[(0, ⟨16, sliceType, [], true, false⟩)], 1, 32⟩
def slicePointer : Value := .pointer (.pointer true false sliceType) ⟨0, 0⟩
def sliceSaved (contents : Option ObjectValue) :=
  (store sliceBefore slicePointer (.optionalObject bytes ⟨16, 8⟩ contents)).toOption.getD sliceBefore
theorem null_and_empty_slice_differ :
    load (sliceSaved none) slicePointer = .ok (.optionalObject bytes ⟨16, 8⟩ none) ∧
    load (sliceSaved (some (.leaf (.slice bytes ⟨99, 5⟩ 0)))) slicePointer =
      .ok (.optionalObject bytes ⟨16, 8⟩ (some (.leaf (.slice bytes ⟨99, 5⟩ 0)))) := ⟨by rfl', by rfl'⟩
theorem slice_permissions_and_length_checked :
    payload bytes ⟨16, 8⟩ (.optionalObject bytes ⟨16, 8⟩
      (some (.leaf (.slice (.slice true (.scalar (.int false 8))) ⟨99, 5⟩ 0)))) = .error .malformed ∧
    payload bytes ⟨16, 8⟩ (.optionalObject bytes ⟨16, 8⟩
      (some (.leaf (.slice bytes ⟨99, 5⟩ (2^64))))) = .error .malformed := ⟨by rfl', by rfl'⟩

def nested : Ty := .aggregate "Nested" ⟨48, 8⟩ [(0, .object record), (32, .object sliceType)]
def nestedValue : ObjectValue := .fields [(0, contents), (32, .leaf (.optionalObject bytes ⟨16, 8⟩ none))]
theorem nested_payload_checked : nestedValue.hasType nested = true ∧
    (ObjectValue.fields [(0, contents), (32, .leaf (.optionalObject bytes ⟨16, 8⟩
      (some (.fields []))))]).hasType nested = false ∧
    (ObjectValue.fields [(0, .fields []), (32, .leaf (.optionalObject bytes ⟨16, 8⟩ none))]).hasType nested = false :=
  ⟨by decide, by decide, by decide⟩

end Compiler.ZigAir.Memory.OptionalObject.Tests
