/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryOptionalObject
import Compiler.ZigAir.MemoryRelease
import Compiler.ZigAir.MemoryRecordFields

namespace Compiler.ZigAir.Memory.OptionalObject.PointerTests

def child : Ty := .pointer true true (.record "Metadata" ⟨1, 1⟩)
def type : Ty := .optionalObject child ⟨8, 8⟩
def cell : Allocation := ⟨16, type, [], true, true⟩
def before : State := ⟨[(0, cell)], 1, 24⟩
def pointer : Value := .pointer (.pointer true false type) ⟨0, 0⟩
def value (contents : Option ObjectValue) : Value := .optionalObject child ⟨8, 8⟩ contents
def saved (contents : Option ObjectValue) : State := (store before pointer (value contents)).toOption.getD before
def get (state : State) : Except Fault (Option ObjectValue) := do
  let loaded ← load state pointer
  payload child ⟨8, 8⟩ loaded
def present (address : Address) : Option ObjectValue := some (.leaf (.pointer child address))

theorem initial_valid_and_layout : before.valid = true ∧ type.layout = some ⟨8, 8⟩ := ⟨by decide, rfl⟩

/-- Null and every well-typed copied pointer initialize the complete atomic
value. This supplies no allocation, ownership or contents for that pointer. -/
theorem every_payload (contents : Option ObjectValue) (typed : Typed child contents) :
    ∃ after, store before pointer (value contents) = .ok after ∧ after.valid = true ∧ get after = .ok contents :=
  store_root before 0 cell child ⟨8, 8⟩ contents typed initial_valid_and_layout.1 rfl rfl rfl rfl (by decide)

theorem missing_null_and_present : get before = .error .uninitialized ∧
    get (saved none) = .ok none ∧ get (saved (present ⟨99, 7⟩)) = .ok (present ⟨99, 7⟩) := ⟨by rfl', by rfl', by rfl'⟩

theorem nullable_word_does_not_allocate_pointee :
    (saved (present ⟨99, 7⟩)).valid = true ∧ (saved (present ⟨99, 7⟩)).heap.lookup 99 = none ∧
      (saved none).nextId = before.nextId ∧ (saved none).nextAddress = before.nextAddress := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem wrong_payload_rejects :
    store before pointer (value (some (.leaf (.pointer (.pointer false true (.record "Metadata" ⟨1, 1⟩)) ⟨99, 7⟩)))) = .error .malformed ∧
    store before pointer (value (some (.leaf (.pointer (.pointer true false (.record "Metadata" ⟨1, 1⟩)) ⟨99, 7⟩)))) = .error .malformed ∧
    store before pointer (value (some (.leaf (.scalar (.int false 64 0))))) = .error .malformed := ⟨by rfl', by rfl', by rfl'⟩

theorem nullable_layout_is_exact :
    (Ty.optionalObject child ⟨16, 8⟩).layout = none ∧ (Ty.optionalObject child ⟨8, 4⟩).layout = none ∧
      (Ty.optionalObject child ⟨0, 8⟩).layout = none ∧ (Ty.optionalObject child ⟨8, 0⟩).layout = none := by decide

theorem no_pointer_or_discriminator_projection : fieldType type 0 = none ∧
    fieldPointer (saved none) pointer 0 = .error .unsupported ∧
    load (saved none) (.pointer (.pointer false false child) ⟨0, 0⟩) = .error .unsupported := ⟨by rfl', by rfl', by rfl'⟩

theorem readonly_dead_and_misaligned_reject :
    store { before with heap := [(0, { cell with writable := false })] } pointer (value none) = .error .readOnly ∧
    load (cleanup 0 (saved none)) pointer = .error .unallocated ∧
    store before (.pointer (.pointer true false type) ⟨0, 1⟩) (value none) = .error .memoryValidity := ⟨by rfl', by rfl', by rfl'⟩

theorem exhaustive_lock_tag_range : (Ty.scalar (.int false 1)).layout = some ⟨1, 1⟩ ∧
    (Value.scalar (.int false 1 0)).valid = true ∧ (Value.scalar (.int false 1 1)).valid = true ∧
    (Value.scalar (.int false 1 2)).valid = false := by decide

end Compiler.ZigAir.Memory.OptionalObject.PointerTests
