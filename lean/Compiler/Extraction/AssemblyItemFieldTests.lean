/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemFields
import Compiler.ZigAir.MemoryOptionalScalarTests
import Compiler.Extraction.ExpressionLifetimeTests

namespace Compiler.Extraction.AssemblyItem.Fields.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

def initial := Compiler.Extraction.ExpressionDeinit.Lifetime.Tests.initial
def request : Creation.Allocate Nat := fun _ before => (some 320, before.effects + 1)
def created := (Creation.create request 7 Compiler.Extraction.ExpressionDeinit.Lifetime.Tests.itemValue initial).2

theorem created_contract :
    Creation.create request 7 Compiler.Extraction.ExpressionDeinit.Lifetime.Tests.itemValue initial = (.ok 5, created) ∧
    Creation.Created 7 5 initial created := by
  have fits : RegionAllocation.Fits initial.memory Creation.layout 320 := by
    refine ⟨by decide, by decide, by decide, ?_⟩
    intro entry present old shaped
    have valid := Compiler.Extraction.ExpressionDeinit.Lifetime.Tests.initial_valid.memory
    simp only [State.valid, Bool.and_eq_true, List.all_eq_true] at valid
    have region := (valid.1.2 entry present).2
    simp only [shaped, Bool.and_eq_true, decide_eq_true_eq] at region
    exact Or.inr (Nat.le_trans region.1.2 (by decide))
  exact Creation.create_from_response request 7 320 Compiler.Extraction.ExpressionDeinit.Lifetime.Tests.itemValue initial 1 Compiler.Extraction.ExpressionDeinit.Lifetime.Tests.initial_valid rfl fits

def ptr (offset : Nat) (type : Ty) (writable : Bool := true) : Value :=
  .pointer (.pointer writable false type) ⟨5, offset⟩
def wide : Value := .scalar (.int false 256 (2^255 + 17))
def writes : Except Fault State := do
  let a ← store created.memory (ptr item_typeOffset (.scalar (.int true 32))) (.scalar (.int true 32 2))
  let b ← store a (ptr data_valueOffset (.scalar (.int false 256))) wide
  let c ← store b (ptr jump_typeOffset (.scalar (.int true 32))) (.scalar (.int true 32 2))
  store c (ptr modifier_depthOffset usize) (.scalar (.int false 64 19))
def initialized := writes.toOption.getD created.memory

theorem allocation_not_initialization :
    read created.memory ⟨5, 0⟩ item_typeOffset = .error .uninitialized ∧
    read created.memory ⟨5, 0⟩ data_valueOffset = .error .uninitialized ∧
    read created.memory ⟨5, 0⟩ jump_typeOffset = .error .uninitialized ∧
    read created.memory ⟨5, 0⟩ modifier_depthOffset = .error .uninitialized :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem complete_scalar_readback : writes = .ok initialized ∧
    kind initialized ⟨5, 0⟩ = .ok 2 ∧ read initialized ⟨5, 0⟩ data_valueOffset = .ok wide ∧
    jump initialized ⟨5, 0⟩ = .ok 2 ∧
    read initialized ⟨5, 0⟩ modifier_depthOffset = .ok (.scalar (.int false 64 19)) :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem parent_unchanged : initialized.heap.lookup 0 = initial.memory.heap.lookup 0 ∧
    initialized.heap.lookup 4 = initial.memory.heap.lookup 4 := ⟨by rfl', by rfl'⟩

def changedTag (offset : Nat) (value : Int) :=
  (store initialized (ptr offset (.scalar (.int true 32))) (.scalar (.int true 32 value))).toOption.getD initialized

theorem invalid_tags_reject : kind (changedTag item_typeOffset (-1)) ⟨5, 0⟩ = .error .malformed ∧
    kind (changedTag item_typeOffset 14) ⟨5, 0⟩ = .error .malformed ∧
    jump (changedTag jump_typeOffset 3) ⟨5, 0⟩ = .error .malformed := ⟨by rfl', by rfl', by rfl'⟩

theorem compound_fields_need_initialization :
    read initialized ⟨5, 0⟩ verbatimOffset = .error .uninitialized ∧
    read initialized ⟨5, 0⟩ debug_dataOffset = .error .unsupported := ⟨by rfl', by rfl'⟩

theorem integer_optionals_missing :
    optional initialized ⟨5, 0⟩ .pushed = .error .uninitialized ∧
    optional initialized ⟨5, 0⟩ .immutable = .error .uninitialized := ⟨by rfl', by rfl'⟩

theorem all_optional_payloads (field : OptionalField) (payload : Option (BitVec field.bits)) :
    ∃ after, store created.memory (ptr field.offset (OptionalScalar.unsigned field.bits))
      (OptionalScalar.unsignedValue field.bits payload) = .ok after ∧ after.valid = true ∧
      optional after ⟨5, 0⟩ field = .ok payload :=
  optional_store created.memory 5 (Creation.cell 320) field payload created_contract.2.valid.memory (by rfl') rfl rfl

def withIntegerOptionals (word : Option (BitVec 256)) (size : Option (BitVec 64)) := (do
  let memory ← store initialized (ptr pushed_valueOffset (OptionalScalar.unsigned 256)) (OptionalScalar.unsignedValue 256 word)
  store memory (ptr immutable_occurrencesOffset (OptionalScalar.unsigned 64)) (OptionalScalar.unsignedValue 64 size)
  : Except Fault State).toOption.getD initialized

theorem integer_optionals_null : optional (withIntegerOptionals none none) ⟨5, 0⟩ .pushed = .ok none ∧
    optional (withIntegerOptionals none none) ⟨5, 0⟩ .immutable = .ok none := ⟨by rfl', by rfl'⟩
theorem integer_optionals_zero : optional (withIntegerOptionals (some 0) (some 0)) ⟨5, 0⟩ .pushed = .ok (some 0) ∧
    optional (withIntegerOptionals (some 0) (some 0)) ⟨5, 0⟩ .immutable = .ok (some 0) := ⟨by rfl', by rfl'⟩
theorem integer_optionals_high_bits :
    optional (withIntegerOptionals (some (BitVec.ofNat 256 (2^255 + 17))) (some (BitVec.ofNat 64 (2^63 + 17))))
      ⟨5, 0⟩ .pushed = .ok (some (BitVec.ofNat 256 (2^255 + 17))) ∧
    optional (withIntegerOptionals (some (BitVec.ofNat 256 (2^255 + 17))) (some (BitVec.ofNat 64 (2^63 + 17))))
      ⟨5, 0⟩ .immutable = .ok (some (BitVec.ofNat 64 (2^63 + 17))) :=
  ⟨by rfl', by rfl'⟩
theorem integer_optionals_frame :
    read (withIntegerOptionals (some (-1)) (some (-1))) ⟨5, 0⟩ data_valueOffset = .ok wide ∧
    kind (withIntegerOptionals none (some 0)) ⟨5, 0⟩ = .ok 2 ∧
    (withIntegerOptionals none none).heap.lookup 0 = initial.memory.heap.lookup 0 := ⟨by rfl', by rfl', by rfl'⟩
theorem integer_optionals_no_punning :
    store initialized (ptr pushed_valueOffset (OptionalScalar.unsigned 64)) (OptionalScalar.unsignedValue 64 none) =
      .error .unsupported ∧
    store initialized (ptr immutable_occurrencesOffset (OptionalScalar.unsigned 256)) (OptionalScalar.unsignedValue 256 none) =
      .error .memoryValidity := ⟨by rfl', by rfl'⟩

theorem padding_rejects : read initialized ⟨5, 0⟩ 218 = .error .unsupported := by rfl'
theorem readonly_store_rejects : store initialized (ptr item_typeOffset (.scalar (.int true 32)) false)
    (.scalar (.int true 32 1)) = .error .readOnly := by rfl'
theorem wrong_scalar_rejects : store initialized (ptr item_typeOffset usize) (.scalar (.int false 64 1)) =
    .error .unsupported := by rfl'

def substitute (type : Ty) : State :=
  { created.memory with heap := created.memory.heap.replace 5 { Creation.cell 320 with type := type } }

theorem nominal_is_not_declaration : read (substitute allocationType) ⟨5, 0⟩ item_typeOffset = .error .unsupported := by rfl'
theorem partial_is_not_declaration : read (substitute (.aggregate "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨224, 16⟩
    [(208, .scalar (.int true 32))])) ⟨5, 0⟩ item_typeOffset = .error .unsupported := by rfl'
theorem wrong_identity_rejects : recordView initialized viewType
    (.pointer (.pointer true false (.record "OtherItem" ⟨224, 16⟩)) ⟨5, 0⟩) = .error .unsupported := by rfl'
theorem interior_rejects : read initialized ⟨5, 16⟩ item_typeOffset = .error .memoryValidity := by rfl'

def released := AssemblyItem.destroy (fun _ before => before.effects + 2) 7 5 { created with memory := initialized }
def reused := Creation.create request 7 Compiler.Extraction.ExpressionDeinit.Lifetime.Tests.itemValue released.2

theorem release_invalidates_fields : released.1 = .ok () ∧ released.2.effects = 3 ∧
    read released.2.memory ⟨5, 0⟩ item_typeOffset = .error .unallocated := ⟨by rfl', by rfl', by rfl'⟩
theorem address_reuse_keeps_history : reused.1 = .ok 6 ∧ reused.2.memory.nextId = 7 ∧
    read reused.2.memory ⟨5, 0⟩ item_typeOffset = .error .unallocated ∧
    read reused.2.memory ⟨6, 0⟩ item_typeOffset = .error .uninitialized := ⟨by rfl', by rfl', by rfl', by rfl'⟩

def withInstruction (payload : Option (BitVec 8)) :=
  (store initialized (ptr instruction_valueOffset OptionalScalar.byte) (OptionalScalar.byteValue payload)).toOption.getD initialized

theorem instruction_missing : instruction initialized ⟨5, 0⟩ = .error .uninitialized := by rfl'
theorem instruction_null : instruction (withInstruction none) ⟨5, 0⟩ = .ok none := by rfl'
theorem instruction_zero : instruction (withInstruction (some 0)) ⟨5, 0⟩ = .ok (some 0) := by rfl'
theorem instruction_unknown_opcode : instruction (withInstruction (some 12)) ⟨5, 0⟩ = .ok (some 12) := by rfl'
theorem instruction_last_opcode : instruction (withInstruction (some 255)) ⟨5, 0⟩ = .ok (some 255) := by rfl'
theorem instruction_frames_scalars : kind (withInstruction (some 12)) ⟨5, 0⟩ = .ok 2 ∧
    read (withInstruction (some 12)) ⟨5, 0⟩ data_valueOffset = .ok wide ∧ jump (withInstruction none) ⟨5, 0⟩ = .ok 2 :=
  ⟨by rfl', by rfl', by rfl'⟩
theorem instruction_dead_alias : instruction released.2.memory ⟨5, 0⟩ = .error .unallocated := by rfl'
theorem instruction_reuse_uninitialized : instruction reused.2.memory ⟨6, 0⟩ = .error .uninitialized := by rfl'

end Compiler.Extraction.AssemblyItem.Fields.Tests
