/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemMembers
import Compiler.Extraction.AssemblyItemFieldTests

namespace Compiler.Extraction.AssemblyItem.Fields.MemberTests
open Compiler.ZigAir.Memory

def before := Tests.created.memory
def ptr (selected : Member) (writable : Bool := true) : Value := Tests.ptr selected.offset selected.type writable
def saved (selected : Member) (value : Value) : State := (store before (ptr selected) value).toOption.getD before

theorem all_member_values (selected : Member) (value : Value) (typed : value.hasType selected.type = true) :
    ∃ after, store before (ptr selected) value = .ok after ∧ after.valid = true ∧
      member after ⟨5, 0⟩ selected = .ok value :=
  member_store before 5 (Creation.cell 320) selected value typed Tests.created_contract.2.valid.memory (by rfl') rfl rfl

theorem missing_compound_members : member before ⟨5, 0⟩ .verbatim = .error .uninitialized ∧
    member before ⟨5, 0⟩ .nativeSource = .error .uninitialized ∧
    member before ⟨5, 0⟩ .originSource = .error .uninitialized ∧
    member before ⟨5, 0⟩ .astId = .error .uninitialized := ⟨by rfl', by rfl', by rfl', by rfl'⟩

def verbatimValue (payload : Option ObjectValue) : Value := .optionalObject verbatimType ⟨40, 8⟩ payload
def payload (arguments returns : Int) (address : Address) (length : Nat) : ObjectValue := .fields
  [(verbatim_argumentsOffset, .leaf (.scalar (.int false 64 arguments))),
   (verbatim_return_variablesOffset, .leaf (.scalar (.int false 64 returns))),
   (verbatim_dataOffset, .leaf (.slice (.slice true (.scalar (.int false 8))) address length))]

theorem all_verbatim_payloads (payload : Option ObjectValue) (typed : OptionalObject.Typed verbatimType payload) :
    ∃ after, store before (ptr .verbatim) (verbatimValue payload) = .ok after ∧ after.valid = true ∧
      verbatim after ⟨5, 0⟩ = .ok payload := by
  have valueTyped : (verbatimValue payload).hasType Member.verbatim.type = true := by
    simpa only [Value.hasType, verbatimValue, Member.type, verbatimOptionalType, Value.type,
      decide_true, Bool.true_and] using OptionalObject.value_valid verbatimType ⟨40, 8⟩ payload typed
  obtain ⟨after, stored, valid, readback⟩ := all_member_values .verbatim (verbatimValue payload) valueTyped
  refine ⟨after, stored, valid, ?_⟩
  rw [verbatim, readback]
  exact OptionalObject.payload_value verbatimType ⟨40, 8⟩ payload typed

theorem verbatim_null_empty_and_offset :
    verbatim (saved .verbatim (verbatimValue none)) ⟨5, 0⟩ = .ok none ∧
    verbatim (saved .verbatim (verbatimValue (some (payload 0 0 ⟨99, 2⟩ 0)))) ⟨5, 0⟩ = .ok (some (payload 0 0 ⟨99, 2⟩ 0)) ∧
    verbatim (saved .verbatim (verbatimValue (some (payload 3 2 ⟨99, 1⟩ 3)))) ⟨5, 0⟩ = .ok (some (payload 3 2 ⟨99, 1⟩ 3)) ∧
    verbatim (saved .verbatim (verbatimValue (some (payload (2^64-1) (2^64-1) ⟨99, 0⟩ 6)))) ⟨5, 0⟩ =
      .ok (some (payload (2^64-1) (2^64-1) ⟨99, 0⟩ 6)) := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem verbatim_incomplete_wrong_permission_and_range :
    store before (ptr .verbatim) (verbatimValue (some (.fields []))) = .error .malformed ∧
    store before (ptr .verbatim) (verbatimValue (some (payload (-1) 0 ⟨99, 0⟩ 0))) = .error .malformed ∧
    store before (ptr .verbatim) (verbatimValue (some (payload 0 (2^64) ⟨99, 0⟩ 0))) = .error .malformed ∧
    store before (ptr .verbatim) (verbatimValue (some (.fields
      [(0, .leaf (.scalar (.int false 64 0))), (8, .leaf (.scalar (.int false 64 0))),
       (16, .leaf (.slice (.slice false (.scalar (.int false 8))) ⟨99, 0⟩ 0))]))) = .error .malformed :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

def sourceValue (payload : Option (Address × Nat)) : Value :=
  .optionalObject (.slice false (.scalar (.int false 8))) ⟨16, 8⟩
    (payload.map fun (address, length) => .leaf (.slice (.slice false (.scalar (.int false 8))) address length))
def astValue (payload : Option Int) : Value := .optionalScalar (.int true 64) (payload.map (.int true 64))
def debugWrites : Except Fault State := do
  let a ← store Tests.initialized (ptr .nativeSource) (sourceValue (some (⟨99, 2⟩, 3)))
  let b ← store a (ptr .nativeStart) (.scalar (.int true 32 (-1)))
  let c ← store b (ptr .nativeEnd) (.scalar (.int true 32 17))
  let d ← store c (ptr .originSource) (sourceValue (some (⟨100, 7⟩, 0)))
  let e ← store d (ptr .originStart) (.scalar (.int true 32 (-(2^31))))
  let f ← store e (ptr .originEnd) (.scalar (.int true 32 (2^31-1)))
  store f (ptr .astId) (astValue (some (-1)))
-- Share the expected reached state across observations instead of repeatedly
-- reducing the seven-store execution in each independent assertion.
def debugInitialized : State :=
  { Tests.initialized with
    heap := Tests.initialized.heap.replace 5
      { Creation.cell 320 with cells :=
        [(168, astValue (some (-1))), (164, .scalar (.int true 32 (2^31-1))),
         (160, .scalar (.int true 32 (-(2^31)))), (144, sourceValue (some (⟨100, 7⟩, 0))),
         (140, .scalar (.int true 32 17)), (136, .scalar (.int true 32 (-1))),
         (120, sourceValue (some (⟨99, 2⟩, 3))), (200, .scalar (.int false 64 19)),
         (212, .scalar (.int true 32 2)), (0, Tests.wide), (208, .scalar (.int true 32 2))] } }

theorem nested_debug_readback : debugWrites = .ok debugInitialized ∧ debugInitialized.valid = true ∧
    member debugInitialized ⟨5, 0⟩ .nativeStart = .ok (.scalar (.int true 32 (-1))) ∧
    member debugInitialized ⟨5, 0⟩ .nativeEnd = .ok (.scalar (.int true 32 17)) ∧
    member debugInitialized ⟨5, 0⟩ .originStart = .ok (.scalar (.int true 32 (-(2^31)))) ∧
    member debugInitialized ⟨5, 0⟩ .originEnd = .ok (.scalar (.int true 32 (2^31-1))) ∧
    member debugInitialized ⟨5, 0⟩ .astId = .ok (astValue (some (-1))) :=
  ⟨by rfl', by decide, by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem source_descriptors_keep_identity_offset_and_empty :
    member debugInitialized ⟨5, 0⟩ .nativeSource = .ok (sourceValue (some (⟨99, 2⟩, 3))) ∧
    member debugInitialized ⟨5, 0⟩ .originSource = .ok (sourceValue (some (⟨100, 7⟩, 0))) ∧
    sourceName (saved .nativeSource (sourceValue none)) ⟨5, 0⟩ false = .ok none ∧
    sourceName debugInitialized ⟨5, 0⟩ true = .ok (some (.leaf (.slice (.slice false (.scalar (.int false 8))) ⟨100, 7⟩ 0))) :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem debug_frames_neighbors : read debugInitialized ⟨5, 0⟩ data_valueOffset = .ok Tests.wide ∧
    kind debugInitialized ⟨5, 0⟩ = .ok 2 ∧ debugInitialized.heap.lookup 0 = Tests.initial.memory.heap.lookup 0 ∧
    member debugInitialized ⟨5, 0⟩ .immutable = .error .uninitialized := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem signed_ast_boundaries :
    member (saved .astId (astValue none)) ⟨5, 0⟩ .astId = .ok (astValue none) ∧
    member (saved .astId (astValue (some 0))) ⟨5, 0⟩ .astId = .ok (astValue (some 0)) ∧
    member (saved .astId (astValue (some (-(2^63))))) ⟨5, 0⟩ .astId = .ok (astValue (some (-(2^63)))) ∧
    member (saved .astId (astValue (some (2^63-1)))) ⟨5, 0⟩ .astId = .ok (astValue (some (2^63-1))) ∧
    store before (ptr .astId) (astValue (some (-(2^63)-1))) = .error .malformed ∧
    store before (ptr .astId) (astValue (some (2^63))) = .error .malformed :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem source_and_ast_type_confusion_reject :
    store before (ptr .nativeSource) (sourceValue (some (⟨99, 0⟩, 2^64))) = .error .malformed ∧
    store before (ptr .astId) (OptionalScalar.unsignedValue 64 none) = .error .malformed ∧
    store before (ptr .originStart) (.scalar (.int true 32 (2^31))) = .error .malformed := ⟨by rfl', by rfl', by rfl'⟩

theorem no_optional_or_whole_debug_punning :
    readTyped debugInitialized ⟨5, 0⟩ Member.nativeSource.offset (.slice false (.scalar (.int false 8))) = .error .unsupported ∧
    readTyped debugInitialized ⟨5, 0⟩ Member.astId.offset (.scalar (.int true 64)) = .error .unsupported ∧
    read debugInitialized ⟨5, 0⟩ debug_dataOffset = .error .unsupported := ⟨by rfl', by rfl', by rfl'⟩

theorem readonly_dead_and_borrowed : store before (ptr .astId false) (astValue none) = .error .readOnly ∧
    member (erase debugInitialized 5) ⟨5, 0⟩ .originSource = .error .unallocated ∧
    load debugInitialized (.pointer (.pointer false false (.scalar (.int false 8))) ⟨99, 2⟩) = .error .unallocated :=
  ⟨by rfl', by rfl', by rfl'⟩

def array : State := ⟨[(0, ⟨16, .array 2 viewType,
  [(344, sourceValue (some (⟨99, 2⟩, 3)))], true, false⟩)], 1, 464⟩
theorem nonzero_item_view : array.valid = true ∧
    member array ⟨0, 224⟩ .nativeSource = .ok (sourceValue (some (⟨99, 2⟩, 3))) ∧
    member array ⟨0, 0⟩ .nativeSource = .error .uninitialized ∧
    member array ⟨0, 240⟩ .nativeSource = .error .memoryValidity := ⟨by decide, by rfl', by rfl', by rfl'⟩

theorem partial_owner_declaration_rejects :
    member (Tests.substitute (.aggregate "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨224, 16⟩
      [(168, .object (.optionalScalar (.int true 64)))])) ⟨5, 0⟩ .astId = .error .unsupported := by rfl'

def cleared : State := (store debugInitialized (ptr .nativeSource) (sourceValue none)).toOption.getD debugInitialized
theorem clearing_preserves_other_members : sourceName cleared ⟨5, 0⟩ false = .ok none ∧
    member cleared ⟨5, 0⟩ .originSource = .ok (sourceValue (some (⟨100, 7⟩, 0))) ∧
    member cleared ⟨5, 0⟩ .nativeStart = .ok (.scalar (.int true 32 (-1))) ∧
    member cleared ⟨5, 0⟩ .astId = .ok (astValue (some (-1))) := ⟨by rfl', by rfl', by rfl', by rfl'⟩

end Compiler.Extraction.AssemblyItem.Fields.MemberTests
