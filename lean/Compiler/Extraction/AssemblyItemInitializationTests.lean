/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemInitializers
import Compiler.Extraction.AssemblyItemMemberTests
import Compiler.Extraction.RepresentativeOperationTests

namespace Compiler.Extraction.AssemblyItem.Initializers.Tests
open Compiler.ZigAir.Memory Compiler.Algebraic Contract.Yul
open Fields

def debug : Values
  | .nativeStart => .scalar (.int true 32 (-1))
  | .nativeEnd => .scalar (.int true 32 17)
  | .nativeSource => MemberTests.sourceValue (some (⟨99, 2⟩, 3))
  | .originStart => .scalar (.int true 32 (-(2^31)))
  | .originEnd => .scalar (.int true 32 (2^31-1))
  | .originSource => MemberTests.sourceValue (some (⟨100, 7⟩, 0))
  | .astId => MemberTests.astValue (some (-1))
  | _ => .scalar (.int false 64 888)

theorem debug_valid : DebugTyped debug := by unfold DebugTyped; decide

def values := operation 254 debug
def before := Fields.Tests.created.memory

-- Independent expected complete contents. In particular, the oracle does not
-- enumerate `members`, so removing a member cannot remove it from the oracle.
def expectedCells : Cells := [
  (168, MemberTests.astValue (some (-1))), (144, MemberTests.sourceValue (some (⟨100, 7⟩, 0))),
  (164, .scalar (.int true 32 (2^31-1))), (160, .scalar (.int true 32 (-(2^31)))),
  (120, MemberTests.sourceValue (some (⟨99, 2⟩, 3))), (140, .scalar (.int true 32 17)),
  (136, .scalar (.int true 32 (-1))), (212, .scalar (.int true 32 0)), (200, .scalar (.int false 64 0)),
  (184, OptionalScalar.unsignedValue 64 none), (32, OptionalScalar.unsignedValue 256 none),
  (80, .optionalObject verbatimType ⟨40, 8⟩ none), (0, .scalar (.int false 256 0)),
  (216, OptionalScalar.byteValue (some 254)), (208, .scalar (.int true 32 1))]

def expected : State := { before with heap := before.heap.replace 5 { Creation.cell 320 with cells := expectedCells } }

theorem complete_execution : assign values 5 before = .ok expected := by rfl'
theorem complete_valid : expected.valid = true := by decide

theorem every_member : ∀ selected, member expected ⟨5, 0⟩ selected = .ok (values selected) := by
  intro selected
  cases selected <;> rfl'

def expectedDebug : ObjectValue := .fields [
  (0, .fields [(0, .leaf (MemberTests.sourceValue (some (⟨99, 2⟩, 3)))),
    (16, .leaf (.scalar (.int true 32 (-1)))), (20, .leaf (.scalar (.int true 32 17)))]),
  (24, .fields [(0, .leaf (MemberTests.sourceValue (some (⟨100, 7⟩, 0)))),
    (16, .leaf (.scalar (.int true 32 (-(2^31))))), (20, .leaf (.scalar (.int true 32 (2^31-1))))]),
  (48, .leaf (MemberTests.astValue (some (-1))))]

theorem complete_record_shape : objectValue values = .fields [
    (0, .leaf (.scalar (.int false 256 0))), (32, .leaf (OptionalScalar.unsignedValue 256 none)),
    (80, .leaf (.optionalObject verbatimType ⟨40, 8⟩ none)), (120, expectedDebug),
    (184, .leaf (OptionalScalar.unsignedValue 64 none)), (200, .leaf (.scalar (.int false 64 0))),
    (208, .leaf (.scalar (.int true 32 1))), (212, .leaf (.scalar (.int true 32 0))),
    (216, .leaf (OptionalScalar.byteValue (some 254)))] := rfl

theorem debug_identity_and_offset : debugValue values = debugValue debug ∧
    sourceName expected ⟨5, 0⟩ false = .ok (some (.leaf (.slice (.slice false (.scalar (.int false 8))) ⟨99, 2⟩ 3))) ∧
    sourceName expected ⟨5, 0⟩ true = .ok (some (.leaf (.slice (.slice false (.scalar (.int false 8))) ⟨100, 7⟩ 0))) ∧
    expected.heap.lookup 99 = none ∧ expected.heap.lookup 100 = none := ⟨rfl, by rfl', by rfl', rfl, rfl⟩

theorem all_values (rhs : Values) (typed : rhs.Typed) :
    ∃ after, assign rhs 5 before = .ok after ∧ Written rhs 5 members before after ∧
      ∀ selected, member after ⟨5, 0⟩ selected = .ok (rhs selected) :=
  assign_total rhs 5 before (Creation.cell 320) typed Fields.Tests.created_contract.2.valid.memory (by rfl') rfl rfl

theorem complete_frame : expected.heap.lookup 0 = before.heap.lookup 0 ∧
    expected.heap.lookup 4 = before.heap.lookup 4 ∧ expected.nextId = before.nextId ∧
    expected.nextAddress = before.nextAddress := ⟨by rfl', by rfl', rfl, rfl⟩

theorem overwrite_all_fields : assign values 5 MemberTests.debugInitialized = .ok expected := by rfl'

theorem zero_and_last_opcode : (operation 0 debug .instruction) = OptionalScalar.byteValue (some 0) ∧
    (operation 255 debug .instruction) = OptionalScalar.byteValue (some 255) ∧
    (constant 0 debug .instruction) = OptionalScalar.byteValue none := ⟨rfl, rfl, rfl⟩

theorem all_constant_words (value : Word) : (constant value debug).Typed ∧
    constant value debug .data = .scalar (.int false 256 value.toNat) :=
  ⟨constant_typed value debug debug_valid, (constant_arguments value debug).2.2.1⟩

theorem all_operation_bytes (opcode : Cache.Opcode) : (operation opcode debug).Typed ∧
    operation opcode debug .instruction = OptionalScalar.byteValue (some opcode) :=
  ⟨operation_typed opcode debug debug_valid, (operation_arguments opcode debug).2.1⟩

def invalidDebug (selected : Member) : Value := if selected = .astId then MemberTests.astValue (some (2^63)) else debug selected
theorem malformed_value_rejects : ¬DebugTyped invalidDebug ∧
    assign (operation 1 invalidDebug) 5 before = .error .malformed ∧
    assign (operation 1 invalidDebug) 5 (erase before 5) = .error .malformed ∧
    assign (fun selected => if selected = .verbatim then MemberTests.verbatimValue (some (.fields [])) else values selected)
      5 before = .error .malformed := ⟨by unfold DebugTyped; decide, by rfl', by rfl', by rfl'⟩

def withType (type : Ty) : State := { before with heap := before.heap.replace 5 { Creation.cell 320 with type } }

theorem complete_owner_required :
    assign values 5 (withType (.aggregate "wrong-owner" ⟨224, 16⟩
      (match viewType with | .aggregate _ _ fields => fields | _ => []))) = .error .unsupported ∧
    assign values 5 (withType (.aggregate "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨224, 16⟩
      [(208, .scalar (.int true 32))])) = .error .unsupported := ⟨by rfl', by rfl'⟩

theorem readonly_and_dead :
    assign values 5 { before with heap := before.heap.replace 5 { Creation.cell 320 with writable := false } } = .error .readOnly ∧
    assign values 5 (erase before 5) = .error .unallocated := ⟨by rfl', by rfl'⟩

theorem raw_enum_is_not_native_admission :
    Values.Typed (fun selected => if selected = .kind then Value.scalar (.int true 32 14) else values selected) ∧
    ¬((14 : Int) ∈ itemTagValues) := by
  refine ⟨?_, by decide⟩
  intro selected
  cases selected <;> decide

def graphBefore := RepresentativeArray.Operation.Tests.owned
def graphAfter : State :=
  { graphBefore with
    heap := graphBefore.heap.replace 0 { RepresentativeArray.Operation.Tests.item with cells := expectedCells } }

theorem graph_query_from_assignment : assign values 0 graphBefore = .ok graphAfter ∧
    RepresentativeArray.Operation.run graphAfter ⟨3, 0⟩ 0 254 =
      .ok (.ok (some (RepresentativeArray.Operation.borrowed ⟨1, 0⟩ 4))) ∧
    RepresentativeArray.Operation.run graphAfter ⟨3, 0⟩ 0 12 = .ok (.ok none) ∧
    graphAfter.heap.lookup 1 = graphBefore.heap.lookup 1 ∧ graphAfter.heap.lookup 2 = graphBefore.heap.lookup 2 :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def logical (item : Cache.Item) : Storage.Cell :=
  { item, otherValue := 0, itemAddress := 5, arguments := [], sequence := 0, argumentsAddress := 0 }

theorem initial_region : RegionAllocation.Fits Fields.Tests.initial.memory Creation.layout 320 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present old shaped
  have valid := ExpressionDeinit.Lifetime.Tests.initial_valid.memory
  simp only [State.valid, Bool.and_eq_true, List.all_eq_true] at valid
  have region := (valid.1.2 entry present).2
  simp only [shaped, Bool.and_eq_true, decide_eq_true_eq] at region
  exact Or.inr (Nat.le_trans region.1.2 (by decide))

theorem actual_creation_and_initialization (item : Cache.Item) (domain : (item.kind.toNat : Int) ∈ itemTagValues) :
    ∃ allocated after,
      Creation.create Fields.Tests.request 7 item Fields.Tests.initial = (.ok 5, allocated) ∧
      assign (construct item debug) 5 allocated.memory = .ok after ∧
      Written (construct item debug) 5 members allocated.memory after ∧
      Compiler.Extraction.Memory.Arguments.Normalization.Valid { allocated with memory := after } ∧
      Owned 7 5 { allocated with memory := after } ∧
      (∀ selected, member after ⟨5, 0⟩ selected = .ok (construct item debug selected)) ∧
      RepresentativeArray.Operation.Item after (logical item) :=
  create_initialize Fields.Tests.request 7 320 (logical item) debug Fields.Tests.initial 1
    ExpressionDeinit.Lifetime.Tests.initial_valid rfl initial_region domain debug_valid

theorem all_constant_creation (value : Word) :
    ∃ allocated after,
      Creation.create Fields.Tests.request 7 (Interner.constructorCode.constantRequest value).item Fields.Tests.initial =
        (.ok 5, allocated) ∧ assign (constant value debug) 5 allocated.memory = .ok after ∧
      RepresentativeArray.Operation.Item after (logical (Interner.constructorCode.constantRequest value).item) ∧
      Compiler.Extraction.Memory.Arguments.Normalization.Valid { allocated with memory := after } := by
  obtain ⟨allocated, after, created, assigned, _, valid, _, _, queried⟩ :=
    actual_creation_and_initialization (Interner.constructorCode.constantRequest value).item
      (by change (2 : Int) ∈ itemTagValues; decide)
  have sameValues : constant value debug = construct (Interner.constructorCode.constantRequest value).item debug := by
    funext selected
    cases selected <;> rfl
  rw [← sameValues] at assigned
  exact ⟨allocated, after, created, assigned, queried, valid⟩

theorem all_operation_creation (opcode : Cache.Opcode) :
    ∃ allocated after,
      Creation.create Fields.Tests.request 7 (Interner.constructorCode.operationRequest opcode []).item Fields.Tests.initial =
        (.ok 5, allocated) ∧ assign (operation opcode debug) 5 allocated.memory = .ok after ∧
      RepresentativeArray.Operation.Item after (logical (Interner.constructorCode.operationRequest opcode []).item) ∧
      Compiler.Extraction.Memory.Arguments.Normalization.Valid { allocated with memory := after } := by
  obtain ⟨allocated, after, created, assigned, _, valid, _, _, queried⟩ :=
    actual_creation_and_initialization (Interner.constructorCode.operationRequest opcode []).item
      (by change (1 : Int) ∈ itemTagValues; decide)
  have sameValues : operation opcode debug = construct (Interner.constructorCode.operationRequest opcode []).item debug := by
    funext selected
    cases selected <;> rfl
  rw [← sameValues] at assigned
  exact ⟨allocated, after, created, assigned, queried, valid⟩

end Compiler.Extraction.AssemblyItem.Initializers.Tests
