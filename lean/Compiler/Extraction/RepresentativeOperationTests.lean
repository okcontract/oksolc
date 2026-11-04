/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeOperationProofs
import Compiler.Extraction.ExpressionFieldTests
import Compiler.ZigAir.MemoryRelease

namespace Compiler.Extraction.RepresentativeArray.Operation.Tests
open Compiler.ZigAir.Memory Compiler.Algebraic

def item (kind : Int := 1) (instruction : Option (Option (BitVec 8)) := some (some 12)) : Allocation :=
  ⟨32, AssemblyItem.viewType,
    [(AssemblyItem.item_typeOffset, .scalar (.int true 32 kind))] ++
      (instruction.toList.map fun value => (AssemblyItem.instruction_valueOffset, OptionalScalar.byteValue value)), true, false⟩

def descriptor (arguments : Option Value := some Expression.Tests.arguments) : Allocation :=
  ⟨512, .array 1 Expression.allocationType,
    Expression.Tests.item.leaves Expression.itemOffset ++
      (arguments.toList.flatMap fun value => value.leaves Expression.argumentsOffset) ++
      [(Expression.idOffset, .scalar (.int false 32 0)), (Expression.sequence_numberOffset, .scalar (.int false 32 23))], true, false⟩

def header (length : Nat := 1) : Allocation :=
  ⟨544, allocationType, (Value.slice itemsType ⟨2, 0⟩ length).leaves itemsOffset ++
    [(capacityOffset, .scalar (.int false 64 1))], true, false⟩

def state (kind : Int := 1) (instruction : Option (Option (BitVec 8)) := some (some 12))
    (arguments : Option Value := some Expression.Tests.arguments) : State :=
  ⟨[(3, header), (2, descriptor arguments), (1, Expression.Tests.argumentsAllocation), (0, item kind instruction)], 4, 568⟩

def query (memory : State := state) (id : NodeId := 0) (opcode : BitVec 8 := 12) := run memory ⟨3, 0⟩ id opcode

theorem initial_valid : state.valid = true := by decide
theorem offset_descriptor : query = .ok (.ok (some (borrowed ⟨1, 4⟩ 2))) := by rfl'
theorem readonly_return : query = .ok (.ok (some (.slice (.slice false Expression.idType) ⟨1, 4⟩ 2))) := by rfl'
theorem original_unsorted_contents :
    (do let .ok (some view) ← query | .error .malformed
        let first ← sliceElementPointer state view 0
        let second ← sliceElementPointer state view 1
        return [← load state first, ← load state second]) =
      .ok [.scalar (.int false 32 99), .scalar (.int false 32 1)] := by rfl'
theorem readonly_cannot_store :
    (do let .ok (some view) ← query | .error .malformed
        let first ← sliceElementPointer state view 0
        store state first (.scalar (.int false 32 8))) = .error .readOnly := by rfl'
theorem original_bound :
    (do let .ok (some view) ← query | .error .malformed
        sliceElementPointer state view 2) = .error .sourceBounds := by rfl'

theorem invalid_id_skips_backing : query (erase (erase state 2) 0) 1 = .ok (.ok none) := by rfl'
theorem empty_header_skips_backing : query { state with heap := [(3, header 0)] } = .ok (.ok none) := by rfl'
theorem nonoperation_skips_optional_and_arguments : query (state 2 none none) = .ok (.ok none) := by rfl'
theorem null_operation_fault : query (state 1 (some none) none) = .ok (.error .invalidOptional) := by rfl'
theorem missing_optional_fault : query (state 1 none none) = .error .uninitialized := by rfl'
theorem opcode_miss_skips_arguments : query (state 1 (some (some 12)) none) 0 13 = .ok (.ok none) := by rfl'
theorem matching_missing_arguments_fault : query (state 1 (some (some 12)) none) = .error .uninitialized := by rfl'
theorem zero_is_an_opcode : query (state 1 (some (some 0))) 0 0 = .ok (.ok (some (borrowed ⟨1, 4⟩ 2))) := by rfl'
theorem last_opcode : query (state 1 (some (some 255))) 0 255 = .ok (.ok (some (borrowed ⟨1, 4⟩ 2))) := by rfl'
theorem empty_descriptor_identity : query (state 1 (some (some 12)) (some (.slice Expression.argumentsType ⟨999, 28⟩ 0))) =
    .ok (.ok (some (borrowed ⟨999, 28⟩ 0))) := by rfl'
theorem query_does_not_read_operands : query (erase state 1) = .ok (.ok (some (borrowed ⟨1, 4⟩ 2))) := by rfl'
theorem stale_item_fault : query (erase state 0) = .error .unallocated := by rfl'
theorem stale_backing_fault : query (erase state 2) = .error .unallocated := by rfl'
theorem invalid_tag_fault : query (state 14) = .error .malformed := by rfl'
theorem id_and_sequence_are_not_read : query { state with heap := state.heap.replace 2 ({ descriptor with cells := (descriptor).cells.filter (fun slot => slot.1 < 24) }) } =
      .ok (.ok (some (borrowed ⟨1, 4⟩ 2))) := by rfl'

/-- A root-owned row exercises the universal correspondence theorem. Offset
views above exercise physical return identity independently of that invariant. -/
def owned : State := state 1 (some (some 12)) (some (.slice Expression.argumentsType ⟨1, 0⟩ 4))
def cell : Storage.Cell := ⟨⟨1, some 12, 0⟩, 0, 0, [777, 99, 1, 5], 23, 1⟩
theorem owned_valid : owned.valid = true := by decide
theorem owned_row : DescriptorRelation.Row owned 2 0 cell := by rfl'
theorem owned_item : Item owned cell := ⟨by rfl', fun _ => by rfl'⟩
theorem all_ids_and_opcodes (id : NodeId) (opcode : BitVec 8) :
    query owned id opcode = .ok ((Storage.operationProgram.run [cell] id opcode).map (Option.map returned)) := by
  apply Operation.query owned ⟨3, 0⟩ 2 1 (descriptor (some (.slice Expression.argumentsType ⟨1, 0⟩ 4))) [cell] id opcode
    owned_valid (by rfl') (by rfl') rfl rfl (by decide)
  · intro index value found
    cases index with
    | zero => cases Option.some.inj found; exact owned_row
    | succ index => simp at found
  · intro value member
    simp only [List.mem_singleton] at member
    subst value; exact owned_item

end Compiler.Extraction.RepresentativeArray.Operation.Tests
