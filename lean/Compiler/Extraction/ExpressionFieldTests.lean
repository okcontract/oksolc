/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionFields

namespace Compiler.Extraction.Expression.Tests
open Compiler.ZigAir.Memory

deriving instance DecidableEq for Except

def item : Value := .pointer itemType ⟨0, 0⟩
def arguments : Value := .slice argumentsType ⟨1, 4⟩ 2
def id : Value := .scalar (.int false 32 17)
def sequence : Value := .scalar (.int false 32 23)
def cells : Cells := item.leaves itemOffset ++ arguments.leaves argumentsOffset ++
  id.leaves idOffset ++ sequence.leaves sequence_numberOffset
def itemAllocation : Allocation := ⟨32, Compiler.Extraction.AssemblyItem.allocationType, [], true, false⟩
def argumentsAllocation : Allocation := ⟨256, .array 4 idType,
  [(0, .scalar (.int false 32 777)), (4, .scalar (.int false 32 99)),
   (8, .scalar (.int false 32 1)), (12, .scalar (.int false 32 5))], true, false⟩
def descriptor (contents : Cells := cells) (type : Ty := allocationType) (stack : Bool := false) : Allocation :=
  ⟨512, type, contents, true, stack⟩
def memory (contents : Cells := cells) (type : Ty := allocationType) (stack : Bool := false) : State :=
  ⟨[(2, descriptor contents type stack), (1, argumentsAllocation), (0, itemAllocation)], 3, 544⟩

theorem complete_valid : (memory).valid = true := by decide

theorem complete_fields : readFields memory false ⟨2, 0⟩ = .ok [item, arguments, id, sequence] := by decide

theorem source_field_read : readField memory false ⟨2, 0⟩ argumentsOffset =
    load memory (.pointer (.pointer false false argumentsType) ⟨2, 8⟩) :=
  read_from_root memory 2 (descriptor) argumentsOffset argumentsType false complete_valid (by decide) rfl
    field_types_checked.2.1

theorem unsorted_offset_borrow :
    (do let view ← readField memory false ⟨2, 0⟩ argumentsOffset
        let first ← sliceElementPointer memory view 0
        let second ← sliceElementPointer memory view 1
        return [← load memory first, ← load memory second]) =
      .ok [.scalar (.int false 32 99), .scalar (.int false 32 1)] := by decide

theorem original_slice_bound : sliceElementPointer memory arguments 2 = .error .sourceBounds := by decide

theorem item_allocation_identity : readField memory false ⟨2, 0⟩ itemOffset = .ok item := by decide

theorem uninitialized_fields_reject : readFields (memory []) false ⟨2, 0⟩ = .error .uninitialized := by decide

theorem partial_slice_reject :
    readField (memory (item.leaves itemOffset ++ [(8, .pointer (.pointer true true idType) ⟨1, 4⟩)]))
      false ⟨2, 0⟩ argumentsOffset = .error .uninitialized := by decide

theorem missing_id_is_not_defaulted :
    readFields (memory (item.leaves itemOffset ++ arguments.leaves argumentsOffset ++
      sequence.leaves sequence_numberOffset)) false ⟨2, 0⟩ = .error .uninitialized := by decide

theorem wrong_leaf_type_rejects : readField (memory [(0, .scalar (.int false 64 0))])
    false ⟨2, 0⟩ itemOffset = .error .malformed := by decide

theorem wrong_leaf_state_invalid : (memory [(0, .scalar (.int false 64 0))]).valid = false := by decide

theorem duplicate_leaf_state_invalid : (memory (cells ++ [(24, id)])).valid = false := by decide

def badType (fields : List (Nat × Field)) (layout : Layout := ⟨32, 8⟩) : Ty := .aggregate "bad" layout fields

theorem overlapping_fields_reject : allocate {} (badType [(0, .slice true (.int false 32)),
    (8, .scalar (.int false 32))]) = .error .unsupported := by decide

theorem field_extent_rejects : allocate {} (badType [(32, .scalar (.int false 32))]) = .error .unsupported := by decide

theorem misaligned_field_rejects : allocate {} (badType [(4, .slice true (.int false 32))]) = .error .unsupported := by decide

theorem parent_alignment_rejects : allocate {} (badType [(0, .slice true (.int false 32))] ⟨32, 4⟩) =
    .error .unsupported := by decide

theorem same_extent_different_owner_rejects : readField (memory [] (.array 8 idType)) false ⟨2, 0⟩ itemOffset =
    .error .unsupported := by decide

theorem interior_bytes_are_not_fields : readField memory false ⟨2, 0⟩ 4 = .error .unsupported := by decide

theorem full_parent_extent_is_required : readField memory false ⟨2, 8⟩ itemOffset = .error .memoryValidity := by decide

theorem const_field_store_rejects :
    (do let field ← fieldPointer memory (.pointer (.pointer false false allocationType) ⟨2, 0⟩) idOffset
        store memory field id) = .error .readOnly := by decide

theorem whole_record_load_remains_unsupported : load memory (.pointer (.pointer false false allocationType) ⟨2, 0⟩) =
    .error .unsupported := by decide

theorem cleanup_rejects_stale_descriptor : readField (cleanup 2 (memory cells allocationType true))
    false ⟨2, 0⟩ argumentsOffset = .error .unallocated := by decide

theorem cleanup_keeps_independent_operands : load (cleanup 2 (memory cells allocationType true))
    (.pointer (.pointer false false idType) ⟨1, 4⟩) = .ok (.scalar (.int false 32 99)) := by decide

def reused : State := ⟨[(3, descriptor), (1, argumentsAllocation), (0, itemAllocation)], 4, 544⟩

theorem address_reuse_keeps_lifetime : readFields reused false ⟨3, 0⟩ = .ok [item, arguments, id, sequence] ∧
    readFields reused false ⟨2, 0⟩ = .error .unallocated := by decide

def arrayMemory : State := ⟨[(2, ⟨512, .array 2 allocationType,
  cells ++ cells.map (fun (offset, value) => (offset + 32, value)), true, false⟩),
  (1, argumentsAllocation), (0, itemAllocation)], 3, 576⟩

theorem array_descriptor_field_read : arrayMemory.valid = true ∧
    readFields arrayMemory false ⟨2, 32⟩ = .ok [item, arguments, id, sequence] := by decide

def initializedItem : State := { memory [] with heap := (memory []).heap.replace 2 (descriptor (item.leaves itemOffset)) }

theorem item_store_initializes_only_item :
    (do let field ← fieldPointer (memory []) (.pointer (.pointer true false allocationType) ⟨2, 0⟩) itemOffset
        store (memory []) field item) = .ok initializedItem ∧
    readField initializedItem false ⟨2, 0⟩ itemOffset = .ok item ∧
    readField initializedItem false ⟨2, 0⟩ argumentsOffset = .error .uninitialized := by decide

theorem independent_field_overwrites :
    (do let idField ← fieldPointer memory (.pointer (.pointer true false allocationType) ⟨2, 0⟩) idOffset
        let withId ← store memory idField (.scalar (.int false 32 19))
        let sequenceField ← fieldPointer withId (.pointer (.pointer true false allocationType) ⟨2, 0⟩) sequence_numberOffset
        let after ← store withId sequenceField (.scalar (.int false 32 29))
        readFields after false ⟨2, 0⟩) =
      .ok [item, arguments, .scalar (.int false 32 19), .scalar (.int false 32 29)] := by decide

theorem store_readback_from_execution (state after : State) (cell : Allocation) (lifetime : Nat) (value : Value)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell) (typed : cell.type = allocationType)
    (stored : store state (.pointer (.pointer true false argumentsType) ⟨lifetime, argumentsOffset⟩) value = .ok after) :
    readField after true ⟨lifetime, 0⟩ argumentsOffset = .ok value := by
  apply read_after_store state after true ⟨lifetime, 0⟩ argumentsOffset _ value _ stored
  exact root_selector state lifetime cell argumentsOffset argumentsType true initial found typed field_types_checked.2.1

end Compiler.Extraction.Expression.Tests
