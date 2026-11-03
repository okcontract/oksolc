/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedMemory
import Compiler.ZigAir.GeneratedMemoryCells

namespace Compiler.ZigAir.MemoryTests
open Memory GeneratedMemory

def byte : Ty := .scalar (.int false 8)
def word32 : Ty := .scalar (.int false 32)
def pointer (writable many : Bool) (child : Ty) (id offset : Nat) : Value :=
  .pointer (.pointer writable many child) ⟨id, offset⟩
def number (n : Nat) : Value := .scalar (.int false 64 n)
def bytes : State := ⟨[(0, ⟨8, .array 16 byte, [], false, false⟩)], 1, 24⟩
def input : Value := pointer false true byte 0 0

theorem bounded_slice_success :
    (fn_bounded_slice.run [input, number 8, number 2, number 5] bytes).1 = .ok (number 3) := by rfl

/-- The allocation has sixteen bytes. The original slice has only two. -/
theorem original_view_bounds_are_required :
    (fn_bounded_slice.run [input, number 2, number 0, number 4] bytes).1 = .error .sourceBounds := by rfl

theorem untaken_slice_is_not_checked :
    (fn_conditional_slice.run [input, number 2, number 4, .scalar (.bool false)] bytes).1 = .ok (number 0) := by rfl

theorem taken_slice_is_checked :
    (fn_conditional_slice.run [input, number 2, number 4, .scalar (.bool true)] bytes).1 = .error .sourceBounds := by rfl

theorem taken_slice_success :
    (fn_conditional_slice.run [input, number 8, number 5, .scalar (.bool true)] bytes).1 = .ok (number 5) := by rfl

theorem constant_result_keeps_source_guard :
    (fn_constant_length.run [input, number 2] bytes).1 = .error .sourceBounds := by rfl

theorem unused_result_keeps_source_guard :
    (fn_unused_slice.run [input, number 2, number 4] bytes).1 = .error .sourceBounds := by rfl

theorem unused_slice_success :
    (fn_unused_slice.run [input, number 2, number 1] bytes).1 = .ok (number 1) := by rfl

theorem constant_length_success :
    (fn_constant_length.run [input, number 4] bytes).1 = .ok (number 4) := by rfl

theorem unbounded_constant_length_success :
    (fn_unbounded_constant_length.run [input] bytes).1 = .ok (number 4) := by rfl

theorem unbounded_constant_length_checks_memory :
    let short : State := ⟨[(0, ⟨8, .array 2 byte, [], false, false⟩)], 1, 16⟩
    (fn_unbounded_constant_length.run [input] short).1 = .error .memoryValidity := by rfl

theorem static_array_bound_success :
    (fn_array_slice.run [pointer false false (.array 16 byte) 0 0, number 2, number 5] bytes).1 =
      .ok (number 3) := by rfl

theorem memory_extent_is_also_required :
    (fn_bounded_slice.run [input, number 17, number 0, number 1] bytes).1 = .error .memoryValidity := by rfl

theorem cleanup_on_success :
    (fn_bounded_slice.run [input, number 8, number 2, number 5] bytes).2.heap = bytes.heap := by rfl

theorem cleanup_on_failure :
    (fn_bounded_slice.run [input, number 2, number 0, number 4] bytes).2.heap = bytes.heap := by rfl

def cell : State := ⟨[(0, ⟨8, word32, [(0, .scalar (.int false 32 1))], true, false⟩)], 1, 16⟩

theorem generated_store_load :
    let result := fn_load_store.run [pointer true false word32 0 0, .scalar (.int false 32 7)] cell
    result.1 = .ok (.scalar (.int false 32 7)) ∧
      load result.2 (pointer false false word32 0 0) = .ok (.scalar (.int false 32 7)) := by constructor <;> rfl

def mutableSliceCell : State := ⟨[(1, ⟨24, .slice true byte, (Value.slice (.slice true byte) ⟨0, 0⟩ 2).leaves, true, false⟩),
  (0, ⟨8, .array 16 byte, [], true, false⟩)], 2, 40⟩

theorem generated_slice_field_alias :
    let result := fn_slice_fields.run [pointer true false (.slice true byte) 1 0, number 4] mutableSliceCell
    result.1 = .ok (pointer true true byte 0 0) ∧
      load result.2 (pointer false false (.slice true byte) 1 0) =
        .ok (.slice (.slice true byte) ⟨0, 0⟩ 4) := by constructor <;> rfl

theorem generated_pointer_subtraction :
    let state : State := ⟨[(0, ⟨8, .array 4 word32, [], true, false⟩)], 1, 24⟩
    (fn_move_back.run [pointer true true word32 0 8, number 1] state).1 =
      .ok (pointer true true word32 0 4) := by rfl

theorem generated_pointer_subtraction_rejects_provenance :
    let state : State := ⟨[(0, ⟨8, .array 4 word32, [], true, false⟩)], 1, 24⟩
    (fn_move_back.run [pointer true true word32 0 8, number 3] state).1 = .error .memoryValidity := by rfl

theorem lifetime_is_not_reused :
    (fn_bounded_slice.run [input, number 2, number 0, number 4] bytes).2.nextId = 3 := by rfl

theorem read_after_cleanup_rejects :
    load (fn_bounded_slice.run [input, number 8, number 2, number 5] bytes).2
      (pointer false false (.pointer false true byte) 1 0) = .error .unallocated := by rfl

theorem uninitialized_load_rejects :
    load ⟨[(0, ⟨8, word32, [], true, false⟩)], 1, 16⟩ (pointer false false word32 0 0) =
      .error .uninitialized := by rfl

theorem array_uninitialized_rejects :
    load bytes (pointer false false byte 0 0) = .error .uninitialized := by rfl

theorem partial_slice_initialization_is_retained :
    writeCell ⟨8, .slice true byte, [], true, true⟩ 8 (.scalar (.int false 64 4)) =
      .ok ⟨8, .slice true byte, [(8, .scalar (.int false 64 4))], true, true⟩ := by rfl

theorem unaligned_load_rejects :
    load cell (pointer false false word32 0 1) = .error .memoryValidity := by rfl

theorem const_write_rejects :
    store cell (pointer false false word32 0 0) (.scalar (.int false 32 7)) = .error .readOnly := by rfl

theorem allocation_readonly_rejects :
    store { cell with heap := [(0, ⟨8, word32, [(0, .scalar (.int false 32 1))], false, false⟩)] }
      (pointer true false word32 0 0) (.scalar (.int false 32 7)) = .error .readOnly := by rfl

theorem physical_wrap_is_distinct :
    offsetPointer bytes false input addressLimit = .error (.scalar .illegalBehavior) := by rfl

theorem provenance_failure_is_distinct :
    offsetPointer bytes false input 17 = .error .memoryValidity := by rfl

theorem last_byte_is_representable :
    let state : State := ⟨[(0, ⟨addressLimit - 1, byte, [(0, .scalar (.int false 8 7))], false, false⟩)], 1, addressLimit⟩
    load state (pointer false false byte 0 0) = .ok (.scalar (.int false 8 7)) := by rfl

theorem unrepresentable_empty_pointer_rejects :
    let state : State := ⟨[(0, ⟨addressLimit - 1, .array 1 byte, [], false, false⟩)], 1, addressLimit⟩
    makeSlice state (.slice false byte) (pointer false true byte 0 1) 0 = .error .memoryValidity := by rfl

theorem explicit_resource_exhaustion :
    allocate ⟨[], 0, addressLimit - 4⟩ word32 = .error .outOfMemory := by rfl

def buffer : State := ⟨[(0, ⟨8, .array 4 word32, [], true, false⟩)], 1, 24⟩
def bufferPointer : Value := pointer true true word32 0 0

theorem generated_buffer_alias :
    let result := fn_buffer_alias.run [bufferPointer, number 0, .scalar (.int false 32 3), .scalar (.int false 32 7)] buffer
    result.1 = .ok (.scalar (.int false 32 7)) ∧
      load result.2 (pointer false false word32 0 0) = .ok (.scalar (.int false 32 7)) := by constructor <;> rfl

theorem generated_buffer_separation :
    let result := fn_buffer_alias.run [bufferPointer, number 1, .scalar (.int false 32 3), .scalar (.int false 32 7)] buffer
    result.1 = .ok (.scalar (.int false 32 3)) ∧
      load result.2 (pointer false false word32 0 4) = .ok (.scalar (.int false 32 7)) := by constructor <;> rfl

theorem unwritten_buffer_element_rejects :
    let result := fn_buffer_alias.run [bufferPointer, number 1, .scalar (.int false 32 3), .scalar (.int false 32 7)] buffer
    load result.2 (pointer false false word32 0 8) = .error .uninitialized := by rfl

theorem buffer_view_bound_rejects :
    (fn_buffer_alias.run [bufferPointer, number 4, .scalar (.int false 32 3), .scalar (.int false 32 7)] buffer).1 =
      .error .memoryValidity := by rfl

def emptySliceCell : State := { mutableSliceCell with heap :=
  [(1, ⟨24, .slice true byte, [], true, false⟩), (0, ⟨8, .array 16 byte, [], true, false⟩)] }

theorem generated_slice_initialization :
    let result := fn_initialize_slice.run
      [pointer true false (.slice true byte) 1 0, pointer true true byte 0 0, number 4] emptySliceCell
    result.1 = .ok (.scalar .unit) ∧ load result.2 (pointer false false (.slice true byte) 1 0) =
      .ok (.slice (.slice true byte) ⟨0, 0⟩ 4) := by constructor <;> rfl

theorem generated_slice_overwrite :
    let result := fn_initialize_slice.run
      [pointer true false (.slice true byte) 1 0, pointer true true byte 0 0, number 4] mutableSliceCell
    result.1 = .ok (.scalar .unit) ∧ load result.2 (pointer false false (.slice true byte) 1 0) =
      .ok (.slice (.slice true byte) ⟨0, 0⟩ 4) := by constructor <;> rfl

theorem generated_partial_length :
    let result := fn_initialize_length.run [pointer true false (.slice true byte) 1 0, number 4] emptySliceCell
    result.1 = .ok (number 4) ∧ load result.2 (pointer false false (.slice true byte) 1 0) =
      .error .uninitialized := by constructor <;> rfl

theorem generated_length_existing :
    let result := fn_initialize_length.run [pointer true false (.slice true byte) 1 0, number 4] mutableSliceCell
    result.1 = .ok (number 4) ∧ load result.2 (pointer false false (.slice true byte) 1 0) =
      .ok (.slice (.slice true byte) ⟨0, 0⟩ 4) := by constructor <;> rfl

theorem pointer_field_initializes_independently :
    let result := store emptySliceCell (pointer true false (.pointer true true byte) 1 0) (pointer true true byte 0 0)
    result >>= (fun state => load state (pointer false false (.pointer true true byte) 1 0)) =
      .ok (pointer true true byte 0 0) := by rfl

theorem array_of_slices_aliases :
    let state : State := ⟨[(0, ⟨8, .array 2 (.slice true byte), [], true, false⟩)], 1, 40⟩
    let result := store state (pointer true false (.slice true byte) 0 16) (.slice (.slice true byte) ⟨1, 0⟩ 2)
    result >>= (fun state => load state (pointer false false usize 0 24)) = .ok (number 2) := by rfl

theorem nested_array_element :
    let state : State := ⟨[(0, ⟨8, .array 2 (.array 3 word32), [], true, false⟩)], 1, 32⟩
    let result := store state (pointer true false word32 0 20) (.scalar (.int false 32 7))
    result >>= (fun state => load state (pointer false false word32 0 20)) = .ok (.scalar (.int false 32 7)) := by rfl

theorem array_whole_value_remains_unsupported :
    load buffer (pointer false false (.array 4 word32) 0 0) = .error .unsupported := by rfl

theorem zero_stride_element_remains_unsupported :
    leafType (.array 2 (.scalar .unit)) 0 = none := by rfl

theorem misaligned_leaf_is_not_a_subobject :
    Cells.readLeaf [] (.array 2 word32) 1 word32 = .error .unsupported := by rfl

theorem outside_leaf_state_rejects :
    State.valid ⟨[(0, ⟨8, .array 2 word32, [(8, .scalar (.int false 32 7))], true, false⟩)], 1, 16⟩ = false := by rfl

theorem duplicate_leaf_state_rejects :
    State.valid ⟨[(0, ⟨8, word32, [(0, .scalar (.int false 32 7)), (0, .scalar (.int false 32 3))], true, false⟩)], 1, 16⟩ =
      false := by rfl

theorem wrong_leaf_type_rejects :
    State.valid ⟨[(0, ⟨8, word32, [(0, .scalar (.int false 8 7))], true, false⟩)], 1, 16⟩ = false := by rfl

end Compiler.ZigAir.MemoryTests
