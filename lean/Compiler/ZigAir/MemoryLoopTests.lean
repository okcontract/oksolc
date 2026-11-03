/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedMemoryLoops
import Compiler.ZigAir.MemoryExecutionProofs

/-! Executable observations of captured loop programs. These cases include
overlapping buffers, labelled continues, suspension and partial effects on
failure. They are finite model checks, not universal loop functional proofs. -/
namespace Compiler.ZigAir.MemoryLoopTests
open Memory MemoryAir GeneratedMemory

private abbrev word : Ty := .scalar (.int false 32)
private def number (n : Int) : Value := .scalar (.int false 32 n)
private def size (n : Nat) : Value := .scalar (.int false 64 n)
private def pointer (writable : Bool := true) (offset : Nat := 0) : Value :=
  .pointer (.pointer writable true word) ⟨0, offset⟩

private def words (values : List Int) : State :=
  ⟨[(0, ⟨8, .array values.length word,
    values.zipIdx |>.map (fun (value, index) => (4 * index, number value)), true, false⟩)],
    1, 8 + 4 * values.length⟩

/-- Include termination, every observable word, live allocation identities and
allocator cursors. An exhausted budget is distinct from every terminal result. -/
private def observe (count : Nat) : Invocation →
    Option (Except Fault Value × List (Except Fault Value) × List Nat × Nat × Nat)
  | .suspended .. => none
  | .finished result state => some (result,
      (List.range count).map (fun index => Memory.load state (.pointer (.pointer false false word) ⟨0, 4 * index⟩)),
      state.heap.map Prod.fst, state.nextId, state.nextAddress)

private def expected (values : List Int) (nextId nextAddress : Nat)
    (result : Except Fault Value := .ok (.scalar .unit)) :
    Option (Except Fault Value × List (Except Fault Value) × List Nat × Nat × Nat) :=
  some (result, values.map (fun n => Except.ok (number n)), [0], nextId, nextAddress)

private def fill (length : Nat) :=
  fn_fill.runFuel 160 [pointer, size length, number 9] (words [1, 2, 3, 4, 5])

theorem fill_zero : observe 5 (fill 0) = expected [1, 2, 3, 4, 5] 3 48 := by rfl'
theorem fill_one : observe 5 (fill 1) = expected [9, 2, 3, 4, 5] 3 48 := by rfl'
theorem fill_all : observe 5 (fill 5) = expected [9, 9, 9, 9, 9] 3 48 := by rfl'

private def copy (destination source length : Nat) :=
  fn_copy_forward.runFuel 200 [pointer true (4 * destination), pointer false (4 * source), size length]
    (words [1, 2, 3, 4, 5])

theorem copy_zero : observe 5 (copy 1 0 0) = expected [1, 2, 3, 4, 5] 4 56 := by rfl'
theorem copy_same : observe 5 (copy 0 0 5) = expected [1, 2, 3, 4, 5] 4 56 := by rfl'
theorem copy_forward_overlap : observe 5 (copy 1 0 4) = expected [1, 1, 1, 1, 1] 4 56 := by rfl'
theorem copy_backward_overlap : observe 5 (copy 0 1 4) = expected [2, 3, 4, 5, 5] 4 56 := by rfl'

private def nested (rows columns stop : Nat) :=
  fn_nested_continue.runFuel 240 [pointer, size rows, size columns, size stop, number 9]
    (words [1, 1, 1, 1, 1, 1])

theorem nested_no_rows : observe 6 (nested 0 3 1) = expected [1, 1, 1, 1, 1, 1] 4 56 := by rfl'
theorem nested_no_columns : observe 6 (nested 2 0 1) = expected [1, 1, 1, 1, 1, 1] 4 56 := by rfl'
theorem nested_immediate : observe 6 (nested 2 3 0) = expected [1, 1, 1, 1, 1, 1] 4 56 := by rfl'
theorem nested_continue : observe 6 (nested 2 3 1) = expected [9, 1, 1, 9, 1, 1] 4 56 := by rfl'
theorem nested_full : observe 6 (nested 2 3 3) = expected [9, 9, 9, 9, 9, 9] 4 56 := by rfl'

theorem fill_fault_keeps_prefix :
    observe 5 (fill 6) = expected [9, 9, 9, 9, 9] 3 48 (.error .memoryValidity) := by rfl'

theorem indexed_pointer_requires_complete_element :
    elementPointer (words [1]) (pointer) 1 = .error .memoryValidity := by rfl

theorem indexed_pointer_preserves_readonly :
    elementPointer (words [1, 2]) (pointer false) 1 =
      .ok (.pointer (.pointer false false word) ⟨0, 4⟩) := by rfl

theorem fill_zero_does_not_dereference (address : Address) :
    fn_fill.runFuel 32 [.pointer (.pointer true true word) address, size 0, number 9] {} =
      .finished (.ok (.scalar .unit)) ⟨[], 2, 24⟩ := by rfl'

theorem fill_dead_pointer_fault_cleans_stack :
    fn_fill.runFuel 32 [.pointer (.pointer true true word) ⟨99, 0⟩, size 1, number 9] {} =
      .finished (.error .unallocated) ⟨[], 2, 24⟩ := by rfl

theorem fill_suspends_with_stack :
    (fn_fill.runFuel 10 [pointer, size 5, number 9] (words [1, 2, 3, 4, 5])).state.heap.map Prod.fst =
      [2, 1, 0] := by rfl'

theorem fill_resumes (a b : Nat) (args : List Value) (state : State) :
    (fn_fill.runFuel a args state).resume b = fn_fill.runFuel (a + b) args state :=
  (Invocation.resume_add a b (fn_fill.start args state)).symm

end Compiler.ZigAir.MemoryLoopTests
