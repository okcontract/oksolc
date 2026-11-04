/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExecution

namespace Compiler.ZigAir.MemoryExecutionTests
open Memory MemoryAir

private abbrev word : Ty := .scalar (.int false 32)
private abbrev pointer : Ty := .pointer true false word
private def number (n : Int) : Value := .scalar (.int false 32 n)
private def unitRef : Ref := .constant (.scalar .unit)
private def allocThen (next : Control.Code Ty Prim Ref true) (returnType : Ty := .scalar .unit) : Program true :=
  ⟨[], returnType, .bind 0 pointer (.alloc word) next⟩

private def caller : State :=
  ⟨[(0, ⟨8, word, [(0, number 5)], true, true⟩)], 1, 12⟩

private def callerAfter : State := { caller with nextId := 2, nextAddress := 16 }

theorem zero_budget_retains_valid_entry :
    (allocThen (.ret unitRef)).runFuel 0 [] {} =
      .suspended (.scalar .unit) 0 []
        ⟨.bind 0 pointer (.alloc word) (.ret unitRef), fun _ => none, {}, []⟩ := by rfl

theorem zero_budget_rejects_bad_arguments :
    (allocThen (.ret unitRef)).runFuel 0 [number 1] {} = .finished (.error .malformed) {} := by rfl

theorem invalid_heap_rejects_before_execution :
    (allocThen (.ret unitRef)).runFuel 10 [] { nextAddress := 2^64 + 1 } =
      .finished (.error .malformed) { nextAddress := 2^64 + 1 } := by rfl

theorem suspension_keeps_stack_allocation :
    ((allocThen (.ret unitRef)).runFuel 1 [] {}).state =
      ⟨[(0, ⟨8, word, [], true, true⟩)], 1, 12⟩ := by rfl

theorem return_cleans_only_current_invocation :
    (allocThen (.ret unitRef)).runFuel 2 [] caller = .finished (.ok (.scalar .unit)) callerAfter := by rfl

theorem resumption_keeps_original_mark :
    ((allocThen (.ret unitRef)).runFuel 1 [] caller).resume 1 =
      .finished (.ok (.scalar .unit)) callerAfter := by rfl

theorem return_type_failure_cleans_stack :
    (allocThen (.ret unitRef) (.scalar .bool)).runFuel 2 [] caller =
      .finished (.error .malformed) callerAfter := by rfl

theorem escaping_jump_cleans_stack :
    (allocThen (.jump 99 unitRef)).runFuel 2 [] caller =
      .finished (.error .malformed) callerAfter := by rfl

private def argumentAfterAllocation : Program true :=
  ⟨[word], word, .bind 0 pointer (.alloc word) (.bind 1 word (.argument 0) (.ret (.local 1)))⟩

theorem resumption_keeps_arguments :
    (argumentAfterAllocation.runFuel 1 [number 7] {}).resume 2 =
      .finished (.ok (number 7)) ⟨[], 1, 12⟩ := by rfl

private def effectThenFault : Program true :=
  ⟨[pointer], .scalar .unit,
    .bind 0 pointer (.argument 0)
      (.bind 1 (.scalar .unit) (.store (.local 0) (.constant (number 7)))
        (.bind 2 pointer (.alloc word) (.bind 3 word (.load (.local 2)) (.ret unitRef))))⟩

theorem fault_keeps_prior_effects_and_cleans_current_stack :
    effectThenFault.runFuel 4 [.pointer pointer ⟨0, 0⟩] caller =
      .finished (.error .uninitialized) ⟨[(0, ⟨8, word, [(0, number 7)], true, true⟩)], 2, 16⟩ := by rfl

private def spinning : Program true := allocThen (.loop rfl 1 (.repeat rfl 1))

theorem loop_suspension_keeps_stack :
    (spinning.runFuel 10 [] {}).state = ⟨[(0, ⟨8, word, [], true, true⟩)], 1, 12⟩ := by rfl

theorem loop_budget_is_not_a_fault :
    (match spinning.runFuel 10 [] {} with | .suspended .. => true | .finished .. => false) = true := by rfl

end Compiler.ZigAir.MemoryExecutionTests
