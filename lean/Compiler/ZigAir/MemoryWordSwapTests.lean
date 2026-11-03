/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedWordSwap
import Compiler.ZigAir.MemoryByteExchangeTests

/-! Complete captured-loop observations and universal entry-contract laws.
The finite executions below do not establish universal loop refinement. -/
namespace Compiler.ZigAir.MemoryWordSwap.Tests
open Memory MemoryAir GeneratedMemory
open Memory.ByteExchange.Tests (caller view items expected writable represented)

def args : List Value := [view.pointer 0, view.pointer 1]

theorem contract_witness : WordPair.validate caller args = .ok () :=
  WordPair.validate_view caller view items 0 1 WordByteView.Tests.valid_caller writable represented
    (by decide) (by decide) (by decide)

theorem preserves_valid (fuel : Nat) (args : List Value) (state : State) (initial : state.valid = true) :
    (fn_swap_u32.runFuel fuel args state).state.valid = true :=
  fn_swap_u32.preserves_valid fuel args state initial

theorem complete_swap : fn_swap_u32.runFuel 160 args caller =
    .finished (.ok (.scalar .unit)) { expected with nextId := 2, nextAddress := 40 } := by rfl'

theorem reversed_swap : fn_swap_u32.runFuel 160 args.reverse caller =
    .finished (.ok (.scalar .unit))
      ⟨[(0, { WordByteView.Tests.cell 305419896 with cells :=
        [(0, WordArray.number 305419896), (4, WordArray.number 3735928559), (8, WordArray.number 3131961357)] })],
        2, 40⟩ := by rfl'

theorem aliases_reject : fn_swap_u32.runFuel 160 [view.pointer 0, view.pointer 0] caller =
    .finished (.error .memoryValidity) caller := by rfl'

theorem unaligned_reject : fn_swap_u32.runFuel 160
    [view.pointer 0, .pointer (.pointer true false WordArray.word) ⟨0, 2⟩] caller =
    .finished (.error .memoryValidity) caller := by rfl'

theorem uninitialized_reject : fn_swap_u32.runFuel 160 args WordByteView.Tests.empty =
    .finished (.error .uninitialized) WordByteView.Tests.empty := by rfl'

theorem readonly_reject : fn_swap_u32.runFuel 160 args WordByteView.Tests.readonly =
    .finished (.error .readOnly) WordByteView.Tests.readonly := by rfl'

theorem dead_reject : fn_swap_u32.runFuel 160 args {} = .finished (.error .unallocated) {} := by rfl'

theorem malformed_reject : fn_swap_u32.runFuel 160 [] caller = .finished (.error .malformed) caller := by rfl'

def exhausted : State := { caller with nextAddress := addressLimit }
theorem allocation_exhausted : fn_swap_u32.runFuel 160 args exhausted =
    .finished (.error .outOfMemory) exhausted := by rfl'

theorem suspended_stack : (fn_swap_u32.runFuel 12 args caller).state.heap.map Prod.fst = [1, 0] := by rfl'

theorem resumed_swap : (fn_swap_u32.runFuel 12 args caller).resume 148 =
    .finished (.ok (.scalar .unit)) { expected with nextId := 2, nextAddress := 40 } := by
  rw [WordPairProgram.resume_add]
  exact complete_swap

end Compiler.ZigAir.MemoryWordSwap.Tests
