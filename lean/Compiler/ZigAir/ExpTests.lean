/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedExp
import Compiler.ZigAir.MemoryExecutionProofs

/-! Finite observations of actual production AIR, with complete result/heap/
cursor comparisons. Universal exponentiation correctness remains a separate
obligation. Native observations are compared by the acceptance harness. -/
namespace Compiler.ZigAir.ExpTests
open Memory MemoryAir GeneratedMemory

def word (n : Int) : Value := .scalar (.int false 256 n)
def call (base exponent : Int) : Invocation := fn_exp256.runFuel 400 [word base, word exponent] {}
def expected (n : Int) : Invocation := .finished (.ok (word n)) ⟨[], 3, 112⟩

theorem zero_zero : call 0 0 = expected 1 := by rfl'
theorem zero_one : call 0 1 = expected 0 := by rfl'
theorem power_ten : call 2 10 = expected 1024 := by rfl'
theorem highest_bit : call 2 255 = expected (2^255) := by rfl'
theorem wrapping_power : call 2 256 = expected 0 := by rfl'
theorem wide_identity : call (2^255) 1 = expected (2^255) := by rfl'
theorem wide_square : call (2^255) 2 = expected 0 := by rfl'
theorem mixed_square : call (2^128+1) 2 = expected (2^129+1) := by rfl'

theorem first_allocation_oom :
    fn_exp256.runFuel 16 [word 2, word 10] ⟨[], 7, addressLimit - 32⟩ =
      .finished (.error .outOfMemory) ⟨[], 7, addressLimit - 32⟩ := by rfl'
theorem second_allocation_oom :
    fn_exp256.runFuel 16 [word 2, word 10] ⟨[], 7, addressLimit - 64⟩ =
      .finished (.error .outOfMemory) ⟨[], 8, addressLimit - 32⟩ := by rfl'
theorem third_allocation_oom :
    fn_exp256.runFuel 16 [word 2, word 10] ⟨[], 7, addressLimit - 80⟩ =
      .finished (.error .outOfMemory) ⟨[], 9, addressLimit - 16⟩ := by rfl'
theorem invalid_argument_no_allocation :
    fn_exp256.runFuel 400 [word (-1), word 10] {} = .finished (.error .malformed) {} := by rfl'

/-- The newly admitted layout participates in the existing heap invariant at
every budget. This does not imply termination or the expected power result. -/
theorem heap_valid (fuel : Nat) (args : List Value) (state : State) (valid : state.valid = true) :
    (fn_exp256.runFuel fuel args state).state.valid = true :=
  Program.runFuel_preserves_valid fn_exp256 fuel args state valid

end Compiler.ZigAir.ExpTests
