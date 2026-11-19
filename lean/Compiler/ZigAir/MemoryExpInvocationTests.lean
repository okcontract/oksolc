/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpInvocation

namespace Compiler.ZigAir.MemoryExp.InvocationTests
open Memory MemoryAir GeneratedMemory

private def caller (nextId nextAddress : Nat) : State :=
  ⟨[(4, ⟨16, wordType, [(0, number 7)], false, true⟩)], nextId, nextAddress⟩

/-- A readonly caller-owned stack cell survives cleanup at the incoming mark;
the three new scratch lifetimes disappear and their counters remain advanced. -/
theorem nonempty_witness :
    ∃ fuel, fn_exp256.runFuel fuel (arguments 2 10) (caller 9 48) =
      .finished (.ok (number 1024)) (caller 12 144) := by
  have expected : specification 2 10 (caller 9 48) = (.ok (number 1024), caller 12 144) := by rfl'
  simpa only [expected] using exp_terminates 2 10 (caller 9 48) (by rfl')

theorem full_width_witness :
    ∃ fuel, fn_exp256.runFuel fuel (arguments 57896044618658097711785492504343953926634992332820282019728792003956564819969 2) (caller 9 48) =
      .finished (.ok (number 1)) (caller 12 144) := by
  have expected : specification 57896044618658097711785492504343953926634992332820282019728792003956564819969 2 (caller 9 48) = (.ok (number 1), caller 12 144) := by rfl'
  simpa only [expected] using exp_terminates 57896044618658097711785492504343953926634992332820282019728792003956564819969 2 (caller 9 48) (by rfl')

theorem zero_exponent_still_allocates :
    ∃ fuel, fn_exp256.runFuel fuel (arguments 0 0) (caller 9 48) =
      .finished (.ok (number 1)) (caller 12 144) := by
  have expected : specification 0 0 (caller 9 48) = (.ok (number 1), caller 12 144) := by rfl'
  simpa only [expected] using exp_terminates 0 0 (caller 9 48) (by rfl')

theorem first_allocation_oom :
    ∃ fuel, fn_exp256.runFuel fuel (arguments 2 10) (caller 9 addressLimit) =
      .finished (.error .outOfMemory) (caller 9 addressLimit) := by
  have expected : specification 2 10 (caller 9 addressLimit) =
      (.error .outOfMemory, caller 9 addressLimit) := by rfl'
  simpa only [expected] using exp_terminates 2 10 (caller 9 addressLimit) (by rfl')

theorem second_allocation_oom :
    ∃ fuel, fn_exp256.runFuel fuel (arguments 2 10) (caller 9 (addressLimit - 64)) =
      .finished (.error .outOfMemory) (caller 10 (addressLimit - 32)) := by
  have expected : specification 2 10 (caller 9 (addressLimit - 64)) =
      (.error .outOfMemory, caller 10 (addressLimit - 32)) := by rfl'
  simpa only [expected] using exp_terminates 2 10 (caller 9 (addressLimit - 64)) (by rfl')

theorem third_allocation_oom :
    ∃ fuel, fn_exp256.runFuel fuel (arguments 2 10) (caller 9 (addressLimit - 96)) =
      .finished (.error .outOfMemory) (caller 11 (addressLimit - 32)) := by
  have expected : specification 2 10 (caller 9 (addressLimit - 96)) =
      (.error .outOfMemory, caller 11 (addressLimit - 32)) := by rfl'
  simpa only [expected] using exp_terminates 2 10 (caller 9 (addressLimit - 96)) (by rfl')

theorem invalid_heap_rejected (fuel : Nat) :
    fn_exp256.runFuel fuel (arguments 2 10) (caller 4 48) =
      .finished (.error .malformed) (caller 4 48) :=
  exp_rejected _ _ fuel (by rfl')

end Compiler.ZigAir.MemoryExp.InvocationTests
