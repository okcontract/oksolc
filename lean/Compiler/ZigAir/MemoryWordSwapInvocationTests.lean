/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapInvocation
import Compiler.ZigAir.MemoryWordSwapTests
import Compiler.ZigAir.MemoryExpSafetyTests
import Compiler.ZigAir.MemoryFillInvocationTests
import Compiler.Extraction.InsertionSortHeapTests

namespace Compiler.ZigAir.MemoryWordSwap.Tests
open Memory MemoryAir GeneratedMemory
open Memory.ByteExchange.Tests (caller view items expected writable represented)

/-- The full theorem supplies termination and the swapped-list relation;
the existing concrete run excludes its allocation-failure alternative. -/
theorem total_witness :
    ∃ fuel after, fn_swap_u32.runFuel fuel args caller = .finished (.ok (.scalar .unit)) after ∧
      after.valid = true ∧ WordArray.Represents after view [305419896, 3735928559] := by
  obtain ⟨fuel, result, after, ran, valid, outcome⟩ := swap_refines caller view items 0 1
    WordByteView.Tests.valid_caller writable represented (by decide) (by decide) (by decide)
  have same := Invocation.finished_unique (fn_swap_u32.start args caller) fuel 160 result (.ok (.scalar .unit)) after
    { expected with nextId := 2, nextAddress := 40 } ran complete_swap
  have valueEq : result = .ok (.scalar .unit) := (Prod.mk.inj same).1
  refine ⟨fuel, after, by simpa only [valueEq] using ran, valid, ?_⟩
  rcases outcome with ⟨failed, _⟩ | ⟨_, _, _, _, _, _, rep, _⟩
  · rw [valueEq] at failed
    cases failed
  · exact rep

theorem exhausted_valid : exhausted.valid = true := by decide +kernel

theorem exhausted_total_witness : ∃ fuel,
    fn_swap_u32.runFuel fuel args exhausted = .finished (.error .outOfMemory) exhausted := by
  have cap := WordArray.writable_heap_eq caller exhausted view rfl writable
  have rep := WordArray.represents_heap_eq caller exhausted view items rfl represented
  obtain ⟨fuel, result, after, ran, _, _⟩ := swap_refines exhausted view items 0 1
    exhausted_valid cap rep (by decide) (by decide) (by decide)
  have same := Invocation.finished_unique (fn_swap_u32.start args exhausted) fuel 160 result (.error .outOfMemory)
    after exhausted ran allocation_exhausted
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
  exact ⟨fuel, ran⟩

end Compiler.ZigAir.MemoryWordSwap.Tests
