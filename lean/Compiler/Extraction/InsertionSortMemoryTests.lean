/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortTests
import Compiler.Extraction.InsertionSortMemory

deriving instance DecidableEq for Except

namespace Compiler.Extraction.InsertionSort.MemoryTests
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

def arrayCell (a b : BitVec 32) : Allocation :=
  ⟨16, .array 4 word, [(0, number 3735928559), (4, number a), (8, number b), (12, number 3131961357)], true, false⟩

def caller (a b : BitVec 32) : State :=
  ⟨[(0, arrayCell a b), (1, ⟨40, word, [(0, number 99)], true, false⟩)], 2, 44⟩

def view : View := ⟨0, 1, 2⟩

def observations (state : State) : List (Except Compiler.ZigAir.Memory.Fault Value) :=
  [load state (.pointer (.pointer true false word) ⟨0, 0⟩),
   load state (view.pointer 0), load state (view.pointer 1),
   load state (.pointer (.pointer true false word) ⟨0, 12⟩),
   load state (.pointer (.pointer true false word) ⟨1, 0⟩)]

def pairObservation (a b : BitVec 32) : Except Compiler.ZigAir.Memory.Fault Unit × List (Except Compiler.ZigAir.Memory.Fault Value) :=
  let (result, after) := exchange (caller a b) view 1 0
  (result, observations after)

def expected (a b : BitVec 32) : Except Compiler.ZigAir.Memory.Fault Unit × List (Except Compiler.ZigAir.Memory.Fault Value) :=
  (.ok (), [.ok (number 3735928559), .ok (number b), .ok (number a), .ok (number 3131961357), .ok (number 99)])

theorem swap_zero : pairObservation 0 0 = expected 0 0 := by decide +kernel
theorem swap_small : pairObservation 1 2 = expected 1 2 := by decide +kernel
theorem swap_max : pairObservation 4294967295 0 = expected 4294967295 0 := by decide +kernel
theorem swap_equal_max : pairObservation 4294967295 4294967295 = expected 4294967295 4294967295 := by decide +kernel
theorem swap_high : pairObservation 2147483648 1 = expected 2147483648 1 := by decide +kernel
theorem swap_zero_high : pairObservation 0 2147483648 = expected 0 2147483648 := by decide +kernel
theorem swap_duplicate : pairObservation 7 7 = expected 7 7 := by decide +kernel
theorem swap_mixed : pairObservation 2863311530 1431655765 = expected 2863311530 1431655765 := by decide +kernel

theorem valid_caller : (caller 3 1).valid = true := by decide
theorem writable_caller : Writable (caller 3 1) view :=
  ⟨4, arrayCell 3 1, rfl, rfl, rfl, by decide⟩
theorem represented_caller : Represents (caller 3 1) view [3, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have cases : index = 0 ∨ index = 1 := by simp only [List.length_cons, List.length_nil] at inside; omega
  rcases cases with rfl | rfl
  · exact (by decide +kernel : load (caller 3 1) (view.pointer 0) = .ok (number 3))
  · exact (by decide +kernel : load (caller 3 1) (view.pointer 1) = .ok (number 1))

theorem larger_allocation_not_view :
    exchange (caller 3 1) view 2 0 = (.error .sourceBounds, caller 3 1) := by decide +kernel
theorem empty_view_rejects :
    exchange (caller 3 1) { view with length := 0 } 0 0 = (.error .sourceBounds, caller 3 1) := by decide +kernel
theorem over_extent_rejects :
    exchange (caller 3 1) { view with first := 3 } 1 0 = (.error .memoryValidity, caller 3 1) := by decide +kernel

def uninitialized : State :=
  { caller 3 1 with heap := [(0, { arrayCell 3 1 with cells := [(4, number 3)] })] }
theorem uninitialized_valid : uninitialized.valid = true := by decide
theorem uninitialized_rejects : exchange uninitialized view 1 0 = (.error .uninitialized, uninitialized) := by decide +kernel

def readonly : State :=
  { caller 3 1 with heap := [(0, { arrayCell 3 1 with writable := false })] }
theorem readonly_rejects : exchange readonly view 1 0 = (.error .readOnly, readonly) := by decide +kernel
theorem dead_rejects : exchange {} view 1 0 = (.error .unallocated, {}) := by decide +kernel

def misaligned : State :=
  { caller 3 1 with heap := [(0, { arrayCell 3 1 with base := 15 })] }
theorem misalignment_rejects : exchange misaligned view 1 0 = (.error .memoryValidity, misaligned) := by decide +kernel

/-- A typed exchange with the same address has an ordinary result, but cannot
satisfy the distinct-region premise required by Zig's noalias source contract. -/
theorem alias_not_disjoint : ¬((20 : Nat) + 4 ≤ 20 ∨ (20 : Nat) + 4 ≤ 20) := by decide
theorem alias_typed_observation : (exchange (caller 3 1) view 0 0).1 = .ok () := by decide +kernel

theorem typed_exchange_witness :
    ∃ after, exchange (caller 3 1) view 1 0 = (.ok (), after) ∧ after.valid = true ∧
      Writable after view ∧ Represents after view [1, 3] := by
  obtain ⟨after, ran, valid, cap, represented, _⟩ :=
    exchange_refines (caller 3 1) view [3, 1] 1 0 valid_caller writable_caller represented_caller (by decide) (by decide)
  exact ⟨after, ran, valid, cap, represented⟩

end Compiler.Extraction.InsertionSort.MemoryTests
