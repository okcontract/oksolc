/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordCopyProofs

namespace Compiler.ZigAir.Memory.WordCopy.Tests
open WordArray

def source : View := ⟨0, 0, 3⟩
def target : View := ⟨1, 1, 3⟩
def sourceCell : Allocation := ⟨16, .array 3 word, [(0, number 3), (4, number 1), (8, number 2)], false, false⟩
def targetCell : Allocation := ⟨32, .array 5 word, [(0, number 3735928559), (16, number 3131961357)], true, false⟩
def caller : State := ⟨[(0, sourceCell), (1, targetCell), (2, ⟨64, word, [(0, number 99)], true, false⟩)], 3, 68⟩
def copied : State := (copy caller source target).2

def observations (state : State) : List (Except Fault Value) :=
  (List.range 3).map (fun index => load state (readPointer source index)) ++
  (List.range 5).map (fun index => load state (({ target with first := 0 } : View).pointer index)) ++
  [load state (.pointer (.pointer true false word) ⟨2, 0⟩)]

theorem valid_caller : caller.valid = true := by decide +kernel
theorem writable_target : Writable caller target := ⟨5, targetCell, rfl, rfl, rfl, by decide⟩
theorem represented_source : Represents caller source [3, 1, 2] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by simp only [List.length_cons, List.length_nil] at inside; omega
  rcases cases with rfl | rfl | rfl <;> rfl'

theorem target_uninitialized : load caller (target.pointer 0) = .error .uninitialized := by rfl'
theorem readonly_source : sourceCell.writable = false := rfl
theorem copies_readonly_into_uninitialized : (copy caller source target).1 = .ok () := by rfl'
theorem source_and_sentinels_preserved : observations copied =
    [3, 1, 2, 3735928559, 3, 1, 2, 3131961357, 99].map (fun value => .ok (number value)) := by rfl'
theorem counters_preserved : copied.nextId = caller.nextId ∧ copied.nextAddress = caller.nextAddress := ⟨by rfl', by rfl'⟩

theorem total_witness : ∃ after, copy caller source target = (.ok (), after) ∧
    after.valid = true ∧ Writable after target ∧ Represents after source [3, 1, 2] ∧
    Represents after target [3, 1, 2] ∧ Frame target caller after :=
  copy_refines caller source target [3, 1, 2] valid_caller writable_target represented_source rfl (by decide)

theorem empty_skips_accesses : copy {} ⟨0, 0, 0⟩ ⟨0, 0, 0⟩ = (.ok (), {}) := rfl
theorem unequal_lengths : copy caller source { target with length := 2 } = (.error .sourceBounds, caller) := rfl
theorem aliases_rejected : copy caller source source = (.error .memoryValidity, caller) := rfl
theorem partial_overlap_rejected : copy caller ⟨1, 0, 3⟩ target = (.error .memoryValidity, caller) := rfl

def shared : State := ⟨[(0, ⟨16, .array 6 word, sourceCell.cells, true, false⟩)], 1, 40⟩
theorem same_allocation_disjoint :
    let (result, after) := copy shared source ⟨0, 3, 3⟩
    result = .ok () ∧ (List.range 6).map (fun index => load after (source.pointer index)) =
      [3, 1, 2, 3, 1, 2].map (fun value => .ok (number value)) := ⟨by rfl', by rfl'⟩

def incompleteSource : State := { caller with heap := [(0, { sourceCell with cells := [(0, number 3)] }), (1, targetCell)] }
def prefixState : State := (copyFrom source target 1 0 incompleteSource).2

theorem incomplete_source_valid : incompleteSource.valid = true := by decide +kernel
theorem uninitialized_retains_prefix : copy incompleteSource source target = (.error .uninitialized, prefixState) := by rfl'
theorem prefix_not_zero_filled : load prefixState (target.pointer 0) = .ok (number 3) ∧
    load prefixState (target.pointer 1) = .error .uninitialized := ⟨by rfl', by rfl'⟩

def readonlyTarget : State := { caller with heap := [(0, sourceCell), (1, { targetCell with writable := false })] }
theorem readonly_target_rejected : copy readonlyTarget source target = (.error .readOnly, readonlyTarget) := by rfl'
theorem dead_source_rejected : copy {} source target = (.error .unallocated, {}) := by rfl'
def deadTarget : State := { caller with heap := [(0, sourceCell)] }
theorem dead_target_rejected : copy deadTarget source target = (.error .unallocated, deadTarget) := by rfl'
theorem outside_target_rejected : copy caller source { target with first := 5 } = (.error .memoryValidity, caller) := by rfl'

end Compiler.ZigAir.Memory.WordCopy.Tests
