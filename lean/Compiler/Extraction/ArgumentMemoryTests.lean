/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemoryProofs

namespace Compiler.Extraction.Memory.Arguments.Tests
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

def logical : Heap := fun id =>
  if id = 0 then some ⟨7, .arguments [3, 1, 2]⟩
  else if id = 1 then some ⟨11, .arguments [99]⟩ else none

def first : ArgumentSlice := ⟨0, [3, 1, 2]⟩
def second : ArgumentSlice := ⟨1, [99]⟩
def firstCell : Compiler.ZigAir.Memory.Allocation :=
  ⟨16, .array 3 word, [(0, number 3), (4, number 1), (8, number 2)], true, false⟩
def secondCell : Compiler.ZigAir.Memory.Allocation := ⟨40, .array 1 word, [(0, number 99)], true, false⟩
def scratchCell : Compiler.ZigAir.Memory.Allocation := ⟨48, .array 2 word, [], true, true⟩
def bytes : Compiler.ZigAir.Memory.State := ⟨[(0, firstCell), (1, secondCell), (2, scratchCell)], 3, 56⟩
def after : Compiler.ZigAir.Memory.State := Compiler.ZigAir.Memory.erase bytes 0
def remaining : Heap := write logical 0 none

theorem valid : bytes.valid = true := by decide +kernel
theorem first_live : SliceValid 7 logical first := Or.inr rfl
theorem related : Related logical bytes := by
  intro allocator id items _ stored
  by_cases zero : id = 0
  · subst id
    have same : 7 = allocator ∧ [3, 1, 2] = items := by simpa [logical] using stored
    rcases same with ⟨rfl, rfl⟩
    refine ⟨⟨firstCell, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
    intro index inside
    have cases : index = 0 ∨ index = 1 ∨ index = 2 := by simp only [List.length_cons, List.length_nil] at inside; omega
    rcases cases with rfl | rfl | rfl <;> rfl'
  · by_cases one : id = 1
    · subst id
      have same : 11 = allocator ∧ [99] = items := by simpa [logical] using stored
      rcases same with ⟨rfl, rfl⟩
      refine ⟨⟨secondCell, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
      intro index inside
      have only : index = 0 := by simp only [List.length_cons, List.length_nil] at inside; omega
      subst index
      rfl'
    · simp [logical, zero, one] at stored

theorem read_agrees : readArgument logical first 1 = .ok 1 ∧
    Compiler.ZigAir.Memory.load bytes ((view first).pointer 1) = .ok (number 1) :=
  related_read logical bytes 7 first related first_live 1 (by decide)

theorem release_both : release logical bytes 7 first = .ok (remaining, after) := by rfl'
theorem total_witness : ∃ afterHeap after, release logical bytes 7 first = .ok (afterHeap, after) ∧
    ReleasePost logical bytes 7 first afterHeap after := release_refines logical bytes 7 first valid related first_live
theorem after_related : Related remaining after := related_erase logical bytes 0 related
theorem after_valid : after.valid = true := Compiler.ZigAir.Memory.erase_preserves_valid bytes 0 valid
theorem history_retained : after.nextId = 3 ∧ after.nextAddress = 56 := ⟨rfl, rfl⟩
theorem alias_dead : readArgument remaining first 2 = .error .unallocated ∧
    Compiler.ZigAir.Memory.load after ((view first).pointer 2) = .error .unallocated := ⟨by rfl', by rfl'⟩
theorem other_words_and_uninitialized_preserved :
    Compiler.ZigAir.Memory.load after ((view second).pointer 0) = .ok (number 99) ∧
    Compiler.ZigAir.Memory.load after ((⟨2, 0, 2⟩ : View).pointer 0) = .error .uninitialized ∧
    after.heap.lookup 2 = some scratchCell := ⟨by rfl', by rfl', by rfl'⟩
theorem double_free_rejected : release remaining after 7 first = .error (.ownership .unallocated) := by rfl'
theorem wrong_allocator_rejected : release logical bytes 8 first = .error (.ownership .wrongAllocator) := by rfl'
theorem wrong_extent_rejected : release logical bytes 7 ⟨0, [3, 1]⟩ = .error (.memory .memoryValidity) := by rfl'
theorem missing_typed_lifetime_rejected : release logical after 7 first = .error (.memory .unallocated) := by rfl'
theorem empty_skips_invalid_heap_and_sentinel : release logical { nextAddress := Compiler.ZigAir.Memory.addressLimit + 1 }
    999 ⟨999, []⟩ = .ok (logical, { nextAddress := Compiler.ZigAir.Memory.addressLimit + 1 }) := rfl

def stack : Compiler.ZigAir.Memory.State := { bytes with heap := [(0, { firstCell with stack := true })] }
theorem stack_rejected : release logical stack 7 first = .error (.memory .memoryValidity) := by rfl'
theorem stack_is_not_owned : ¬Owned stack 0 3 := by
  simp [Owned, stack, bytes, firstCell, Compiler.ZigAir.Memory.Heap.lookup]
def readonly : Compiler.ZigAir.Memory.State := { bytes with heap := [(0, { firstCell with writable := false })] }
theorem readonly_storage_rejected : release logical readonly 7 first = .error (.memory .memoryValidity) := by rfl'
def uninitialized : Compiler.ZigAir.Memory.State := { bytes with heap := [(0, { firstCell with cells := [] })] }
theorem uninitialized_owned_can_be_freed : release logical uninitialized 7 first =
    .ok (remaining, Compiler.ZigAir.Memory.erase uninitialized 0) := by rfl'
theorem uninitialized_is_not_related : ¬Related logical uninitialized := by
  intro assumed
  have read := (related_read logical uninitialized 7 first assumed first_live 0 (by decide)).2
  contradiction
theorem malformed_heap_rejected : release logical { bytes with nextId := 0 } 7 first = .error (.memory .malformed) := by rfl'
theorem second_release_keeps_scratch :
    release remaining after 11 second = .ok (write remaining 1 none, Compiler.ZigAir.Memory.erase after 1) ∧
    (Compiler.ZigAir.Memory.erase after 1).heap = [(2, scratchCell)] := ⟨by rfl', by rfl'⟩

end Compiler.Extraction.Memory.Arguments.Tests
