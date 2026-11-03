/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemoryAllocationProofs
import Compiler.Extraction.ArgumentMemoryPreparationTests

namespace Compiler.Extraction.Memory.Arguments.Allocation.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

def before : Compiler.ZigAir.Memory.State :=
  ⟨[(0, WordCopy.Tests.sourceCell), (2, PreparationTests.otherCell)], 3, 52⟩
def logical : Memory.Heap := write PreparationTests.logical 1 none
def source : View := ⟨0, 0, 3⟩
def items : List NodeId := [3, 1, 2]
def request (base : Option Nat) : WordAllocation.Allocator Nat := fun bytes effects => (base, effects + bytes)
def allocated : Compiler.ZigAir.Memory.State := WordAllocation.extend before 3 32
def registered : Memory.Heap := write logical 3 (some ⟨7, .arguments items⟩)
def destination : ArgumentSlice := ⟨3, items⟩
def after : Compiler.ZigAir.Memory.State := (Copied.run 160 allocated source (view destination)).2
def projected : Memory.Heap := write registered 3 (some ⟨7, .arguments [1, 2, 3]⟩)

theorem valid : before.valid = true := by decide +kernel
theorem represented : Represents before source items := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have cases : index = 0 ∨ index = 1 ∨ index = 2 := by simp [items] at inside; omega
  rcases cases with rfl | rfl | rfl <;> rfl'
theorem related : Related logical before := by
  intro allocator id values nonempty stored
  obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ := PreparationTests.others_related allocator id values nonempty stored
  have two : id = 2 := by
    by_cases two : id = 2
    · exact two
    · by_cases one : id = 1 <;> simp [logical, write, PreparationTests.logical, one, two] at stored
  subst id
  refine ⟨⟨cell, found, typed, writable, stack⟩, represented.1, ?_⟩
  intro index inside
  exact represented.2 index inside
theorem fits : WordAllocation.Fits before 3 32 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  simp only [before, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl <;> cases shaped <;> decide
theorem admitted : reserve logical before 7 items (request (some 32)) 5 =
    ((.ok (some destination), registered, allocated), 17) :=
  reserve_admitted logical before 7 32 items (request (some 32)) 5 17 valid (by decide) source represented rfl rfl fits
theorem allocated_valid : allocated.valid = true := WordAllocation.extend_valid before 3 32 valid fits
theorem allocated_owned : Owned allocated 3 3 := extend_owned before 3 32
theorem source_preserved : Represents allocated source items := WordAllocation.source_preserved before 3 32 source items valid represented
theorem provisional_uninitialized : load allocated ((view destination).pointer 0) = .error .uninitialized := by rfl'
theorem provisional_not_related : ¬Related registered allocated := by
  intro claimed
  have read := (related_read registered allocated 7 destination claimed (Or.inr rfl) 0 (by decide)).2
  contradiction
theorem fresh_lifetime_reused_region : allocated.heap.lookup 1 = none ∧ allocated.heap.lookup 3 = some (WordAllocation.cell 3 32) := ⟨by rfl', by rfl'⟩
theorem old_alias_dead : load allocated ((⟨1, 0, 3⟩ : View).pointer 0) = .error .unallocated := by rfl'
theorem cleanup_keeps_persistent : (cleanup before.nextId allocated).heap.lookup 3 = allocated.heap.lookup 3 := by rfl'
theorem high_water_retained : allocated.nextId = 4 ∧ allocated.nextAddress = 52 := ⟨rfl, rfl⟩

theorem empty_skips_external : reserve logical before 7 [] (request (some 0)) 5 =
    ((.ok (some ⟨3, []⟩), logical, before), 5) := rfl
theorem oom_retains_effects : reserve logical before 7 items (request none) 5 = ((.ok none, logical, before), 17) :=
  reserve_failed logical before 7 items (request none) 5 17 valid (by decide) source represented rfl
theorem byte_overflow_skips_external : WordAllocation.reserve before (addressLimit / 4) (request (some 32)) 5 =
    ((.ok none, before), 5) := by rfl'
theorem invalid_length_rejected : WordAllocation.reserve before addressLimit (request (some 32)) 5 =
    ((.error .malformed, before), 5) := by rfl'
theorem invalid_initial_heap_rejected : WordAllocation.reserve {before with nextId := 0} 3 (request (some 32)) 5 =
    ((.error .malformed, {before with nextId := 0}), 5) := by rfl'
theorem null_region_rejected : reserve logical before 7 items (request (some 0)) 5 =
    ((.error (.memory .memoryValidity), logical, before), 17) := by rfl'
theorem misaligned_region_rejected : reserve logical before 7 items (request (some 33)) 5 =
    ((.error (.memory .memoryValidity), logical, before), 17) := by rfl'
theorem overlapping_region_rejected : reserve logical before 7 items (request (some 8)) 5 =
    ((.error (.memory .memoryValidity), logical, before), 17) := by rfl'
theorem address_overflow_rejected : reserve logical before 7 items (request (some (addressLimit - 4))) 5 =
    ((.error (.memory .memoryValidity), logical, before), 17) := by rfl'
def collision : Memory.Heap := write logical 3 (some ⟨11, .representatives []⟩)
theorem collision_retains_allocation : reserve collision before 7 items (request (some 32)) 5 =
    ((.error (.registry .notFresh), collision, allocated), 17) := by rfl'
theorem every_response_valid (base : Option Nat) :
    (reserve logical before 7 items (request base) 5).1.2.2.valid = true :=
  reserve_preserves_valid logical before 7 items (request base) 5 valid

theorem settles_from_allocation : ∃ result final values heap, Captured.Settles
    (fun budget => Copied.run budget allocated source (view destination)) (result, final) ∧
    Updated registered heap 3 values ∧ Related heap final ∧ final.valid = true ∧ values.Perm items ∧
    Represents final source items ∧ HeapFrame (view destination) allocated final ∧ SliceValid 7 heap ⟨3, values⟩ ∧
    ((result = .ok () ∧ values = sortIds items) ∨ result = .error (.memory .outOfMemory)) :=
  copied_refines logical registered before allocated 7 items (request (some 32)) 5 17 destination source
    valid related represented (by decide) admitted
theorem complete : Copied.run 160 allocated source (view destination) = (.ok (), after) := by rfl'
theorem complete_values :
    (List.range 3).map (fun index => load after ((view destination).pointer index)) =
      [1, 2, 3].map (fun value => .ok (number value)) ∧
    load after ((⟨2, 0, 1⟩ : View).pointer 0) = .ok (number 99) := ⟨by rfl', by rfl'⟩
theorem complete_related : Related projected after := by
  have copied := Copied.run_result 160 allocated after source (view destination) items (.ok ()) allocated_valid
    (owned_writable allocated 3 3 allocated_owned) source_preserved rfl (by decide) complete
  rcases copied with impossible | ⟨values, connected, _, _, frame, effect⟩
  · contradiction
  · rcases effect with ⟨_, sorted⟩ | impossible
    · have valuesEq : values = [1, 2, 3] := sorted.trans (by rfl')
      subst values
      exact related_publish registered allocated after 7 (view destination) [1, 2, 3]
        (extend_others logical before 7 32 items valid related) frame
        (copied_owned 160 allocated source (view destination) 3 3 allocated_valid allocated_owned) rfl connected.values
    · contradiction
theorem release_after_preparation : ∃ heap final, release projected after 7 ⟨3, [1, 2, 3]⟩ = .ok (heap, final) ∧
    ReleasePost projected after 7 ⟨3, [1, 2, 3]⟩ heap final :=
  release_refines projected after 7 ⟨3, [1, 2, 3]⟩ (Copied.run_storage 160 allocated source (view destination) allocated_valid).1
    complete_related (Or.inr (by rfl'))
theorem release_retains_reached_counters : (erase after 3).nextId = 6 ∧ (erase after 3).nextAddress = 72 := ⟨by rfl', by rfl'⟩
theorem released_alias_rejected : load (erase after 3) ((view destination).pointer 2) = .error .unallocated := by rfl'

end Compiler.Extraction.Memory.Arguments.Allocation.Tests
