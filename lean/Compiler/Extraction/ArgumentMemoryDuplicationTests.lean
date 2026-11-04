/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemoryDuplicationProofs
import Compiler.Extraction.ArgumentMemoryAllocationTests

namespace Compiler.Extraction.Memory.Arguments.Duplication.Tests
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Allocation.Tests (before logical source items request allocated registered destination)

def after : Compiler.ZigAir.Memory.State := (WordCopy.copy allocated source (view destination)).2

theorem complete : run logical before 7 source items (request (some 32)) 5 =
    ((.ok (some destination), registered, after), 17) := by rfl'
theorem exact_unsorted_contents :
    (List.range 3).map (fun index => load after ((view destination).pointer index)) =
      [3, 1, 2].map (fun value => .ok (number value)) := by rfl'
theorem source_and_other_preserved :
    (List.range 3).map (fun index => load after (source.pointer index)) =
      [3, 1, 2].map (fun value => .ok (number value)) ∧
    load after ((⟨2, 0, 1⟩ : View).pointer 0) = .ok (number 99) := ⟨by rfl', by rfl'⟩
theorem complete_post : Post logical before 7 source items destination registered after := by
  obtain ⟨final, ran, post⟩ := run_admitted logical before 7 32 source items (request (some 32)) 5 17 Allocation.Tests.valid
    Allocation.Tests.related Allocation.Tests.represented (by decide) rfl rfl Allocation.Tests.fits
  have same : final = after := congrArg (fun value => value.1.2.2) (ran.symm.trans complete)
  simpa only [same] using post
theorem all_requests_classified (selected : Option Nat)
    (admitted : ∀ base, selected = some base → WordAllocation.Fits before items.length base) :
    ∃ result heap final reached, run logical before 7 source items (request selected) 5 = ((.ok result, heap, final), reached) ∧
      match result with
      | none => heap = logical ∧ final = before ∧ request selected (items.length * 4) 5 = (none, reached)
      | some slice => Post logical before 7 source items slice heap final := by
  apply run_total logical before 7 source items (request selected) 5 Allocation.Tests.valid Allocation.Tests.related Allocation.Tests.represented
    (fun _ => rfl)
  intro _ base reached response
  exact admitted base (congrArg Prod.fst response)
theorem counters_only_allocate : after.nextId = 4 ∧ after.nextAddress = 52 := ⟨by rfl', by rfl'⟩
theorem independent_copy :
    let changed := store after ((view destination).pointer 0) (number 42)
    ∃ final, changed = .ok final ∧ load final (source.pointer 0) = .ok (number 3) ∧
      load final ((view destination).pointer 0) = .ok (number 42) := by
  obtain ⟨final, written⟩ := write_total after (view destination) 0 42 complete_post.valid
    (owned_writable after 3 3 (complete_post.owned (by decide))) (by decide)
  have preserved := WordCopy.source_after_store after final source (view destination) items 0 42
    (by decide) (by decide) complete_post.source written
  exact ⟨final, written, preserved.2 0 (by decide), load_after_store _ _ _ _ written⟩
theorem release_contract : ∃ heap final, release registered after 7 destination = .ok (heap, final) ∧
    ReleasePost registered after 7 destination heap final := complete_post.release
theorem release_exact : release registered after 7 destination = .ok (write registered 3 none, erase after 3) := by rfl'
theorem released_alias_dead : load (erase after 3) ((view destination).pointer 1) = .error .unallocated := by rfl'
theorem released_source_retained : load (erase after 3) (source.pointer 0) = .ok (number 3) ∧
    (erase after 3).nextId = 4 ∧ (erase after 3).nextAddress = 52 := ⟨by rfl', by rfl', by rfl'⟩

theorem borrowed_subslice :
    let result := run logical before 7 ⟨0, 1, 2⟩ [1, 2] (request (some 32)) 5
    result.1.1 = .ok (some ⟨3, [1, 2]⟩) ∧ result.2 = 13 ∧
      (List.range 2).map (fun index => load result.1.2.2 ((⟨3, 0, 2⟩ : View).pointer index)) =
        [1, 2].map (fun value => .ok (number value)) := ⟨by rfl', rfl, by rfl'⟩
theorem empty_skips_invalid_heap_and_collision :
    run Allocation.Tests.collision {before with nextAddress := 0} 7 ⟨900, 90, 0⟩ [] (request (some 0)) 5 =
      ((.ok (some ⟨3, []⟩), Allocation.Tests.collision, {before with nextAddress := 0}), 5) := by rfl'
theorem descriptor_mismatch_rejected : run logical before 7 source [3, 1] (request (some 32)) 5 =
    ((.error (.memory .sourceBounds), logical, before), 5) := by rfl'
theorem oom_retains_effects : run logical before 7 source items (request none) 5 = ((.ok none, logical, before), 17) :=
  run_oom logical before 7 source items (request none) 5 17 Allocation.Tests.valid (by decide) Allocation.Tests.represented rfl
theorem invalid_region_is_fault : run logical before 7 source items (request (some 33)) 5 =
    ((.error (.memory .memoryValidity), logical, before), 17) := by rfl'
theorem collision_keeps_uninitialized_allocation :
    let result := run Allocation.Tests.collision before 7 source items (request (some 32)) 5
    result = ((.error (.registry .notFresh), Allocation.Tests.collision, allocated), 17) ∧
      load result.1.2.2 ((view destination).pointer 0) = .error .uninitialized := ⟨by rfl', by rfl'⟩

def incomplete : Compiler.ZigAir.Memory.State :=
  { before with heap := [(0, { WordCopy.Tests.sourceCell with cells := [(0, number 3)] }), (2, PreparationTests.otherCell)] }
def failure := run logical incomplete 7 source items (request (some 32)) 5
theorem incomplete_valid : incomplete.valid = true := by decide +kernel
theorem oom_precedes_source_reads : run logical incomplete 7 source items (request none) 5 = ((.ok none, logical, incomplete), 17) := by rfl'
theorem copy_fault_retains_prefix : failure.1.1 = .error (.memory .uninitialized) ∧ failure.2 = 17 ∧
    load failure.1.2.2 ((view destination).pointer 0) = .ok (number 3) ∧
    load failure.1.2.2 ((view destination).pointer 1) = .error .uninitialized := ⟨by rfl', rfl, by rfl', by rfl'⟩
theorem copy_fault_valid : failure.1.2.2.valid = true := run_preserves_valid logical incomplete 7 source items (request (some 32)) 5 incomplete_valid
theorem copy_fault_owned : Owned failure.1.2.2 3 3 :=
  run_allocated_owned logical registered incomplete (WordAllocation.extend incomplete 3 32) 7 source items (request (some 32)) 5 17 destination
    rfl (by decide) (by rfl')
theorem copy_fault_not_published : ¬Related registered failure.1.2.2 := by
  intro claimed
  have read := (related_read registered failure.1.2.2 7 destination claimed (Or.inr rfl) 1 (by decide)).2
  contradiction
theorem explicit_release_of_partial_copy : release registered failure.1.2.2 7 destination =
    .ok (write registered 3 none, erase failure.1.2.2 3) :=
  release_effects registered failure.1.2.2 7 destination copy_fault_valid (by decide) rfl copy_fault_owned
theorem all_responses_valid (selected : Option Nat) :
    (run logical incomplete 7 source items (request selected) 5).1.2.2.valid = true :=
  run_preserves_valid logical incomplete 7 source items (request selected) 5 incomplete_valid

end Compiler.Extraction.Memory.Arguments.Duplication.Tests
