/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryRelease
import Compiler.Extraction.RepresentativeArrayAllocation
import Compiler.Extraction.RepresentativeArrayTests
import Compiler.Extraction.RepresentativeOwnerFieldTests

namespace Compiler.Extraction.RepresentativeArray.Backing.Tests
open Compiler.ZigAir.Memory

/-- The prior backing lifetime ended; its address can be reused while the
header is still unchanged. This intermediate state cannot be read as a graph. -/
def before : State := erase RepresentativeArray.Tests.memory 2
def request (base : Option Nat) : RegionAllocation.Allocator (List (Nat × Nat)) :=
  fun bytes alignment effects => (base, effects ++ [(bytes, alignment)])
def after : State := RegionAllocation.extend before (type 3) 96 512

theorem initial_valid : before.valid = true := by decide

theorem fits : RegionAllocation.Fits before ⟨96, 8⟩ 512 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  change entry ∈ [(3, RepresentativeArray.Tests.header), (1, Expression.Tests.argumentsAllocation),
    (0, Expression.Tests.itemAllocation)] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl <;> cases shaped <;> decide

theorem actual_request : reserve before 3 (request (some 512)) [] =
    ((.ok (some ⟨4, 0⟩), after), [(96, 8)]) := by decide

theorem admitted_without_final_premises : ∃ finalState,
    reserve before 3 (request (some 512)) [] = ((.ok (some ⟨before.nextId, 0⟩), finalState), [(96, 8)]) ∧
    finalState.valid = true ∧ before.heap.RetainsShape finalState.heap ∧
    finalState.heap.lookup before.nextId = some ⟨512, type 3, [], true, false⟩ ∧
    finalState.nextId = before.nextId + 1 ∧ finalState.nextAddress = max before.nextAddress (512 + 3 * 32) ∧
    (∀ id, id ≠ before.nextId → finalState.heap.lookup id = before.heap.lookup id) :=
  reserve_verified before 3 512 (request (some 512)) [] [(96, 8)] initial_valid (by decide) (by decide) rfl fits

theorem complete_uninitialized_backing : after.valid = true ∧
    after.heap.lookup 4 = some ⟨512, .array 3 Expression.allocationType, [], true, false⟩ ∧
    Expression.readFields after false ⟨4, 32⟩ = .error .uninitialized := by decide

theorem fresh_lifetime_and_high_water : after.nextId = 5 ∧ after.nextAddress = 632 ∧
    after.heap.lookup 2 = none ∧ Expression.readFields after false ⟨2, 32⟩ = .error .unallocated := by decide

theorem allocation_does_not_publish_header : readHeader after ⟨3, 0⟩ = readHeader before ⟨3, 0⟩ ∧
    representative after ⟨3, 0⟩ 0 = .error .unallocated ∧
    after.heap.lookup 0 = before.heap.lookup 0 ∧ after.heap.lookup 1 = before.heap.lookup 1 := by decide

def parent : WordArray.View := ⟨1, 1, 2⟩
theorem parent_contents : WordArray.Represents before parent [99, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have choice : index = 0 ∨ index = 1 := by simp at inside; omega
  rcases choice with rfl | rfl <;> rfl'

theorem offset_parent_survives : WordArray.Represents after parent [99, 1] := by
  have preserved := reserve_parent_borrow before 3 (request (some 512)) [] parent [99, 1] initial_valid parent_contents
  simpa only [actual_request] using preserved

theorem every_response_preserves_parent (base : Option Nat) :
    WordArray.Represents (reserve before 3 (request base) []).1.2 parent [99, 1] :=
  reserve_parent_borrow before 3 (request base) [] parent [99, 1] initial_valid parent_contents

def besideLiveBacking : State := RegionAllocation.extend RepresentativeArray.Tests.memory (type 6) 192 640

theorem live_backing_survives_reservation :
    reserve RepresentativeArray.Tests.memory 6 (request (some 640)) [] =
      ((.ok (some ⟨4, 0⟩), besideLiveBacking), [(192, 8)]) ∧
    besideLiveBacking.valid = true ∧
    besideLiveBacking.heap.lookup 2 = RepresentativeArray.Tests.memory.heap.lookup 2 ∧
    representative besideLiveBacking ⟨3, 0⟩ 1 = representative RepresentativeArray.Tests.memory ⟨3, 0⟩ 1 := by decide

theorem still_live_region_cannot_be_reused : reserve RepresentativeArray.Tests.memory 3 (request (some 512)) [] =
    ((.error .memoryValidity, RepresentativeArray.Tests.memory), [(96, 8)]) := by decide

theorem empty_skips_allocator : reserve before 0 (request (some 0)) [] =
    ((.ok (some ⟨4, 0⟩), before), []) := by decide

theorem oom_retains_effects : reserve before 3 (request none) [(4, 4)] =
    ((.ok none, before), [(4, 4), (96, 8)]) := by decide

theorem overflow_skips_allocator : reserve before (addressLimit / 32) (request (some 512)) [] =
    ((.ok none, before), []) := by decide

theorem invalid_capacity_rejects : reserve before addressLimit (request (some 512)) [] =
    ((.error .malformed, before), []) := by decide

theorem invalid_heap_rejects_before_request : reserve {before with nextId := 0} 3 (request (some 512)) [] =
    ((.error .malformed, {before with nextId := 0}), []) := by decide

theorem null_and_word_only_alignment_reject : reserve before 3 (request (some 0)) [] =
    ((.error .memoryValidity, before), [(96, 8)]) ∧ reserve before 3 (request (some 516)) [] =
    ((.error .memoryValidity, before), [(96, 8)]) := by decide

theorem overlap_and_address_overflow_reject : reserve before 4 (request (some 512)) [] =
    ((.error .memoryValidity, before), [(128, 8)]) ∧ reserve before 3 (request (some (addressLimit - 8))) [] =
    ((.error .memoryValidity, before), [(96, 8)]) := by decide

theorem every_response_valid (base : Option Nat) : (reserve before 3 (request base) []).1.2.valid = true :=
  reserve_preserves_valid before 3 (request base) [] initial_valid

theorem unsupported_metadata_rejects : RegionAllocation.reserve before (.scalar (.int false 0)) (request (some 512)) [] =
    ((.error .unsupported, before), []) := by decide

end Compiler.Extraction.RepresentativeArray.Backing.Tests
