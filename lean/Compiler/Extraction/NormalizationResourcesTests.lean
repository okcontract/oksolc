/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationResourcesProofs
import Compiler.Extraction.NormalizationMemoryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

/-- All concrete lifecycle fixtures pass through the protocol, including its
actual memory, registry and allocator state, rather than a success-only model. -/
theorem observations (commutative : Bool) (source : View) (items : List NodeId) (exit : NormalizationOwnership.Exit) :
    ResourceAdapter.run success 160 7 commutative source buffer items exit before =
      (some (observed commutative source items exit).1, (observed commutative source items exit).2) := by
  rw [run_eq]
  change (let (result, after) := observed commutative source items exit; (some result, after)) = _
  cases observed commutative source items exit
  rfl

theorem allocated_transfer :
    (ResourceAdapter.run success 160 7 true source buffer items .transfer before).1 = some (.ok (.transferred ⟨4, [1, 2, 3]⟩)) ∧
    (ResourceAdapter.run success 160 7 true source buffer items .transfer before).2.effects = 17 := by
  have native := Normalization.Tests.allocated_transfer
  rw [observations]
  generalize observed true source items .transfer = result at *
  rcases result with ⟨result, after⟩
  exact ⟨congrArg some native.1, native.2⟩

theorem scratch_transfer :
    (ResourceAdapter.run success 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .transfer before).1 = some (.ok (.transferred ⟨5, [1, 3]⟩)) ∧
    (ResourceAdapter.run success 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .transfer before).2.effects = 13 := by
  have native := scratch_duplicate_after_sort
  rw [observations]
  generalize observed true ⟨0, 0, 2⟩ [3, 1] .transfer = result at *
  rcases result with ⟨result, after⟩
  exact ⟨congrArg some native.1, native.2⟩

theorem borrowed_lookup : ResourceAdapter.run success 160 7 false source buffer items .lookup before = (some (.ok .lookup), before) := by
  rw [observations, noncommutative_borrows]

theorem empty_transfer : ResourceAdapter.run success 160 7 true ⟨900, 90, 0⟩ buffer [] .transfer before =
    (some (.ok (.transferred ⟨4, []⟩)), before) := by
  rw [observations, empty_dead_sentinel.1]

theorem temporary_oom : ResourceAdapter.run (external (fun _ => true)) 160 7 true source buffer items .transfer before =
    (some (.error .outOfMemory), { before with effects := 17 }) := by
  rw [run_eq, temporary_oom_retains_effects]

theorem duplicate_oom : ResourceAdapter.run (external (fun _ => true)) 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .cleanup before =
    (some (.error .outOfMemory), { scratchPrepared with effects := 13 }) := by
  rw [run_eq, duplicate_oom_after_scratch]

theorem suspension :
    let result := ResourceAdapter.run success 0 7 true source buffer items .cleanup before
    result.1 = some (.error (.preparation .incomplete)) ∧ result.2.effects = 17 ∧
      result.2.heap 4 = some ⟨7, .arguments items⟩ ∧
      load result.2.memory ((⟨4, 0, 3⟩ : View).pointer 0) = .ok (number 3) := by
  have native := suspension_retains_allocation
  rw [run_eq]
  generalize Normalization.run normalizationOwnershipCode success 0 7 true source buffer items .cleanup before = result at *
  rcases result with ⟨result, after⟩
  exact ⟨congrArg some native.1, native.2⟩

theorem semantic_stack_exhaustion :
    let result := ResourceAdapter.run success 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .cleanup
      { before with memory := { before.memory with nextAddress := addressLimit - 8 } }
    result.1 = some (.error (.preparation (.memory .outOfMemory))) ∧ result.2.effects = 5 := by
  have native := semantic_stack_exhaustion_is_not_oom
  rw [run_eq]
  generalize Normalization.run normalizationOwnershipCode success 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .cleanup
    { before with memory := { before.memory with nextAddress := addressLimit - 8 } } = result at *
  rcases result with ⟨result, after⟩
  exact ⟨congrArg some native.1, native.2⟩

theorem cleanup_retains_scratch :
    let result := ResourceAdapter.run success 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .cleanup before
    result.2.effects = 115 ∧ result.2.memory.heap.lookup 5 = none ∧
      load result.2.memory (buffer.pointer 1) = .ok (number 3) := by
  have native := scratch_caller_retains_buffer
  rw [observations]
  generalize observed true ⟨0, 0, 2⟩ [3, 1] .cleanup = result at *
  rcases result with ⟨result, after⟩
  exact native

/-- Invalid source storage cannot be converted to allocator OOM or trigger
cleanup: the partial duplicate stays allocated and its prefix remains written. -/
def incomplete : Session Nat := { original with memory := Duplication.Tests.incomplete }
def copyFault := ResourceAdapter.run success 160 7 false source buffer items .cleanup incomplete

theorem partial_copy_fault : copyFault.1 = some (.error (.allocation (.memory .uninitialized))) ∧
    copyFault.2.effects = 17 ∧
    load copyFault.2.memory ((⟨3, 0, 3⟩ : View).pointer 0) = .ok (number 3) := by
  unfold copyFault
  rw [run_eq]
  exact ⟨by rfl', by rfl', by rfl'⟩

/-- A corrupt ownership descriptor rejects release, retaining the exact session.
This client deliberately bypasses init to exercise the release fault boundary. -/
theorem release_fault : continued success 160 7 source buffer items .allocation .cleanup
    ⟨source, items, some ⟨900, items⟩⟩ before =
      (some (.error (.release (.ownership .unallocated))), before) := by
  rw [continued_eq]
  rfl'

theorem missing_descriptor_rejects :
    let reached := release success 7 { owner := .caller } (initial source items before)
    reached.rejected = some .missingSlice ∧ observe (.ok (.cleaned, {})) reached = none := ⟨rfl, rfl⟩

/-- A concrete binary ADD uses the inhabited allocator contract, actual caller
stack allocation, adapter execution and composed production theorem. -/
theorem production_add (other : Meaning) (read : Read) (sequence : BitVec 32) :
    (⟨1, some 1, 0⟩ : Item).eval (Folding.wordMeaning other) read [1, 3] sequence =
      (⟨1, some 1, 0⟩ : Item).eval (Folding.wordMeaning other) read [3, 1] sequence := by
  have represented : Represents original.memory ⟨0, 0, 2⟩ [3, 1] := by
    refine ⟨rfl, ?_⟩
    intro index inside
    have cases : index = 0 ∨ index = 1 := by simp at inside; omega
    rcases cases with rfl | rfl <;> rfl'
  have selected := scratch_transfer.1
  generalize execution : ResourceAdapter.run success 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .transfer before = result at selected
  rcases result with ⟨result, after⟩
  dsimp only at selected
  rw [selected] at execution
  exact (ResourceAdapter.production_verified success 160 7 true ⟨0, 0, 2⟩ [3, 1] .transfer original
    after before.memory _ (.ok (.transferred ⟨5, [1, 3]⟩)) ⟨1, some 1, 0⟩ other read sequence
    original_valid represented actual_caller_allocation (by rfl') (external_admitted _) execution).2.2 ⟨5, [1, 3]⟩ rfl

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.Tests
