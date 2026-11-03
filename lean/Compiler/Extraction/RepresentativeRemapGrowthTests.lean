/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRemapGrowth
import Compiler.Extraction.RepresentativeFallbackRegistryTests
import Compiler.Extraction.InsertionKernelTestSupport

namespace Compiler.Extraction.RepresentativeArray.Growth.Registered.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization
open DescriptorRelation.FallbackRegistryTests (before request external initial_valid source_owned)

def callback : Remap.Callback := .noRemap 999 777
def execute (safety : Bool) (response : Option Nat := some 640) := run callback (request response) external 7 ⟨3, 16⟩ 5 (before safety)

theorem actual_refusal (safety : Bool) :
    Remap.run callback external 7 ⟨2, 0⟩ 3 5 (before safety) = (.ok none, before safety) :=
  Remap.refuses external 7 999 777 3 5 ⟨2, 0⟩ (before safety) (initial_valid safety) (source_owned safety) (by decide) (by decide)

theorem initial_unlocked (safety : Bool) :
    Owner.NativeLock.checkHeader (before safety).memory (Owner.headerAddress ⟨3, 0⟩) = .ok () := by
  apply Owner.NativeLock.checkHeader_of_cell safety _ 3 (Backing.Relocation.Tests.owner safety)
    (initial_valid safety).memory (by cases safety <;> insertion_kernel_rfl) rfl
  intro active
  subst safety
  rfl

theorem reached_fallback (safety : Bool) (response : Option Nat) :
    execute safety response = Backing.Fallback.run (request response) external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (before safety) :=
  fallback_execution safety (request response) external 7 3 2 3 5 2 999 777 (before safety) (Backing.Relocation.Tests.owner safety)
    (initial_valid safety) (by cases safety <;> insertion_kernel_rfl) rfl (source_owned safety) (by decide) (by decide) (by decide)
    (by cases safety <;> insertion_kernel_rfl) (by cases safety <;> insertion_kernel_rfl) (initial_unlocked safety)

/-- Both nonempty rows and every query are recovered from the reached native
growth; the ghost move does not alter those bytes or allocator effects. -/
theorem derived_contract (safety : Bool) : ∃ raw after,
    execute safety = (.ok (some ()), raw) ∧ after.memory = raw.memory ∧ after.effects = raw.effects ∧
    Valid after ∧ Compiler.Extraction.Memory.Vector 7 after.heap 4 DescriptorRelation.Tests.nodes ∧
    Backing.Release.Owned 7 ⟨4, 0⟩ 5 after ∧ after.heap 2 = none ∧ after.memory.heap.lookup 2 = none ∧
    DescriptorRelation.Prefix after.memory 4 DescriptorRelation.Tests.nodes ∧ after.memory.nextId = 5 ∧
    after.memory.nextAddress = (before safety).memory.nextAddress ∧
    after.effects = [(7, 0, 96, 8), (7, 0, 160, 8), (7, 512, 96, 8)] ∧
    readHeader after.memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 2, .scalar (.int false 64 5)) ∧
    (∀ id, representativeFields after.memory ⟨3, 16⟩ id =
      .ok ((Storage.representativeProgram.run DescriptorRelation.Tests.nodes id).map (DescriptorRelation.values id.toNat))) := by
  obtain ⟨oldCell, raw, after, oldFound, executed, memory, effects, _, reachedEffects, valid, vector, owned, dead, nativeDead, header, rows, nextId, nextAddress, queries, _⟩ :=
    verified safety request external 7 3 2 3 5 640 999 777 (before safety) _ (Backing.Relocation.Tests.owner safety)
      DescriptorRelation.Tests.nodes (initial_valid safety) (by cases safety <;> insertion_kernel_rfl) rfl rfl (source_owned safety) rfl
      (by decide) (by decide) (by decide) (by decide) rfl (DescriptorRelation.Tests.fits safety)
      (by cases safety <;> insertion_kernel_rfl) (by cases safety <;> insertion_kernel_rfl) (DescriptorRelation.Tests.prefix_from_initialization safety) (initial_unlocked safety)
  have same : oldCell = DescriptorRelation.Tests.backing DescriptorRelation.Tests.allCells :=
    Option.some.inj (oldFound.symm.trans (by cases safety <;> insertion_kernel_rfl))
  subst oldCell
  exact ⟨raw, after, executed, memory, effects, valid, vector, owned, dead, nativeDead, rows, nextId,
    (by cases safety <;> exact nextAddress), reachedEffects, header, queries⟩

theorem reached_observations (safety : Bool) :
    (execute safety).1 = .ok (some ()) ∧
    (execute safety).2.effects = [(7, 0, 96, 8), (7, 0, 160, 8), (7, 512, 96, 8)] ∧
    (execute safety).2.memory.heap.lookup 2 = none ∧
    readHeader (execute safety).2.memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 2, .scalar (.int false 64 5)) ∧
    (execute safety).2.memory.nextId = 5 ∧ (execute safety).2.memory.nextAddress = (before safety).memory.nextAddress := by
  obtain ⟨raw, after, executed, memory, effects, _, _, _, _, dead, _, nextId, nextAddress, reachedEffects, header, _⟩ := derived_contract safety
  rw [executed]
  exact ⟨rfl, effects.symm.trans reachedEffects, (congrArg (fun m => m.heap.lookup 2) memory.symm).trans dead,
    (congrArg (fun m => readHeader m ⟨3, 16⟩) memory.symm).trans header,
    (congrArg (·.nextId) memory.symm).trans nextId, (congrArg (·.nextAddress) memory.symm).trans nextAddress⟩

theorem oom_keeps_old_vector (safety : Bool) :
    execute safety none = (.ok none, {before safety with effects := [(7, 0, 96, 8), (7, 0, 160, 8)]}) := by
  rw [reached_fallback]
  exact (DescriptorRelation.FallbackRegistryTests.oom_keeps_vector safety ⟨3, 16⟩ ⟨2, 0⟩).1

theorem parent_across_all_outcomes (safety : Bool) (selected : Remap.Callback) (allocator : Nat) (response : Option Nat) :
    let after := (run selected (request response) external allocator ⟨3, 16⟩ 5 (before safety)).2
    Valid after ∧ after.memory.heap.lookup 1 = some Expression.Tests.argumentsAllocation ∧
      WordArray.Represents after.memory ⟨1, 1, 2⟩ [99, 1] :=
  parent_borrow safety selected (request response) external allocator 3 5 (before safety) (Backing.Relocation.Tests.owner safety)
    (initial_valid safety) (by decide) (by cases safety <;> insertion_kernel_rfl) rfl
    ⟨1, 1, 2⟩ [99, 1] 4 Expression.Tests.argumentsAllocation (by cases safety <;> insertion_kernel_rfl) rfl
    (DescriptorRelation.Tests.offset_borrow_still_live safety)

theorem unknown_callback_and_wrong_owner (safety : Bool) :
    run .unsupported request external 7 ⟨3, 16⟩ 5 (before safety) = (.error (.memory .unsupported), before safety) ∧
    run callback request external 8 ⟨3, 16⟩ 5 (before safety) = (.error (.ownership .wrongAllocator), before safety) ∧
    run .unsupported request external 8 ⟨3, 16⟩ 3 (before safety) = (.ok (some ()), before safety) := by
  have prepared : prepare (before safety).memory ⟨3, 16⟩ 5 = .ok (some (⟨2, 0⟩, 3)) := by cases safety <;> insertion_kernel_rfl
  have unknown : Remap.run .unsupported external 7 ⟨2, 0⟩ 3 5 (before safety) =
      (.error (.memory .unsupported), before safety) := by cases safety <;> insertion_kernel_rfl
  have wrong : Remap.run callback external 8 ⟨2, 0⟩ 3 5 (before safety) =
      (.error (.ownership .wrongAllocator), before safety) := by cases safety <;> insertion_kernel_rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [run, prepared, unknown]
  · simp only [run, prepared, wrong]
  · cases safety <;> insertion_kernel_rfl

theorem wrapper_guards (safety : Bool) :
    Remap.run .unsupported external 8 ⟨999, 7⟩ 0 5 (before safety) = (.ok none, before safety) ∧
    Remap.run .unsupported external 8 ⟨999, 7⟩ 0 0 (before safety) = (.ok (some ⟨999, 7⟩), before safety) ∧
    Remap.run .unsupported external 8 ⟨999, 7⟩ 3 (addressLimit / 32) (before safety) = (.ok none, before safety) ∧
    (Remap.run callback external 7 ⟨2, 0⟩ 3 0 (before safety)).2.memory.heap.lookup 2 = none := by
  cases safety <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem partial_copy_retained (safety : Bool) :
    run callback request external 7 ⟨3, 16⟩ 5 (DescriptorRelation.FallbackRegistryTests.damaged safety) =
      (.error (.memory .uninitialized), DescriptorRelation.FallbackRegistryTests.copyReached safety) := by
  have prepared : prepare (DescriptorRelation.FallbackRegistryTests.damaged safety).memory ⟨3, 16⟩ 5 =
      .ok (some (⟨2, 0⟩, 3)) := by cases safety <;> insertion_kernel_rfl
  have refused : Remap.run callback external 7 ⟨2, 0⟩ 3 5 (DescriptorRelation.FallbackRegistryTests.damaged safety) =
      (.ok none, DescriptorRelation.FallbackRegistryTests.damaged safety) := by cases safety <;> insertion_kernel_rfl
  simpa only [run, prepared, refused] using DescriptorRelation.FallbackRegistryTests.partial_copy_execution safety

theorem failed_response_retained (safety : Bool) :
    execute safety (some 641) = (.error (.memory .memoryValidity),
      {before safety with effects := [(7, 0, 96, 8), (7, 0, 160, 8)]}) := by
  cases safety <;> insertion_kernel_rfl

theorem publication_failure_retained (safety : Bool) :
    run callback request external 7 ⟨3, 16⟩ 5 (DescriptorRelation.FallbackRegistryTests.readonly safety) =
      (.error (.memory .readOnly), DescriptorRelation.FallbackRegistryTests.readonlyReleased safety) := by
  have prepared : prepare (DescriptorRelation.FallbackRegistryTests.readonly safety).memory ⟨3, 16⟩ 5 =
      .ok (some (⟨2, 0⟩, 3)) := by cases safety <;> insertion_kernel_rfl
  have refused : Remap.run callback external 7 ⟨2, 0⟩ 3 5 (DescriptorRelation.FallbackRegistryTests.readonly safety) =
      (.ok none, DescriptorRelation.FallbackRegistryTests.readonly safety) := by cases safety <;> insertion_kernel_rfl
  simpa only [run, prepared, refused] using DescriptorRelation.FallbackRegistryTests.publication_fault_execution safety

end Compiler.Extraction.RepresentativeArray.Growth.Registered.Tests
