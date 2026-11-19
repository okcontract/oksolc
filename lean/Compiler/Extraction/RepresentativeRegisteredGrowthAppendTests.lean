/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRegisteredGrowthAppendProofs
import Compiler.Extraction.RepresentativeRegisteredGrowthAppendFrame
import Compiler.Extraction.RepresentativeDescriptorRegistryTests
import Compiler.Extraction.InsertionKernelTestSupport

namespace Compiler.Extraction.RepresentativeArray.Append.Registered.GrowthTests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization
open DescriptorRelation

/-- Reach a full three-row container using the existing proved spare append. -/
def before (safety : Bool) : Session Nat :=
  ⟨Compiler.Extraction.Memory.write (RegistryTests.before safety).heap 2 (some ⟨7, .representatives AppendTests.cells⟩),
    AppendTests.after safety, 0⟩
def owner (safety : Bool) : Allocation := {Backing.Relocation.Tests.owner safety with
  cells := (Backing.Relocation.Tests.owner safety).cells.set 24 (.scalar (.int false 64 3))}
def fourth : Storage.Cell := {AppendTests.third with sequence := 37}
def request (response : Option Nat := some 2048) : Backing.Registry.Allocate Nat :=
  fun _ bytes alignment effects => (if bytes == 320 && alignment == 8 then response else none, effects * 10 + 7)
def release : Backing.Release.External Nat := fun allocator base bytes alignment effects =>
  if allocator == 7 && base == 512 && bytes == 96 && alignment == 8 then effects * 10 + 8 else effects * 10 + 9
def calls : Growth.Registered.Callbacks Nat := ⟨.noRemap 999 777, release⟩
def execute (safety : Bool) (response : Option Nat := some 2048) :=
  runWithGrowth calls safety (request response) 7 3 AppendTests.cells fourth (before safety)

theorem initial_valid (safety : Bool) : Valid (before safety) := by
  have ready := RegistryTests.every_outcome_valid safety 4 2 31
  rw [AppendTests.actual_spare] at ready
  have registered := Backing.Registry.vector_write_valid
    ({RegistryTests.before safety with memory := AppendTests.after safety} : Session (List (Nat × Nat)))
    7 2 (DescriptorRelation.Tests.backing AppendTests.complete) AppendTests.cells ready (by cases safety <;> rfl) rfl
  exact ⟨registered.memory, registered.related, registered.injected⟩

theorem allocation_fits (safety : Bool) : RegionAllocation.Fits (before safety).memory ⟨320, 8⟩ 2048 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  change entry ∈ [(3, owner safety), (2, DescriptorRelation.Tests.backing AppendTests.complete),
    (1, Expression.Tests.argumentsAllocation), (0, Expression.Tests.itemAllocation)] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  all_goals cases safety <;> cases shaped <;> decide

theorem derived_contract (safety : Bool) : ∃ after,
    execute safety = (.ok true, after) ∧ Valid after ∧
    Compiler.Extraction.Memory.Vector 7 after.heap 4 (AppendTests.cells ++ [fourth]) ∧
    Backing.Release.Owned 7 ⟨4, 0⟩ 10 after ∧ after.heap 2 = none ∧ after.memory.heap.lookup 2 = none ∧
    after.effects = 78 ∧
    readHeader after.memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 4, .scalar (.int false 64 10)) ∧
    Prefix after.memory 4 (AppendTests.cells ++ [fourth]) ∧
    (∀ id, representativeFields after.memory ⟨3, 16⟩ id =
      .ok ((Storage.representativeProgram.run (AppendTests.cells ++ [fourth]) id).map (values id.toNat))) := by
  have owned : Backing.Release.Owned 7 ⟨2, 0⟩ 3 (before safety) :=
    ⟨rfl, ⟨AppendTests.cells, rfl⟩, DescriptorRelation.Tests.backing AppendTests.complete, by cases safety <;> rfl, rfl, rfl, rfl⟩
  obtain ⟨oldCell, after, oldFound, executed, valid, vector, freshOwned, dead, nativeDead, effects, _, _, _, header, rows, queries, _⟩ :=
    growing_verified safety request release 7 3 2 3 10 2048 999 777 (before safety) 7 (owner safety) AppendTests.cells fourth
      (initial_valid safety) (by cases safety <;> rfl) rfl rfl owned rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) rfl (allocation_fits safety) (by cases safety <;> rfl) (by cases safety <;> rfl)
      (AppendTests.spare_derived_queries safety).1 (by
        apply Owner.NativeLock.checkHeader_of_cell safety _ 3 (owner safety)
          (initial_valid safety).memory (by cases safety <;> rfl) rfl
        intro active
        subst safety
        rfl)
  have same : oldCell = DescriptorRelation.Tests.backing AppendTests.complete := Option.some.inj (oldFound.symm.trans (by cases safety <;> rfl))
  subst oldCell
  exact ⟨after, executed, valid, vector, freshOwned, dead, nativeDead, effects, header, rows, queries⟩

theorem all_outcomes_parent (safety : Bool) (callback : Remap.Callback) (allocator : Nat) (response : Option Nat) :
    let after := (runWithGrowth ⟨callback, release⟩ safety (request response) allocator 3 AppendTests.cells fourth (before safety)).2.memory
    after.valid = true ∧ after.heap.lookup 1 = some Expression.Tests.argumentsAllocation ∧ WordArray.Represents after ⟨1, 1, 2⟩ [99, 1] :=
  growth_parent_borrow ⟨callback, release⟩ safety (request response) allocator 3 AppendTests.cells fourth (before safety) (owner safety)
    (initial_valid safety) (by cases safety <;> rfl) rfl ⟨1, 1, 2⟩ [99, 1] 4 Expression.Tests.argumentsAllocation
    (by cases safety <;> rfl) rfl
    (represented_frame _ _ (DescriptorRelation.Tests.offset_borrow_still_live safety) (by cases safety <;> rfl))

theorem failed_growth (safety : Bool) :
    execute safety none = (.ok false, {before safety with effects := 7}) ∧
    execute safety (some 2049) = (.error (.memory .memoryValidity), {before safety with effects := 7}) ∧
    runWithGrowth ⟨.unsupported, release⟩ safety request 7 3 AppendTests.cells fourth (before safety) =
      (.error (.memory .unsupported), before safety) := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem wrong_allocator (safety : Bool) :
    runWithGrowth calls safety request 8 3 AppendTests.cells fourth (before safety) =
      (.error (.registry .wrongAllocator), before safety) := by cases safety <;> insertion_kernel_rfl

def damaged (safety : Bool) : Session Nat := {before safety with memory := {(before safety).memory with
  heap := (before safety).memory.heap.replace 2 (DescriptorRelation.Tests.backing (AppendTests.complete.filter (fun entry => entry.1 != 92)))}}
def readonly (safety : Bool) : Session Nat := {before safety with memory := {(before safety).memory with
  heap := (before safety).memory.heap.replace 3 {owner safety with writable := false}}}

theorem partial_copy (safety : Bool) :
    let result := runWithGrowth calls safety request 7 3 AppendTests.cells fourth (damaged safety)
    result.1 = .error (.memory .uninitialized) ∧ result.2.effects = 7 ∧
    result.2.heap 2 = some ⟨7, .representatives AppendTests.cells⟩ ∧ result.2.heap 4 = some ⟨7, .representatives []⟩ ∧
    readHeader result.2.memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨2, 0⟩ 3, .scalar (.int false 64 3)) := by
  cases safety <;> exact ⟨by decide +kernel, by decide +kernel, by insertion_kernel_rfl, by insertion_kernel_rfl, by decide +kernel⟩

theorem partial_publication (safety : Bool) :
    let result := runWithGrowth calls safety request 7 3 AppendTests.cells fourth (readonly safety)
    result.1 = .error (.memory .readOnly) ∧ result.2.effects = 78 ∧
    result.2.heap 2 = none ∧ result.2.memory.heap.lookup 2 = none ∧ result.2.heap 4 = some ⟨7, .representatives []⟩ ∧
    readHeader result.2.memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨2, 0⟩ 3, .scalar (.int false 64 3)) ∧
    result.2.memory.heap.lookup 1 = some Expression.Tests.argumentsAllocation := by
  cases safety <;> exact ⟨by decide +kernel, by decide +kernel, by insertion_kernel_rfl, by decide +kernel, by insertion_kernel_rfl, by decide +kernel, by decide +kernel⟩

end Compiler.Extraction.RepresentativeArray.Append.Registered.GrowthTests
