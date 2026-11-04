/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionOuterCleanup
import Compiler.Extraction.InternerInsertionRollbackTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.OuterCleanupTests
open Compiler.ZigAir.Memory
open RepresentativeArray
open AssemblyClone.NativeFields.QueryTests (old logical)

/-- The normalized buffer has the insertion allocator. Keep the same actual
native allocations and independently owned selected row as the rollback fixture. -/
def before (safety persistent empty : Bool) : Frame Nat :=
  let prior := RollbackTests.before safety persistent empty
  withMemory prior { memory prior with heap := Memory.write (memory prior).heap 1 (some ⟨7, .arguments [99]⟩) }
def normalized (empty : Bool) : Storage.ArgumentSlice := if empty then ⟨6, []⟩ else ⟨1, [99]⟩
def ops : Operations Nat := { LastTests.ops with arguments := { LastTests.ops.arguments with
  free := fun slice reached => if slice.address = 1 then
    if readItems reached.memory (Owner.headerAddress ⟨6, 0⟩) == .ok (.slice itemsType ⟨5, 0⟩ 1) &&
      (reached.memory.heap.lookup 4).isNone then reached.effects * 10 + 5 else 999
    else LastTests.ops.arguments.free slice reached } }
def calls (safety outerEmpty : Bool) := callbacks ops (fun _ _ _ effects => (none, effects)) safety 7 6
  ⟨1, 0, 1⟩ ⟨2, 0⟩ AssemblyItem.Creation.NativeFields.Tests.input Insertion.Tests.key (normalized outerEmpty) [old] 0
  (fun _ _ => Interner.observedHeap [] (fun _ => none))
def execute (safety persistent empty outerEmpty : Bool) :=
  (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute (calls safety outerEmpty)
    RollbackTests.ownership (before safety persistent empty)

theorem initial_valid (safety persistent empty : Bool) : Valid (memory (before safety persistent empty)) := by
  have prior := RollbackTests.initial_valid safety persistent empty
  refine ⟨prior.memory, ?_, ?_⟩
  · intro allocator id values nonempty registered
    by_cases same : id = 1
    · subst id
      have pair : allocator = 7 ∧ values = [99] := by
        simpa [before, memory, withMemory, Memory.write] using registered.symm
      rcases pair with ⟨rfl, rfl⟩
      exact prior.related 11 1 [99] (by decide) rfl
    · exact prior.related allocator id values nonempty (by simpa [before, memory, withMemory, Memory.write, same] using registered)
  · intro id block registered
    by_cases same : id = 1
    · subst id
      exact ⟨Memory.Arguments.Tests.secondCell,
        (RollbackTests.lookup_other safety persistent empty 1 (by decide) (by decide)).trans rfl, rfl⟩
    · exact prior.injected id block (by simpa [before, memory, withMemory, Memory.write, same] using registered)

/-- The universal theorem supplies both reached validity and the final cleanup;
no post-destruction ownership is assumed by this fixture. -/
theorem derived_contract (safety persistent empty outerEmpty : Bool) : ∃ after,
    execute safety persistent empty outerEmpty =
      ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run RollbackTests.ownership), after) ∧
    Valid (memory after) ∧ Memory.Vector 7 (memory after).heap 5 [old] ∧
    readHeader (memory after).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 1, .scalar (.int false 64 3)) ∧
    (memory after).memory.nextId = 7 ∧ (memory after).memory.nextAddress = (768 + (Owner.layout safety).bytes) := by
  have rowOwned : Backing.Release.Owned 7 ⟨5, 0⟩ 3 (memory (before safety persistent empty)) :=
    ⟨rfl, ⟨[old, logical], rfl⟩, RollbackTests.backing empty,
      by cases safety <;> cases persistent <;> cases empty <;> decide +kernel,
      by cases empty <;> rfl, by cases empty <;> rfl, by cases empty <;> rfl⟩
  have itemOwned : AssemblyItem.Owned 7 4 (memory (before safety persistent empty)) :=
    ⟨⟨AssemblyItemDeinit.Native.Tests.input.item, rfl⟩, AssemblyItemDeinit.Native.Tests.itemCell,
      (RollbackTests.lookup_other safety persistent empty 4 (by decide) (by decide)).trans rfl, rfl, rfl, rfl⟩
  have represented := AssemblyItemDeinit.Native.Tests.initial_members.frame
    ((RollbackTests.lookup_other safety persistent empty 4 (by decide) (by decide)).trans rfl)
  obtain ⟨_, after, _, ran, _, valid, vector, header, _, _, nextId, nextAddress, _⟩ := rollback_normalized_verified ops
    (fun _ _ _ effects => (none, effects)) safety 7 6 5 3 4 (RollbackTests.ownerCell safety persistent)
    ⟨1, 0, 1⟩ ⟨2, 0⟩ AssemblyItem.Creation.NativeFields.Tests.input AssemblyItemDeinit.Native.Tests.input Insertion.Tests.key
    (normalized outerEmpty) (RollbackTests.arguments empty) [old] logical 0 (fun _ _ => Interner.observedHeap [] (fun _ => none)) RollbackTests.ownership
    (before safety persistent empty) (initial_valid safety persistent empty)
    (by cases safety <;> cases persistent <;> cases empty <;> decide +kernel) rfl rfl rowOwned (by decide)
    (by cases safety <;> cases persistent <;> cases empty <;> decide +kernel)
    (by cases safety <;> cases persistent <;> cases empty <;> decide +kernel) rfl itemOwned
    (by cases safety <;> cases persistent <;> cases empty <;> decide +kernel)
    (by cases safety <;> cases persistent <;> cases empty <;> decide +kernel)
    (by cases empty; exact Or.inr rfl; exact Or.inl rfl) represented
    (by intro slice selected; cases Option.some.inj selected
        exact Or.inr ⟨rfl, AssemblyItemDeinit.Tests.cell,
          (RollbackTests.lookup_other safety persistent empty 3 (by decide) (by decide)).trans rfl, rfl, rfl, rfl, rfl⟩)
      (by cases outerEmpty; exact Or.inr rfl; exact Or.inl rfl)
      (by cases outerEmpty <;> cases empty <;> simp [normalized, RollbackTests.arguments, Memory.Arguments.Tests.first])
  exact ⟨after, ran, valid, vector, header, nextId, nextAddress⟩

theorem effects_and_death (safety persistent empty outerEmpty : Bool) :
    (memory (execute safety persistent empty outerEmpty).2).effects.allocator =
      (if outerEmpty then (if empty then 133 else 1334) else (if empty then 1335 else 13345)) ∧
    (memory (execute safety persistent empty outerEmpty).2).memory.heap.lookup 1 =
      (if outerEmpty then some Memory.Arguments.Tests.secondCell else none) := by
  cases safety <;> cases persistent <;> cases empty <;> cases outerEmpty <;> exact ⟨by decide +kernel, by decide +kernel⟩

def aliasFailure :=
  (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute
    (callbacks LastTests.ops (fun _ _ _ effects => (none, effects)) false 7 6
      ⟨1, 0, 1⟩ ⟨2, 0⟩ AssemblyItem.Creation.NativeFields.Tests.input Insertion.Tests.key Memory.Arguments.Tests.first [old] 0
      (fun _ _ => Interner.observedHeap [] (fun _ => none))) RollbackTests.ownership (before false false false)

theorem alias_rejected_after_pop : aliasFailure.1.1 = .error (.base (.arguments (.release (.ownership .unallocated)))) ∧
    aliasFailure.1.2.appended = false ∧ aliasFailure.1.2.owner .normalized = .local ∧
    (memory aliasFailure.2).effects.allocator = 1334 ∧
    readItems (memory aliasFailure.2).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 1) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def wrongAllocator := (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute
  (calls false false) RollbackTests.ownership (RollbackTests.before false false false)
theorem wrong_allocator_rejected : wrongAllocator.1.1 = .error (.base (.arguments (.release (.ownership .wrongAllocator)))) ∧
    (memory wrongAllocator.2).memory.heap.lookup 1 = some Memory.Arguments.Tests.secondCell ∧
    (memory wrongAllocator.2).effects.allocator = 1334 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.OuterCleanupTests
