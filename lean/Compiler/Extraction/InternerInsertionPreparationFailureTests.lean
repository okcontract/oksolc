/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparationFailure
import Compiler.Extraction.InternerInsertionPreparationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.PreparationFailureTests
open Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open AssemblyClone.NativeFields.QueryTests (old)
open AssemblyItem.Creation.NativeFields.Tests (input source)
open AppendOwnershipTests (initial initial_valid key)

abbrev allocate := AppendOwnershipTests.allocate

def normalized (empty : Bool) : Storage.ArgumentSlice := if empty then ⟨9, []⟩ else PreparationTests.normalized
def operands (empty : Bool) : Storage.ArgumentSlice := ⟨9, (normalized empty).items⟩
def handle (empty : Bool) : Handle := ⟨view (normalized empty), (normalized empty).items, none⟩
def ops (failure : Storage.Allocation) : Operations Nat := { PreparationTests.ops with
  arguments := { (Insertion.Tests.ops (some failure)).arguments with free := PreparationTests.ops.arguments.free }
  create := fun wanted before => if failure = .item then (none, before.effects * 10 + 5)
    else PreparationTests.ops.create wanted before
  copy := fun wanted before => if failure = .clone then (none, before.effects * 10 + 6)
    else PreparationTests.ops.copy wanted before }

theorem admitted (failure : Storage.Allocation) : Admitted (ops failure).arguments :=
  Insertion.Tests.admitted (some failure)
theorem live (safety empty : Bool) : Memory.SliceValid 7 (initial safety).heap (normalized empty) := by
  cases empty
  · exact Or.inr (by rfl')
  · exact Or.inl rfl
theorem represented (safety : Bool) : AssemblyClone.NativeFields.Represents (initial safety).memory source input :=
  AssemblyItem.Creation.NativeFields.Tests.source_represented.frame
    ((AppendOwnershipTests.initial_frame safety 5 (by decide)).trans
      (AssemblyClone.NativeFields.QueryTests.initial_frame safety false 5 (by decide)))

def taken (safety empty : Bool) (failure : Storage.Allocation) :=
  takeOwned normalizationOwnershipCode (Publication.external (ops failure).arguments) 7 (handle empty) (initial safety)
def made (safety empty : Bool) (failure : Storage.Allocation) :=
  AssemblyItem.Creation.create (observe (ops failure).create) 7 input.item (taken safety empty failure).2
def cloned (safety empty : Bool) :=
  AssemblyClone.Physical.run (observe (ops .clone).copy) 7 input (made safety empty .clone).2
def execute (safety empty : Bool) (failure : Storage.Allocation) :=
  execution (ops failure) allocate safety 7 6 ⟨2, 0, 0⟩ source Insertion.Tests.model input key
    (normalized empty) true [old] (PreparationTests.world safety)

theorem failure_results (safety empty : Bool) :
    taken safety false .arguments = (.error .outOfMemory, (taken safety false .arguments).2) ∧
    taken safety empty .item = (.ok (operands empty, handle empty), (taken safety empty .item).2) ∧
    made safety empty .item = (.error .outOfMemory, (made safety empty .item).2) ∧
    taken safety empty .clone = (.ok (operands empty, handle empty), (taken safety empty .clone).2) ∧
    made safety empty .clone = (.ok (if empty then 9 else 10), (made safety empty .clone).2) ∧
    cloned safety empty = (.error .outOfMemory, (cloned safety empty).2) := by
  cases safety <;> cases empty <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem duplicate_contract (safety : Bool) :
    Valid (memory (execute safety false .arguments).2) ∧
    Consumed (normalized false) (memory (execute safety false .arguments).2) := by
  obtain ⟨after, executed, valid, consumed, _⟩ := duplicate_oom_execution (ops .arguments) allocate safety 7 6 ⟨2, 0, 0⟩ source
    Insertion.Tests.model input key (normalized false) [old] (PreparationTests.world safety) (taken safety false .arguments).2
    (initial_valid safety) (live safety false) (admitted .arguments) (by decide) (failure_results safety false).1
  change execute safety false .arguments = _ at executed
  rw [executed]
  exact ⟨valid, consumed⟩

theorem create_contract (safety empty : Bool) :
    Valid (memory (execute safety empty .item).2) ∧
    Consumed (operands empty) (memory (execute safety empty .item).2) ∧
    Consumed (normalized empty) (memory (execute safety empty .item).2) := by
  have results := failure_results safety empty
  obtain ⟨freed, after, executed, valid, consumed, normalizedConsumed, _⟩ := create_oom_execution (ops .item) allocate safety
    7 6 ⟨2, 0, 0⟩ source Insertion.Tests.model input key (normalized empty) (operands empty) [old] (PreparationTests.world safety)
    (taken safety empty .item).2 (made safety empty .item).2 (handle empty)
    (initial_valid safety) (live safety empty) (admitted .item) (by decide) results.2.1 results.2.2.1
  change execute safety empty .item = _ at executed
  rw [executed]
  exact ⟨valid, consumed, normalizedConsumed⟩

theorem clone_contract (safety empty : Bool) :
    Valid (memory (execute safety empty .clone).2) ∧
    Consumed (operands empty) (memory (execute safety empty .clone).2) ∧
    Consumed (normalized empty) (memory (execute safety empty .clone).2) := by
  have results := failure_results safety empty
  obtain ⟨destroyed, freed, after, executed, valid, consumed, normalizedConsumed, _⟩ := clone_oom_execution (ops .clone) allocate safety
    7 6 (if empty then 9 else 10) ⟨2, 0, 0⟩ source Insertion.Tests.model input key (normalized empty) (operands empty) [old]
    (PreparationTests.world safety) (taken safety empty .clone).2 (made safety empty .clone).2 (cloned safety empty).2 (handle empty)
    (initial_valid safety) (live safety empty) (represented safety) (admitted .clone) (by decide)
    results.2.2.2.1 results.2.2.2.2.1 results.2.2.2.2.2
  change execute safety empty .clone = _ at executed
  rw [executed]
  exact ⟨valid, consumed, normalizedConsumed⟩

/-- Decimal traces distinguish each actual attempted allocation and each free;
the empty sentinels alias the new object lifetime but are never freed. -/
theorem cleanup_effects (safety empty : Bool) :
    (memory (execute safety false .arguments).2).effects.allocator = 15 ∧
    (memory (execute safety empty .item).2).effects.allocator = (if empty then 5 else 1545) ∧
    (memory (execute safety empty .clone).2).effects.allocator = (if empty then 563 else 156345) ∧
    (execute safety empty .clone).1.1 = .ok (some .allocationFailure) ∧
    (execute safety empty .item).1.1 = .ok (some .allocationFailure) := by
  cases safety <;> cases empty <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem allocation_history (safety empty : Bool) :
    (memory (execute safety false .arguments).2).memory.nextId = 9 ∧
    (memory (execute safety empty .item).2).memory.nextId = (if empty then 9 else 10) ∧
    (memory (execute safety empty .clone).2).memory.nextId = (if empty then 10 else 11) ∧
    (memory (execute safety empty .clone).2).memory.nextAddress = (made safety empty .clone).2.memory.nextAddress ∧
    ([9, 10, 11].map fun id => ((memory (execute safety empty .clone).2).memory.heap.lookup id).isNone) = [true, true, true] ∧
    (execute safety empty .clone).2.item.object = none ∧ (execute safety empty .clone).2.item.clone.value = none := by
  cases safety <;> cases empty <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl,
    by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem original_allocations (safety empty : Bool) :
    ([0, 1, 3, 5, 6, 7].map fun id => (memory (execute safety empty .clone).2).memory.heap.lookup id) =
      ([0, 1, 3, 5, 6, 7].map fun id => (initial safety).memory.heap.lookup id) ∧
    (memory (execute safety empty .clone).2).memory.heap.lookup 8 = (if empty then (initial safety).memory.heap.lookup 8 else none) := by
  cases safety <;> cases empty <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.PreparationFailureTests
