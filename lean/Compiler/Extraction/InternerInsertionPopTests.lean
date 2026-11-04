/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionLastTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.PopTests
open Compiler.ZigAir.Memory
open RepresentativeArray
open ExpressionDeinit.Native.Tests (rowCell)
open AssemblyClone.NativeFields.QueryTests (old logical)

/-- Supply the initial vector registration missing from the isolated destructor
fixture. This tests pop and cleanup, not complete native graph correspondence. -/
def before : Frame Nat := withMemory LastTests.before { memory LastTests.before with
  heap := Memory.write (memory LastTests.before).heap 5 (some ⟨7, .representatives [old, logical]⟩) }
def cleaned := releaseLast LastTests.ops 7 6 before
def execute := pop 7 6 cleaned.2

theorem initial_valid : Valid (memory before) :=
  Backing.Registry.vector_write_valid (memory LastTests.before) 7 5 rowCell [old, logical] LastTests.initial_valid rfl rfl

theorem cleanup_valid : cleaned.1 = .ok () ∧ Valid (memory cleaned.2) ∧
    Memory.Vector 7 (memory cleaned.2).heap 5 [old, logical] := by
  have rowOwned : Backing.Release.Owned 7 ⟨5, 0⟩ 3 (memory before) :=
    ⟨rfl, ⟨[old, logical], rfl⟩, rowCell, rfl, rfl, rfl, rfl⟩
  have itemOwned : AssemblyItem.Owned 7 4 (memory before) :=
    ⟨⟨AssemblyItemDeinit.Native.Tests.input.item, rfl⟩, AssemblyItemDeinit.Native.Tests.itemCell, rfl, rfl, rfl, rfl⟩
  obtain ⟨_, after, _, ran, _, valid, _, _, _, registry⟩ := releaseLast_verified LastTests.ops 7 6 5 3 1 4
    AssemblyItemDeinit.Native.Tests.input Memory.Arguments.Tests.first before initial_valid rowOwned (by decide)
    (by decide +kernel) itemOwned (by decide +kernel) (by decide +kernel) (Or.inr rfl)
    (AssemblyItemDeinit.Native.Tests.initial_members.frame rfl)
    (by intro slice selected; cases Option.some.inj selected
        exact Or.inr ⟨rfl, AssemblyItemDeinit.Tests.cell, rfl, rfl, rfl, rfl, rfl⟩)
  change releaseLast LastTests.ops 7 6 before = (.ok (), after) at ran
  unfold cleaned
  rw [ran]
  exact ⟨rfl, valid, registry.trans rfl⟩

def cleanedBacking : Compiler.ZigAir.Memory.Allocation := { rowCell with cells :=
  [(24, .scalar (.int false 32 10)), (88, .scalar (.int false 32 20))] }

theorem derived_contract : ∃ after, Pop.Registered.run 7 6 (memory cleaned.2) = (.ok (), after) ∧ Valid after ∧
    Memory.Vector 7 after.heap 5 [old] ∧
    readHeader after.memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 1, .scalar (.int false 64 3)) := by
  obtain ⟨after, ran, valid, _, vector, _, header, _⟩ := Pop.Registered.verified false (memory cleaned.2)
    7 6 5 3 (LastTests.ownerCell) cleanedBacking [old] logical cleanup_valid.2.1
    (by decide +kernel) rfl rfl (by decide +kernel) rfl (by decide +kernel) (by decide +kernel)
    cleanup_valid.2.2 (by decide)
  exact ⟨after, ran, valid, vector, header⟩

theorem vector_restored : (memory execute.2).heap 5 = some ⟨7, .representatives [old]⟩ := by
  obtain ⟨after, ran, _, vector, _⟩ := derived_contract
  rw [execute, pop_memory, ran]
  exact vector

theorem completed : execute.1 = .ok () ∧ (memory execute.2).heap 5 = some ⟨7, .representatives [old]⟩ ∧
    readHeader (memory execute.2).memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨5, 0⟩ 1, .scalar (.int false 64 3)) ∧
    (memory execute.2).effects.allocator = 1334 ∧
    (memory execute.2).memory.heap.lookup 5 = some cleanedBacking ∧
    (memory execute.2).memory.nextId = 7 ∧ (memory execute.2).memory.nextAddress = 824 ∧
    (memory execute.2).memory.heap.lookup 0 = none ∧ (memory execute.2).memory.heap.lookup 3 = none ∧
    (memory execute.2).memory.heap.lookup 4 = none ∧
    (memory execute.2).memory.heap.lookup 1 = (memory before).memory.heap.lookup 1 ∧
    (memory execute.2).effects.keys Insertion.Tests.key = some ⟨5, 6⟩ ∧ execute.2.item.clone.execution.invalidated = true :=
  ⟨by decide +kernel, vector_restored, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

def withOwner (cell : Compiler.ZigAir.Memory.Allocation) : Frame Nat :=
  withMemory cleaned.2 { memory cleaned.2 with memory := { (memory cleaned.2).memory with
    heap := (memory cleaned.2).memory.heap.replace 6 cell } }
def readonly := pop 7 6 (withOwner { LastTests.ownerCell with writable := false })
def missingPointer := pop 7 6 (withOwner { LastTests.ownerCell with cells :=
  [(24, .scalar (.int false 64 2)), (32, .scalar (.int false 64 3))] })

def vectorLength (state : Frame Nat) : Option Nat :=
  match (memory state).heap 5 with
  | some ⟨7, .representatives cells⟩ => some cells.length
  | _ => none

theorem write_rejected : readonly.1 = .error (.pop (.memory .readOnly)) ∧
    (memory readonly.2).effects.allocator = 1334 ∧ (memory readonly.2).memory.heap.lookup 0 = none ∧
    readItems (memory readonly.2).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 2) ∧
    vectorLength readonly.2 = some 2 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem late_read_rejected : missingPointer.1 = .error (.pop (.memory .uninitialized)) ∧
    readField (memory missingPointer.2).memory (Owner.headerAddress ⟨6, 0⟩) Append.lengthOffset = .ok (.scalar (.int false 64 1)) ∧
    (memory missingPointer.2).effects.allocator = 1334 ∧
    vectorLength missingPointer.2 = some 2 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def registry (entry : Option Memory.Allocation) := pop 7 6 (withMemory cleaned.2 { memory cleaned.2 with
  heap := Memory.write (memory cleaned.2).heap 5 entry })

theorem registry_rejected : (registry none).1 = .error (.pop (.registry .unallocated)) ∧
    (registry (some ⟨8, .representatives [old, logical]⟩)).1 = .error (.pop (.registry .wrongAllocator)) ∧
    (registry (some ⟨7, .arguments []⟩)).1 = .error (.pop (.registry .wrongType)) ∧
    (registry (some ⟨7, .representatives [old]⟩)).1 = .error (.pop (.registry .bounds)) ∧
    (registry (some ⟨7, .representatives [old, logical, logical]⟩)).1 = .error (.pop (.registry .bounds)) ∧
    readItems (memory (registry none).2).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 1) ∧
    (memory (registry none).2).effects.allocator = 1334 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

def empty := pop 7 6 (withOwner (LastTests.ownerCell 0 ⟨999, 19⟩))
def offset := pop 7 6 (withOwner (LastTests.ownerCell 2 ⟨5, 32⟩))
theorem boundary_rejected : empty.1 = .error (.pop (.memory .sourceBounds)) ∧
    readField (memory empty.2).memory (Owner.headerAddress ⟨6, 0⟩) Append.lengthOffset = .ok (.scalar (.int false 64 0)) ∧
    offset.1 = .error (.pop (.memory .malformed)) ∧
    readField (memory offset.2).memory (Owner.headerAddress ⟨6, 0⟩) Append.lengthOffset = .ok (.scalar (.int false 64 1)) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.PopTests
