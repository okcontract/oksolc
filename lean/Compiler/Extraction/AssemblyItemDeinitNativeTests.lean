/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemDeinitNative
import Compiler.Extraction.AssemblyCloneFieldFixtures

namespace Compiler.Extraction.AssemblyItemDeinit.Native.Tests
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.ZigAir.Memory
open AssemblyItem.Fields

def input : AssemblyClone.NativeFields.ItemValue :=
  { AssemblyItem.Creation.NativeFields.Tests.input with verbatim := some ⟨2, 3, ⟨3, [7, 8, 9], 0⟩⟩ }
def itemCell : Compiler.ZigAir.Memory.Allocation := { AssemblyItem.Creation.cell 80 with
  cells := (AssemblyItem.Creation.NativeFields.Tests.expectedCells 3 0).map fun (offset, value) =>
    (offset, if offset = 80 then MemberTests.verbatimValue (some (MemberTests.payload 2 3 ⟨3, 0⟩ 3)) else value) }
def before : Session Nat :=
  ⟨Memory.write AssemblyItemDeinit.Tests.initial.heap 4 (some ⟨7, .item input.item⟩),
    ⟨(4, itemCell) :: AssemblyItemDeinit.Tests.initial.memory.heap, 5, 304⟩, 1⟩
def external : Release Nat := fun slice reached => reached.effects * 10 + slice.length
def observed := run external 7 ⟨4, 0⟩ before

theorem initial_valid : Valid before := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro allocator id contents nonempty stored
    by_cases same : id = 4
    · subst id; simp [before, Memory.write] at stored
    · obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ :=
        AssemblyItemDeinit.Tests.initial_valid.related allocator id contents nonempty
          (by simpa [before, Memory.write, same] using stored)
      have frame : before.memory.heap.lookup id = AssemblyItemDeinit.Tests.initial.memory.heap.lookup id := by
        simp [before, Heap.lookup_cons, Ne.symm same]
      exact ⟨⟨cell, frame.trans found, typed, writable, stack⟩, represented_frame _ _ represented frame⟩
  · intro id allocation stored
    by_cases same : id = 4
    · subst id; exact ⟨itemCell, rfl, rfl⟩
    · obtain ⟨cell, found, persistent⟩ := AssemblyItemDeinit.Tests.initial_valid.injected id allocation
        (by simpa [before, Memory.write, same] using stored)
      exact ⟨cell, by simpa [before, Heap.lookup_cons, Ne.symm same] using found, persistent⟩

theorem initial_members : AssemblyClone.NativeFields.Represents before.memory ⟨4, 0⟩ input := by
  intro selected; cases selected <;> decide +kernel

theorem initial_ownership : AssemblyItem.Owned 7 4 before ∧ Owned 7 ⟨3, 3, 0⟩ before :=
  ⟨⟨⟨input.item, rfl⟩, itemCell, rfl, rfl, rfl, rfl⟩,
    Or.inr ⟨rfl, AssemblyItemDeinit.Tests.cell, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem derived_contract : ∃ released after, observed = (.ok (), after) ∧
    AssemblyItemDeinit.Post (some ⟨3, 3, 0⟩) before released ∧
    invalidate released.memory.memory true AssemblyItem.viewType ⟨4, 0⟩ = .ok after.memory.memory ∧
    Valid after.memory ∧ AssemblyItem.Owned 7 4 after.memory ∧ after.memory.effects = 13 := by
  obtain ⟨released, after, executed, _, post, invalidated, valid, owned, _, _, _⟩ :=
    run_verified external 7 4 input before initial_valid initial_ownership.1 initial_members
      (by intro slice selected; cases Option.some.inj selected; exact initial_ownership.2)
  refine ⟨released, after, executed, post, invalidated, valid, owned, ?_⟩
  have effect : observed.2.memory.effects = 13 := by decide +kernel
  rw [observed, executed] at effect
  exact effect

theorem actual_destruction : observed.1 = .ok () ∧ observed.2.invalidated = true ∧
    observed.2.memory.heap 3 = none ∧ observed.2.memory.memory.heap.lookup 3 = none ∧
    observed.2.memory.memory.heap.lookup 4 = some { itemCell with cells := [] } ∧
    observed.2.memory.effects = 13 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem all_members_uninitialized (selected : Member) :
    member observed.2.memory.memory ⟨4, 0⟩ selected = .error .uninitialized := by
  cases selected <;> decide +kernel

theorem history_and_arguments : observed.2.memory.memory.nextId = 5 ∧ observed.2.memory.memory.nextAddress = 304 ∧
    observed.2.memory.memory.heap.lookup 0 = before.memory.heap.lookup 0 ∧
    observed.2.memory.memory.heap.lookup 1 = before.memory.heap.lookup 1 ∧
    observed.2.memory.memory.heap.lookup 2 = before.memory.heap.lookup 2 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def withItem (cell : Compiler.ZigAir.Memory.Allocation) : Session Nat :=
  { before with memory := { before.memory with heap := before.memory.heap.replace 4 cell } }
def withPayload (value : Compiler.ZigAir.Memory.Value) : Session Nat :=
  withItem { itemCell with cells := itemCell.cells.map fun (offset, old) => (offset, if offset = 80 then value else old) }
def variant (payload : Option ObjectValue) := withPayload (MemberTests.verbatimValue payload)
def absent := run external 99 ⟨4, 0⟩ (variant none)
def empty := run external 99 ⟨4, 0⟩ (variant (some (MemberTests.payload 2 3 ⟨999, 17⟩ 0)))

theorem absent_and_empty : absent.1 = .ok () ∧ empty.1 = .ok () ∧
    absent.2.memory.effects = 1 ∧ empty.2.memory.effects = 1 ∧
    absent.2.memory.memory.heap.lookup 3 = before.memory.heap.lookup 3 ∧
    empty.2.memory.memory.heap.lookup 3 = before.memory.heap.lookup 3 ∧
    member absent.2.memory.memory ⟨4, 0⟩ .verbatim = .error .uninitialized ∧
    member empty.2.memory.memory ⟨4, 0⟩ .verbatim = .error .uninitialized :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem rejected_payload :
    (run external 7 ⟨4, 0⟩ (variant (some (MemberTests.payload 2 3 ⟨3, 1⟩ 3)))).1 = .error (.payload (.release (.ownership .bounds))) ∧
    (run external 7 ⟨4, 0⟩ (variant (some (MemberTests.payload 2 3 ⟨3, 0⟩ 2)))).1 = .error (.payload (.release (.ownership .bounds))) ∧
    (run external 8 ⟨4, 0⟩ before).1 = .error (.payload (.release (.ownership .wrongAllocator))) ∧
    (run external 8 ⟨4, 0⟩ before).2.memory.effects = 1 ∧
    (run external 8 ⟨4, 0⟩ before).2.memory.memory = before.memory ∧
    (run external 8 ⟨4, 0⟩ before).2.invalidated = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def readonly := run external 7 ⟨4, 0⟩ (withItem { itemCell with writable := false })
theorem failed_invalidation_keeps_release : readonly.1 = .error (.memory .readOnly) ∧
    readonly.2.invalidated = false ∧ readonly.2.memory.heap 3 = none ∧
    readonly.2.memory.memory.heap.lookup 3 = none ∧ readonly.2.memory.effects = 13 ∧
    readonly.2.memory.memory.heap.lookup 4 = some { itemCell with writable := false } :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem field_failures :
    (run external 7 ⟨4, 0⟩ (withItem { itemCell with cells := [] })).1 = .error (.memory .uninitialized) ∧
    (run external 7 ⟨999, 0⟩ before).1 = .error (.memory .unallocated) ∧
    (run external 7 ⟨4, 0⟩ observed.2.memory).1 = .error (.memory .uninitialized) ∧
    (run external 7 ⟨4, 0⟩ (withPayload (.scalar (.int false 64 0)))).1 = .error (.memory .malformed) ∧
    (run external 7 ⟨4, 0⟩ (withItem { itemCell with cells := [] })).2.memory.effects = 1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem projection_preserves_offset : readPayload
    (variant (some (MemberTests.payload 2 3 ⟨3, 1⟩ 3))).memory ⟨4, 0⟩ = .ok (some ⟨3, 3, 1⟩) := by decide +kernel

end Compiler.Extraction.AssemblyItemDeinit.Native.Tests
