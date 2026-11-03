/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionLastProofs
import Compiler.Extraction.InternerInsertionNativeDeinitTests
import Compiler.Extraction.ExpressionDeinitNativeTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.LastTests
open Compiler.ZigAir.Memory
open RepresentativeArray
open ExpressionDeinit.Native.Tests (rowCell)

def ownerCell (length : Nat := 2) (data : Address := ⟨5, 0⟩) : Compiler.ZigAir.Memory.Allocation :=
  ⟨768, Owner.viewType false,
    [(16, .pointer Publication.pointerType data), (24, .scalar (.int false 64 length)),
     (32, .scalar (.int false 64 3))], true, true⟩
def session : Session Nat :=
  let previous := ExpressionDeinit.Native.Tests.before
  { previous with memory := ⟨(6, ownerCell) :: previous.memory.heap, 7, 824⟩ }
def before : Frame Nat :=
  let original := CleanupTests.frame session
  { original with item := { original.item with object := some 999 }, duplicate := some ⟨1, [99]⟩ }
def ops : Operations Nat := { Insertion.Tests.ops with
  bytes := AssemblyItemDeinit.Native.Tests.external
  objects := ExpressionDeinit.Native.Tests.objects
  arguments := ExpressionDeinit.Native.Tests.external }
def execute (state : Frame Nat := before) := releaseLast ops 7 6 state

private theorem old_allocation (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation)
    (found : ExpressionDeinit.Native.Tests.before.memory.heap.lookup id = some cell) :
    session.memory.heap.lookup id = ExpressionDeinit.Native.Tests.before.memory.heap.lookup id := by
  have older := (valid_lookup _ id cell ExpressionDeinit.Native.Tests.initial_valid.memory found).1
  have apart : 6 ≠ id := by change id < 6 at older; omega
  simp only [session, Heap.lookup_cons, if_neg apart]

theorem initial_valid : Valid (memory before) := by
  have valid := ExpressionDeinit.Native.Tests.initial_valid
  have extended : Valid session := by
    apply Valid.memory_frame ExpressionDeinit.Native.Tests.before session.memory valid (by decide +kernel)
    · intro id cell found
      exact ⟨cell, (old_allocation id cell found).trans found, rfl, rfl, rfl, rfl⟩
    · intro allocator id values stored
      obtain ⟨cell, found, _⟩ := valid.injected id _ stored
      exact old_allocation id cell found
  exact ⟨extended.memory, extended.related, extended.injected⟩

theorem selected_last : Last.select (memory before).memory (Owner.headerAddress ⟨6, 0⟩) = .ok ⟨5, 32⟩ :=
  Last.from_array _ _ 5 3 1 rowCell initial_valid.memory rfl rfl rfl (by decide) (by decide +kernel)

theorem derived_contract : ∃ after, execute = (.ok (), after) ∧ Valid (memory after) ∧
    after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true ∧
    (memory after).heap 5 = (memory before).heap 5 := by
  have rowOwned : Backing.Release.Owned 7 ⟨5, 0⟩ 3 (memory before) :=
    ⟨rfl, ⟨[], rfl⟩, rowCell, rfl, rfl, rfl, rfl⟩
  have itemOwned : AssemblyItem.Owned 7 4 (memory before) :=
    ⟨⟨AssemblyItemDeinit.Native.Tests.input.item, rfl⟩, AssemblyItemDeinit.Native.Tests.itemCell, rfl, rfl, rfl, rfl⟩
  obtain ⟨_, after, _, ran, _, valid, object, clone, invalidated, registry⟩ := releaseLast_verified ops 7 6 5 3 1 4
    AssemblyItemDeinit.Native.Tests.input Memory.Arguments.Tests.first before initial_valid rowOwned (by decide)
    (by decide +kernel) itemOwned (by decide +kernel) (by decide +kernel) (Or.inr rfl)
    (AssemblyItemDeinit.Native.Tests.initial_members.frame rfl)
    (by intro slice selected; cases Option.some.inj selected
        exact Or.inr ⟨rfl, AssemblyItemDeinit.Tests.cell, rfl, rfl, rfl, rfl, rfl⟩)
  exact ⟨after, ran, valid, object, clone, invalidated, registry⟩

/-- Stale item/argument locals cannot override the selected native row. The
header and registry still retain its slot until the separate pop operation. -/
theorem actual_cleanup : execute.1 = .ok () ∧ (memory execute.2).effects.allocator = 1334 ∧
    (memory execute.2).memory.heap.lookup 3 = none ∧ (memory execute.2).memory.heap.lookup 4 = none ∧
    (memory execute.2).memory.heap.lookup 0 = none ∧
    (memory execute.2).memory.heap.lookup 1 = (memory before).memory.heap.lookup 1 ∧
    (memory execute.2).effects.keys Insertion.Tests.key = some ⟨5, 6⟩ ∧
    readItems (memory execute.2).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 2) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

def withAllocation (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation) : Frame Nat :=
  withMemory before { memory before with memory := { (memory before).memory with
    heap := (memory before).memory.heap.replace id cell } }
def missingArguments := execute (withAllocation 5 { rowCell with cells := rowCell.cells.filter (fun entry => entry.1 != 48) })
theorem late_failure : missingArguments.1 = .error (.expression (.fields (.memory .uninitialized))) ∧
    (memory missingArguments.2).effects.allocator = 133 ∧
    (memory missingArguments.2).memory.heap.lookup 3 = none ∧ (memory missingArguments.2).memory.heap.lookup 4 = none ∧
    (memory missingArguments.2).memory.heap.lookup 0 = (memory before).memory.heap.lookup 0 ∧
    missingArguments.2.item.object = some 999 ∧ missingArguments.2.item.clone.value.isSome = true ∧
    missingArguments.2.item.clone.execution.invalidated = false :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def empty := execute (withAllocation 6 (ownerCell 0 ⟨999, 19⟩))
def unbacked := execute (withAllocation 6 (ownerCell 2 ⟨999, 0⟩))
def outside := execute (withAllocation 6 (ownerCell 4))
theorem selection_failures : empty.1 = .error (.lastRow .sourceBounds) ∧
    unbacked.1 = .error (.lastRow .unallocated) ∧ outside.1 = .error (.lastRow .memoryValidity) ∧
    (memory empty.2).effects.allocator = 1 ∧ (memory unbacked.2).effects.allocator = 1 ∧
    (memory outside.2).effects.allocator = 1 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def readonly := execute (withAllocation 5 { rowCell with writable := false })
theorem final_write_failure : readonly.1 = .error (.expression (.invalidation .readOnly)) ∧
    (memory readonly.2).effects.allocator = 1334 ∧ readonly.2.item.object = some 999 ∧
    readonly.2.item.clone.execution.invalidated = false ∧
    (memory readonly.2).memory.heap.lookup 0 = none :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem repeated_cleanup : (execute execute.2).1 = .error (.expression (.fields (.memory .uninitialized))) ∧
    (memory (execute execute.2).2).effects.allocator = 1334 ∧
    (execute execute.2).2.item.clone.execution.invalidated = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.LastTests
