/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionDeinitNativeProofs
import Compiler.Extraction.AssemblyItemDeinitNativeTests

namespace Compiler.Extraction.ExpressionDeinit.Native.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- One initialized interior row in owned backing. Neighboring sentinel leaves
test the write footprint; this is not an initialized graph-prefix fixture. -/
def rowCells (arguments : Address := ⟨0, 0⟩) (length : Nat := 3) : Cells := [
  (24, .scalar (.int false 32 10)), (88, .scalar (.int false 32 20)),
  (32, .pointer Expression.itemType ⟨4, 0⟩),
  (40, .pointer (.pointer true true (.scalar (.int false 32))) arguments),
  (48, .scalar (.int false 64 length)), (56, .scalar (.int false 32 17)), (60, .scalar (.int false 32 23))]
def rowCell : Compiler.ZigAir.Memory.Allocation :=
  ⟨320, .array 3 Expression.allocationType, rowCells, true, false⟩
def before : Session Nat :=
  let previous := AssemblyItemDeinit.Native.Tests.before
  ⟨Memory.write previous.heap 5 (some ⟨7, .representatives []⟩),
    ⟨(5, rowCell) :: previous.memory.heap, 6, 416⟩, previous.effects⟩
def objects : AssemblyItem.Release Nat := fun id reached =>
  if (reached.memory.heap.lookup id).map (fun cell => cell.cells) = some [] then reached.effects * 10 + 3 else 999
def external : External Nat := { ExpressionDeinit.Tests.external with
  free := fun _ reached => if (reached.memory.heap.lookup 4).isNone &&
    Fields.item reached.memory ⟨5, 32⟩ == .ok ⟨4, 0⟩ then reached.effects * 10 + 4 else 999 }
def execute (state : Session Nat := before) := run AssemblyItemDeinit.Native.Tests.external objects external 7 ⟨5, 32⟩ state

theorem initial_valid : Valid before := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro allocator id values nonempty stored
    by_cases same : id = 5
    · subst id; simp [before, Memory.write] at stored
    · obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ :=
        AssemblyItemDeinit.Native.Tests.initial_valid.related allocator id values nonempty
          (by simpa [before, Memory.write, same] using stored)
      have frame : before.memory.heap.lookup id = AssemblyItemDeinit.Native.Tests.before.memory.heap.lookup id := by
        simp [before, Heap.lookup_cons, Ne.symm same]
      exact ⟨⟨cell, frame.trans found, typed, writable, stack⟩, represented_frame _ _ represented frame⟩
  · intro id allocation stored
    by_cases same : id = 5
    · subst id; exact ⟨rowCell, rfl, rfl⟩
    · obtain ⟨cell, found, persistent⟩ := AssemblyItemDeinit.Native.Tests.initial_valid.injected id allocation
        (by simpa [before, Memory.write, same] using stored)
      exact ⟨cell, by simpa [before, Heap.lookup_cons, Ne.symm same] using found, persistent⟩

theorem derived_contract : ∃ after, execute = (.ok (), after) ∧ Valid after.memory ∧
    after.invalidated = true ∧ after.memory.heap 5 = before.heap 5 ∧
    RepresentativeArray.Backing.Release.Owned 7 ⟨5, 0⟩ 3 after.memory := by
  have rowOwned : RepresentativeArray.Backing.Release.Owned 7 ⟨5, 0⟩ 3 before :=
    ⟨rfl, ⟨[], rfl⟩, rowCell, rfl, rfl, rfl, rfl⟩
  have itemOwned : AssemblyItem.Owned 7 4 before :=
    ⟨⟨AssemblyItemDeinit.Native.Tests.input.item, rfl⟩, AssemblyItemDeinit.Native.Tests.itemCell, rfl, rfl, rfl, rfl⟩
  have represented : AssemblyClone.NativeFields.Represents before.memory ⟨4, 0⟩ AssemblyItemDeinit.Native.Tests.input :=
    AssemblyItemDeinit.Native.Tests.initial_members.frame rfl
  obtain ⟨_, _, _, _, after, ran, _, _, _, _, _, _, _, _, _, _, _, marker, valid, registry, retained, _⟩ :=
    run_verified AssemblyItemDeinit.Native.Tests.external objects external 7 5 3 1 4
      AssemblyItemDeinit.Native.Tests.input Memory.Arguments.Tests.first before initial_valid rowOwned (by decide) itemOwned
      (by decide +kernel) (by decide +kernel) (Or.inr rfl) represented
      (by intro slice selected; cases Option.some.inj selected
          exact Or.inr ⟨rfl, AssemblyItemDeinit.Tests.cell, rfl, rfl, rfl, rfl, rfl⟩)
  exact ⟨after, ran, valid, marker, registry, retained⟩

theorem completed : execute.1 = .ok () ∧ execute.2.invalidated = true ∧ execute.2.memory.effects = 1334 ∧
    execute.2.memory.memory.heap.lookup 3 = none ∧ execute.2.memory.memory.heap.lookup 4 = none ∧
    execute.2.memory.memory.heap.lookup 0 = none ∧ execute.2.memory.heap 3 = none ∧
    execute.2.memory.heap 4 = none ∧ execute.2.memory.heap 0 = none :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem row_and_history : execute.2.memory.memory.heap.lookup 5 = some { rowCell with cells :=
    [(24, .scalar (.int false 32 10)), (88, .scalar (.int false 32 20))] } ∧
    execute.2.memory.memory.nextId = 6 ∧ execute.2.memory.memory.nextAddress = 416 ∧
    execute.2.memory.memory.heap.lookup 1 = before.memory.heap.lookup 1 ∧
    execute.2.memory.memory.heap.lookup 2 = before.memory.heap.lookup 2 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def withRow (cell : Compiler.ZigAir.Memory.Allocation) : Session Nat :=
  { before with memory := { before.memory with heap := before.memory.heap.replace 5 cell } }
def missingArguments := execute (withRow { rowCell with cells := rowCells.filter (fun entry => entry.1 != 48) })
theorem late_read_rejection : missingArguments.1 = .error (.fields (.memory .uninitialized)) ∧
    missingArguments.2.invalidated = false ∧ missingArguments.2.memory.effects = 133 ∧
    missingArguments.2.memory.memory.heap.lookup 3 = none ∧ missingArguments.2.memory.memory.heap.lookup 4 = none ∧
    missingArguments.2.memory.memory.heap.lookup 0 = before.memory.heap.lookup 0 ∧
    Fields.item missingArguments.2.memory.memory ⟨5, 32⟩ = .ok ⟨4, 0⟩ :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

def readonlyRow := execute (withRow { rowCell with writable := false })
theorem final_write_rejection : readonlyRow.1 = .error (.invalidation .readOnly) ∧
    readonlyRow.2.invalidated = false ∧ readonlyRow.2.memory.effects = 1334 ∧
    readonlyRow.2.memory.memory.heap.lookup 3 = none ∧ readonlyRow.2.memory.memory.heap.lookup 4 = none ∧
    readonlyRow.2.memory.memory.heap.lookup 0 = none ∧
    readonlyRow.2.memory.memory.heap.lookup 5 = some { rowCell with writable := false } :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

def readonlyItem :=
  let cell := { AssemblyItemDeinit.Native.Tests.itemCell with writable := false }
  let memory := { before.memory with heap := before.memory.heap.replace 4 cell }
  execute { before with memory }
theorem item_write_rejection : readonlyItem.1 = .error (.item (.memory .readOnly)) ∧
    readonlyItem.2.invalidated = false ∧ readonlyItem.2.memory.effects = 13 ∧
    readonlyItem.2.memory.memory.heap.lookup 3 = none ∧
    (readonlyItem.2.memory.memory.heap.lookup 4).isSome = true ∧
    readonlyItem.2.memory.memory.heap.lookup 0 = before.memory.heap.lookup 0 ∧
    readonlyItem.2.memory.memory.heap.lookup 5 = some rowCell :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

def offsetArguments := execute (withRow { rowCell with cells := rowCells ⟨0, 4⟩ 3 })
def shortArguments := execute (withRow { rowCell with cells := rowCells ⟨0, 0⟩ 2 })
def wrongOwner := execute (withRow { rowCell with cells := rowCells ⟨1, 0⟩ 1 })
theorem arguments_rejected : offsetArguments.1 = .error (.fields (.registry .bounds)) ∧
    shortArguments.1 = .error (.fields (.registry .bounds)) ∧
    wrongOwner.1 = .error (.arguments (.release (.ownership .wrongAllocator))) ∧
    offsetArguments.2.memory.effects = 133 ∧ shortArguments.2.memory.effects = 133 ∧ wrongOwner.2.memory.effects = 133 :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def emptyArguments := execute (withRow { rowCell with cells := rowCells ⟨5, 19⟩ 0 })
theorem empty_sentinel : emptyArguments.1 = .ok () ∧ emptyArguments.2.memory.effects = 133 ∧
    emptyArguments.2.invalidated = true ∧ emptyArguments.2.memory.memory.heap.lookup 0 = before.memory.heap.lookup 0 ∧
    (emptyArguments.2.memory.memory.heap.lookup 5).isSome = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem second_run_rejected : (execute execute.2.memory).1 = .error (.fields (.memory .uninitialized)) ∧
    (execute execute.2.memory).2.memory.effects = 1334 := ⟨by decide +kernel, by decide +kernel⟩

end Compiler.Extraction.ExpressionDeinit.Native.Tests
