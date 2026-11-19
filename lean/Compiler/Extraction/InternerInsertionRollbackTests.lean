/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionRollbackProofs
import Compiler.Extraction.InternerInsertionPopTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.RollbackTests
open Compiler.ZigAir.Memory
open RepresentativeArray
open AssemblyClone.NativeFields.QueryTests (old logical)
open ExpressionDeinit.Native.Tests (rowCell rowCells)

def ownerCell (safety persistent : Bool) : Compiler.ZigAir.Memory.Allocation :=
  { LastTests.ownerCell with type := Owner.viewType safety, stack := !persistent }
def backing (empty : Bool) : Compiler.ZigAir.Memory.Allocation :=
  if empty then { rowCell with cells := rowCells ⟨6, 0⟩ 0 } else rowCell
def arguments (empty : Bool) : Storage.ArgumentSlice :=
  if empty then ⟨6, []⟩ else Memory.Arguments.Tests.first
def before (safety persistent empty : Bool) : Frame Nat :=
  withMemory PopTests.before { memory PopTests.before with memory := {
    (memory PopTests.before).memory with
    heap := ((memory PopTests.before).memory.heap.replace 6 (ownerCell safety persistent)).replace 5 (backing empty)
    nextAddress := 768 + (Owner.layout safety).bytes } }

theorem lookup_other (safety persistent empty : Bool) (id : Nat) (notRow : id ≠ 5) (notOwner : id ≠ 6) :
    (memory (before safety persistent empty)).memory.heap.lookup id = (memory PopTests.before).memory.heap.lookup id :=
  (replace_other _ _ _ _ notRow).trans (replace_other _ _ _ _ notOwner)

theorem initial_valid (safety persistent empty : Bool) : Valid (memory (before safety persistent empty)) := by
  have oldValid := PopTests.initial_valid
  have notOwner (id : Nat) (block : Memory.Allocation) (registered : (memory (before safety persistent empty)).heap id = some block) : id ≠ 6 := by
    intro same
    subst id
    change none = some block at registered
    cases registered
  refine ⟨by cases safety <;> cases persistent <;> cases empty <;> decide +kernel, ?_, ?_⟩
  · intro allocator id values nonempty registered
    have notRow : id ≠ 5 := by
      intro same
      subst id
      change (some ⟨7, .representatives [old, logical]⟩ : Option Memory.Allocation) = some ⟨allocator, .arguments values⟩ at registered
      cases registered
    obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ := oldValid.related allocator id values nonempty registered
    have kept := lookup_other safety persistent empty id notRow (notOwner id _ registered)
    exact ⟨⟨cell, kept.trans found, typed, writable, stack⟩, represented_frame _ values represented kept⟩
  · intro id block registered
    by_cases same : id = 5
    · subst id
      exact ⟨backing empty, by cases safety <;> cases persistent <;> cases empty <;> decide +kernel, by cases empty <;> rfl⟩
    · obtain ⟨cell, found, stack⟩ := oldValid.injected id block registered
      exact ⟨cell, (lookup_other safety persistent empty id same (notOwner id block registered)).trans found, stack⟩

def ownership : Storage.State :=
  { owner := fun resource => if resource == .normalized then .local else .graph
    flag := fun resource => resource == .normalized
    appended := true
    capturedId := true }
def calls (safety : Bool) := callbacks LastTests.ops (fun _ _ _ effects => (none, effects)) safety 7 6
  ⟨1, 0, 1⟩ ⟨2, 0⟩ AssemblyItem.Creation.NativeFields.Tests.input Insertion.Tests.key ⟨1, [99]⟩ [old] 0
  (fun _ _ => Interner.observedHeap [] (fun _ => none))
def execute (safety persistent empty : Bool) :=
  (Storage.Cleanup.sequence [.lastValue, .pop]).execute (calls safety) ownership (before safety persistent empty)

/-- Both captured layouts and both owner lifetimes use the same universal
composition. The empty argument sentinel aliases the owner; source-input and
transferred locals differ from the selected row's actual stored payload. -/
theorem derived_contract (safety persistent empty : Bool) : ∃ after,
    execute safety persistent empty = ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run ownership), after) ∧
    Valid (memory after) ∧ Memory.Vector 7 (memory after).heap 5 [old] ∧
    readHeader (memory after).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 1, .scalar (.int false 64 3)) ∧
    (memory after).memory.nextId = 7 ∧ (memory after).memory.nextAddress = (768 + (Owner.layout safety).bytes) := by
  have rowOwned : Backing.Release.Owned 7 ⟨5, 0⟩ 3 (memory (before safety persistent empty)) :=
    ⟨rfl, ⟨[old, logical], rfl⟩, backing empty,
      by cases safety <;> cases persistent <;> cases empty <;> decide +kernel,
      by cases empty <;> rfl, by cases empty <;> rfl, by cases empty <;> rfl⟩
  have itemOwned : AssemblyItem.Owned 7 4 (memory (before safety persistent empty)) :=
    ⟨⟨AssemblyItemDeinit.Native.Tests.input.item, rfl⟩, AssemblyItemDeinit.Native.Tests.itemCell,
      (lookup_other safety persistent empty 4 (by decide) (by decide)).trans rfl, rfl, rfl, rfl⟩
  have represented := AssemblyItemDeinit.Native.Tests.initial_members.frame
    ((lookup_other safety persistent empty 4 (by decide) (by decide)).trans rfl)
  obtain ⟨_, after, _, ran, valid, vector, header, _, nextId, nextAddress, _⟩ := rollback_verified LastTests.ops
    (fun _ _ _ effects => (none, effects)) safety 7 6 5 3 4 (ownerCell safety persistent)
    ⟨1, 0, 1⟩ ⟨2, 0⟩ AssemblyItem.Creation.NativeFields.Tests.input AssemblyItemDeinit.Native.Tests.input Insertion.Tests.key
    ⟨1, [99]⟩ (arguments empty) [old] logical 0 (fun _ _ => Interner.observedHeap [] (fun _ => none)) ownership
    (before safety persistent empty) (initial_valid safety persistent empty)
    (by cases safety <;> cases persistent <;> cases empty <;> decide +kernel) rfl rfl rowOwned (by decide)
    (by cases safety <;> cases persistent <;> cases empty <;> decide +kernel)
    (by cases safety <;> cases persistent <;> cases empty <;> decide +kernel) rfl itemOwned
    (by cases safety <;> cases persistent <;> cases empty <;> decide +kernel)
    (by cases safety <;> cases persistent <;> cases empty <;> decide +kernel)
    (by cases empty; exact Or.inr rfl; exact Or.inl rfl) represented
    (by intro slice selected; cases Option.some.inj selected
        exact Or.inr ⟨rfl, AssemblyItemDeinit.Tests.cell,
          (lookup_other safety persistent empty 3 (by decide) (by decide)).trans rfl, rfl, rfl, rfl, rfl⟩)
  exact ⟨after, ran, valid, vector, header, nextId, nextAddress⟩

theorem logical_cleanup (safety persistent empty : Bool) :
    (execute safety persistent empty).1.1 = .ok () ∧ (execute safety persistent empty).1.2.invalid = false ∧
    (execute safety persistent empty).1.2.appended = false ∧
    (execute safety persistent empty).1.2.owner .normalized = .local ∧
    (execute safety persistent empty).1.2.owner .arguments = .freed := by
  obtain ⟨after, ran, _⟩ := derived_contract safety persistent empty
  rw [ran]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem allocator_effects (safety persistent empty : Bool) :
    (memory (execute safety persistent empty).2).effects.allocator = (if empty then 133 else 1334) := by
  cases safety <;> cases persistent <;> cases empty <;> decide +kernel

theorem empty_sentinel (safety persistent : Bool) :
    (memory (execute safety persistent true).2).memory.heap.lookup 0 = (memory PopTests.before).memory.heap.lookup 0 ∧
    ((memory (execute safety persistent true).2).memory.heap.lookup 6).map (fun cell => (cell.type, cell.stack, cell.base)) =
      some (Owner.viewType safety, !persistent, 768) := by
  cases safety <;> cases persistent <;> exact ⟨by decide +kernel, by decide +kernel⟩

def changed (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation) : Frame Nat :=
  withMemory PopTests.before { memory PopTests.before with memory := { (memory PopTests.before).memory with
    heap := (memory PopTests.before).memory.heap.replace id cell } }
def failed (which : Bool) :=
  (Storage.Cleanup.sequence [.lastValue, .pop]).execute (calls false) ownership
    (if which then changed 6 { LastTests.ownerCell with writable := false }
     else changed 5 { rowCell with cells := rowCell.cells.filter (fun entry => entry.1 != 48) })

theorem destructor_rejection : (failed false).1.1 = .error (.expression (.fields (.memory .uninitialized))) ∧
    (failed false).1.2.owner .value = .graph ∧ (failed false).1.2.appended = true ∧
    (memory (failed false).2).effects.allocator = 133 ∧
    readItems (memory (failed false).2).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 2) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem pop_rejection : (failed true).1.1 = .error (.pop (.memory .readOnly)) ∧
    (failed true).1.2.owner .value = .freed ∧ (failed true).1.2.appended = true ∧
    (memory (failed true).2).effects.allocator = 1334 ∧
    (memory (failed true).2).memory.heap.lookup 0 = none ∧ (failed true).2.item.clone.execution.invalidated = true ∧
    readItems (memory (failed true).2).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 2) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.RollbackTests
