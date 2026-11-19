/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRelocationFrame
import Compiler.Extraction.RepresentativeBackingCopyTests
import Compiler.Extraction.RepresentativePublicationTests

namespace Compiler.Extraction.RepresentativeArray.Backing.Relocation.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

def nativeCells (runtimeSafety : Bool) (cells : Cells) : Cells :=
  cells ++ if runtimeSafety then [(40, .scalar (.int false 64 0))] else []
def owner (runtimeSafety : Bool) : Allocation :=
  { Owner.FieldTests.cell runtimeSafety true true (nativeCells runtimeSafety Owner.FieldTests.completedCells) with base := 800 }
def memory (runtimeSafety : Bool) : State := { RepresentativeArray.Copy.Tests.before with
  heap := RepresentativeArray.Copy.Tests.before.heap.replace 3 (owner runtimeSafety)
  nextAddress := 800 + (Owner.layout runtimeSafety).bytes }
def before (runtimeSafety : Bool) : Session Release.Tests.Effects :=
  ⟨RegisteredCopy.Tests.registry, memory runtimeSafety, [(7, 0, 96, 8), (7, 0, 160, 8)]⟩
def first (runtimeSafety : Bool) : State := { memory runtimeSafety with
  heap := (memory runtimeSafety).heap.replace 4 {RepresentativeArray.Copy.Tests.targetCell with cells := RepresentativeArray.Copy.Tests.firstCells} }
def copied (runtimeSafety : Bool) : Session Release.Tests.Effects := {before runtimeSafety with memory :=
  {memory runtimeSafety with
    heap := (memory runtimeSafety).heap.replace 4 {RepresentativeArray.Copy.Tests.targetCell with cells := RepresentativeArray.Copy.Tests.copiedCells}} }
def released (runtimeSafety : Bool) : Session Release.Tests.Effects :=
  ⟨Compiler.Extraction.Memory.write (before runtimeSafety).heap 2 none, erase (copied runtimeSafety).memory 2,
    (before runtimeSafety).effects ++ [(7, 512, 96, 8)]⟩
def pointerCells : Cells := Owner.FieldTests.completedCells.set 16 (.pointer Publication.pointerType ⟨4, 0⟩)
def finalCells : Cells := pointerCells.set 32 (.scalar (.int false 64 5))
def afterPointer (runtimeSafety : Bool) : Session Release.Tests.Effects := {released runtimeSafety with memory :=
  {(released runtimeSafety).memory with heap := (released runtimeSafety).memory.heap.replace 3 {(owner runtimeSafety) with cells := nativeCells runtimeSafety pointerCells}} }
def after (runtimeSafety : Bool) : Session Release.Tests.Effects := {released runtimeSafety with memory :=
  {(released runtimeSafety).memory with heap := (released runtimeSafety).memory.heap.replace 3 {(owner runtimeSafety) with cells := nativeCells runtimeSafety finalCells}} }

theorem initial_valid (runtimeSafety : Bool) : Valid (before runtimeSafety) := by
  refine ⟨by cases runtimeSafety <;> decide, ?_, ?_⟩
  · intro allocator id values nonempty stored
    obtain ⟨⟨cell, found, typed, writable, persistent⟩, represented⟩ := RegisteredCopy.Tests.initial_valid.related allocator id values nonempty stored
    have apart : id ≠ 3 := by intro same; subst id; simp [before, RegisteredCopy.Tests.registry] at stored
    have frame : (before runtimeSafety).memory.heap.lookup id = RegisteredCopy.Tests.before.memory.heap.lookup id :=
      replace_other _ 3 id _ apart
    exact ⟨⟨cell, frame.trans found, typed, writable, persistent⟩, represented_frame _ values represented frame⟩
  · intro id block stored
    obtain ⟨cell, found, persistent⟩ := RegisteredCopy.Tests.initial_valid.injected id block stored
    have apart : id ≠ 3 := by intro same; subst id; simp [before, RegisteredCopy.Tests.registry] at stored
    exact ⟨cell, (replace_other _ 3 id _ apart).trans found, persistent⟩

theorem source_owned (runtimeSafety : Bool) : Release.Owned 7 ⟨2, 0⟩ 3 (before runtimeSafety) :=
  ⟨rfl, ⟨[], rfl⟩, _, rfl, rfl, rfl, rfl⟩
theorem target_owned (runtimeSafety : Bool) : Release.Owned 7 ⟨4, 0⟩ 5 (before runtimeSafety) :=
  ⟨rfl, ⟨[], rfl⟩, _, rfl, rfl, rfl, rfl⟩
theorem header_loaded (runtimeSafety : Bool) : readItems (before runtimeSafety).memory ⟨3, 16⟩ =
    .ok (.slice itemsType ⟨2, 0⟩ 2) := by cases runtimeSafety <;> rfl

theorem first_copy (runtimeSafety : Bool) : RepresentativeArray.Copy.fields expressionSlots ⟨2, 0⟩ ⟨4, 0⟩
    (before runtimeSafety).memory = (.ok (), first runtimeSafety) := by cases runtimeSafety <;> rfl
theorem second_copy (runtimeSafety : Bool) : RepresentativeArray.Copy.fields expressionSlots ⟨2, 32⟩ ⟨4, 32⟩
    (first runtimeSafety) = (.ok (), (copied runtimeSafety).memory) := by cases runtimeSafety <;> rfl
theorem actual_copy (runtimeSafety : Bool) : RegisteredCopy.run 2 4 2 (before runtimeSafety) = (.ok (), copied runtimeSafety) := by
  simp only [RegisteredCopy.run, RepresentativeArray.Copy.run, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 4 by decide,
    ↓reduceIte, RepresentativeArray.Copy.copyFrom, Nat.zero_mul, Nat.reduceAdd, Nat.reduceMul, first_copy, second_copy]
  rfl
theorem actual_release (runtimeSafety : Bool) : Release.run Release.Tests.external 7 ⟨2, 0⟩ 3 (copied runtimeSafety) =
    (.ok (), released runtimeSafety) := by cases runtimeSafety <;> rfl
theorem actual_publication (runtimeSafety : Bool) : Publication.Registered.run ⟨3, 16⟩ ⟨4, 0⟩ 5 (released runtimeSafety) =
    (.ok (), after runtimeSafety) := by
  have published : Publication.run (released runtimeSafety).memory ⟨3, 16⟩ ⟨4, 0⟩ (5 : Nat) = (.ok (), (after runtimeSafety).memory) := by
    cases runtimeSafety <;> rfl
  simp only [Publication.Registered.run, published]
  rfl
theorem actual_relocation (runtimeSafety : Bool) : run Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ ⟨4, 0⟩ 3 5 (before runtimeSafety) =
    (.ok (), after runtimeSafety) :=
  of_steps Release.Tests.external 7 _ _ _ _ 3 5 2 _ _ _ _ (header_loaded runtimeSafety) rfl rfl (actual_copy runtimeSafety)
    (actual_release runtimeSafety) (actual_publication runtimeSafety)

theorem source_ready (runtimeSafety : Bool) : ∀ index, index < 2 → ∀ slot ∈ expressionSlots,
    ∃ value, Expression.readField (before runtimeSafety).memory false ⟨2, index * 32⟩ slot.1 = .ok value := by
  intro index inside slot member
  obtain ⟨value, loaded⟩ := RepresentativeArray.Copy.Tests.initialized_source index inside slot member
  exact ⟨value, (RegisteredCopy.read_field_frame _ _ _ _ (by rfl)).trans loaded⟩

theorem without_final_premises (runtimeSafety : Bool) : ∃ oldCell finalState,
    (before runtimeSafety).memory.heap.lookup 2 = some oldCell ∧
    run Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ ⟨4, 0⟩ 3 5 (before runtimeSafety) = (.ok (), finalState) ∧
    Valid finalState ∧ Release.Owned 7 ⟨4, 0⟩ 5 finalState ∧
    finalState.heap = Compiler.Extraction.Memory.write (before runtimeSafety).heap 2 none ∧
    finalState.effects = Release.Tests.external 7 oldCell.base 96 8 (before runtimeSafety).effects ∧
    finalState.memory.nextId = (before runtimeSafety).memory.nextId ∧
    finalState.memory.nextAddress = (before runtimeSafety).memory.nextAddress ∧ finalState.memory.heap.lookup 2 = none ∧
    readHeader finalState.memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 2, .scalar (.int false 64 5)) ∧
    (∀ index, index < 2 → Expression.readFields finalState.memory false ⟨4, index * 32⟩ =
      Expression.readFields (before runtimeSafety).memory false ⟨2, index * 32⟩) ∧
    (∀ query, query ≠ 2 → query ≠ 4 → query ≠ 3 → finalState.memory.heap.lookup query = (before runtimeSafety).memory.heap.lookup query) :=
  verified runtimeSafety Release.Tests.external 7 3 2 4 3 5 2 (before runtimeSafety) (owner runtimeSafety) (initial_valid runtimeSafety)
    rfl rfl rfl (source_owned runtimeSafety) (target_owned runtimeSafety) (by decide) (by decide) (by decide)
    (header_loaded runtimeSafety) (source_ready runtimeSafety)

theorem stale_old_and_live_new (runtimeSafety : Bool) :
    (after runtimeSafety).heap 2 = none ∧ (after runtimeSafety).memory.heap.lookup 2 = none ∧
    load (after runtimeSafety).memory (.pointer (.pointer false false Expression.idType) ⟨2, 56⟩) = .error .unallocated ∧
    representativeFields (after runtimeSafety).memory ⟨3, 16⟩ 1 =
      .ok (.ok [Expression.Tests.item, Expression.Tests.arguments, FieldTests.id, FieldTests.sequence]) ∧
    representative (after runtimeSafety).memory ⟨3, 16⟩ 2 = .ok (.error .invalidId) := by cases runtimeSafety <;> decide

theorem parent_contents (runtimeSafety : Bool) : WordArray.Represents (before runtimeSafety).memory ⟨1, 1, 2⟩ [99, 1] :=
  represented_frame _ _ RepresentativeArray.Copy.Tests.parent_contents (by rfl)

theorem every_outcome_preserves_parent (runtimeSafety : Bool) (allocator oldCapacity capacity : Nat) (oldData : Address) :
    WordArray.Represents (run Release.Tests.external allocator ⟨3, 16⟩ oldData ⟨4, 0⟩ oldCapacity capacity (before runtimeSafety)).2.memory
      ⟨1, 1, 2⟩ [99, 1] :=
  (parent_borrow runtimeSafety Release.Tests.external allocator 3 oldCapacity capacity 7 5 oldData ⟨4, 0⟩ (before runtimeSafety)
    (owner runtimeSafety) RepresentativeArray.Copy.Tests.targetCell (initial_valid runtimeSafety) rfl rfl rfl rfl [] rfl
    ⟨1, 1, 2⟩ [99, 1] 4 Expression.Tests.argumentsAllocation rfl rfl (parent_contents runtimeSafety)).2

theorem wrong_brand_keeps_copy (runtimeSafety : Bool) : run Release.Tests.external 8 ⟨3, 16⟩ ⟨2, 0⟩ ⟨4, 0⟩ 3 5 (before runtimeSafety) =
    (.error (.ownership .wrongAllocator), copied runtimeSafety) := by
  simp only [run, header_loaded,
    ne_self_iff_false, ↓reduceIte, and_false, or_self, actual_copy, finish]
  cases runtimeSafety <;> rfl

theorem short_free_keeps_copy (runtimeSafety : Bool) : run Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ ⟨4, 0⟩ 2 5 (before runtimeSafety) =
    (.error (.memory .memoryValidity), copied runtimeSafety) := by
  simp only [run, header_loaded,
    ne_self_iff_false, ↓reduceIte, and_false, or_self, actual_copy, finish]
  cases runtimeSafety <;> rfl

theorem capacity_fault_keeps_release_and_pointer (runtimeSafety : Bool) :
    run Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ ⟨4, 0⟩ 3 addressLimit (before runtimeSafety) =
      (.error (.memory .malformed), afterPointer runtimeSafety) := by
  have rejected : Publication.run (released runtimeSafety).memory ⟨3, 16⟩ ⟨4, 0⟩ addressLimit =
      (.error .malformed, (afterPointer runtimeSafety).memory) := by cases runtimeSafety <;> rfl
  simp only [run, header_loaded,
    ne_self_iff_false, ↓reduceIte, and_false, or_self, actual_copy, finish, actual_release]
  simp only [Publication.Registered.run, rejected, Except.mapError]
  rfl

theorem partial_publication_observations (runtimeSafety : Bool) :
    (afterPointer runtimeSafety).heap 2 = none ∧ (afterPointer runtimeSafety).memory.heap.lookup 2 = none ∧
    (afterPointer runtimeSafety).effects = (released runtimeSafety).effects ∧
    readHeader (afterPointer runtimeSafety).memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 2, .scalar (.int false 64 3)) :=
  ⟨rfl, rfl, rfl, by cases runtimeSafety <;> rfl⟩

def missingItems (runtimeSafety : Bool) : Session Release.Tests.Effects := {before runtimeSafety with memory :=
  {(before runtimeSafety).memory with heap := (before runtimeSafety).memory.heap.replace 3 {(owner runtimeSafety) with cells := []}} }
theorem items_fault_precedes_copy (runtimeSafety : Bool) : run Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ ⟨4, 0⟩ 3 5 (missingItems runtimeSafety) =
    (.error (.memory .uninitialized), missingItems runtimeSafety) := by cases runtimeSafety <;> rfl

theorem interior_target_rejects (runtimeSafety : Bool) : run Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ ⟨4, 32⟩ 3 5 (before runtimeSafety) =
    (.error (.memory .memoryValidity), before runtimeSafety) := by simp only [run, header_loaded]; rfl

def damagedSource : Allocation :=
  {FieldTests.data with cells := Append.Tests.newCells.filter (fun entry => entry.1 != 8)}
def copyFault (runtimeSafety : Bool) : Session Release.Tests.Effects := {before runtimeSafety with memory :=
  {(before runtimeSafety).memory with heap := (before runtimeSafety).memory.heap.replace 2 damagedSource} }
def copyPrefix (runtimeSafety : Bool) : Session Release.Tests.Effects := {copyFault runtimeSafety with memory :=
  {(copyFault runtimeSafety).memory with
    heap := (copyFault runtimeSafety).memory.heap.replace 4 {RepresentativeArray.Copy.Tests.targetCell with cells := [(0, Expression.Tests.item)]}} }
theorem copy_fault_retains_prefix_without_release (runtimeSafety : Bool) :
    run Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ ⟨4, 0⟩ 3 5 (copyFault runtimeSafety) =
      (.error (.memory .uninitialized), copyPrefix runtimeSafety) := by cases runtimeSafety <;> rfl

theorem failed_copy_observations (runtimeSafety : Bool) :
    (copyPrefix runtimeSafety).heap 2 = (before runtimeSafety).heap 2 ∧
    (copyPrefix runtimeSafety).effects = (before runtimeSafety).effects ∧
    readHeader (copyPrefix runtimeSafety).memory ⟨3, 16⟩ = readHeader (before runtimeSafety).memory ⟨3, 16⟩ ∧
    Expression.readField (copyPrefix runtimeSafety).memory false ⟨4, 0⟩ Expression.itemOffset = .ok Expression.Tests.item ∧
    Expression.readField (copyPrefix runtimeSafety).memory false ⟨4, 0⟩ Expression.argumentsOffset = .error .uninitialized :=
  by cases runtimeSafety <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- An initialized empty view may carry an unallocated, non-root sentinel. -/
def emptyBefore (runtimeSafety : Bool) : Session Release.Tests.Effects :=
  { before runtimeSafety with memory := { memory runtimeSafety with
    heap := (memory runtimeSafety).heap.replace 3 { owner runtimeSafety with
      cells := nativeCells runtimeSafety ((Owner.FieldTests.completedCells.set 16
        (.pointer Publication.pointerType ⟨999, 19⟩)).set 24 (.scalar (.int false 64 0))) } } }

theorem empty_sentinel_publication (runtimeSafety : Bool) :
    run Release.Tests.external 7 ⟨3, 16⟩ ⟨999, 19⟩ ⟨4, 0⟩ 0 5 (emptyBefore runtimeSafety) =
      (let published := Publication.Registered.run ⟨3, 16⟩ ⟨4, 0⟩ 5 (emptyBefore runtimeSafety)
       (published.1.mapError (fun fault => .memory fault), published.2)) := by
  rw [empty_source Release.Tests.external 7 ⟨3, 16⟩ ⟨999, 19⟩ ⟨4, 0⟩ ⟨999, 19⟩ 0 5
    (emptyBefore runtimeSafety) (by cases runtimeSafety <;> rfl) rfl]
  rfl

theorem empty_sentinel_observations (runtimeSafety : Bool) :
    let ran := run Release.Tests.external 7 ⟨3, 16⟩ ⟨999, 19⟩ ⟨4, 0⟩ 0 5 (emptyBefore runtimeSafety)
    ran.1 = .ok () ∧ ran.2.effects = (emptyBefore runtimeSafety).effects ∧
    ran.2.heap = (emptyBefore runtimeSafety).heap ∧ ran.2.memory.heap.lookup 999 = none ∧
    readHeader ran.2.memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 0, .scalar (.int false 64 5)) := by
  rw [empty_sentinel_publication]
  cases runtimeSafety <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem nonempty_interior_source_rejects (runtimeSafety : Bool) :
    let before := emptyBefore runtimeSafety
    let changed := { before with memory := { before.memory with
      heap := before.memory.heap.replace 3 { owner runtimeSafety with
        cells := nativeCells runtimeSafety ((Owner.FieldTests.completedCells.set 16
          (.pointer Publication.pointerType ⟨999, 19⟩)).set 24 (.scalar (.int false 64 1))) } } }
    run Release.Tests.external 7 ⟨3, 16⟩ ⟨999, 19⟩ ⟨4, 0⟩ 0 5 changed =
      (.error (.memory .memoryValidity), changed) := by
  cases runtimeSafety <;> rfl

theorem empty_interior_target_rejects (runtimeSafety : Bool) :
    run Release.Tests.external 7 ⟨3, 16⟩ ⟨999, 19⟩ ⟨4, 1⟩ 0 5 (emptyBefore runtimeSafety) =
      (.error (.memory .memoryValidity), emptyBefore runtimeSafety) := by
  cases runtimeSafety <;> rfl

end Compiler.Extraction.RepresentativeArray.Backing.Relocation.Tests
