/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.StorageEffects
import Compiler.Extraction.RepresentativeFrame

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- Executes the source-bound insertion program once. The ghost policy used in
the projection proof is not evaluated by this adapter. Primitive outcomes are
atomic; native allocator, container and deallocator refinement remains separate. -/
def insertEffectsTransaction (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (deterministic : Bool) (attempt : Storage.Allocation → Nat → Bool × Nat) (cursor : Nat) :
    Except Error NodeId × Heap :=
  let ((outcome, state), cursor) := Storage.insertProgram.runWith
    ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ attempt {} cursor
  let result := insertionOutcome cells outcome
  (result, { insertedHeap cells table cell key state with
    representatives := some (insertionCells cells cell result), allocationCursor := cursor })

theorem insert_effect_transaction_projection (cells : List Storage.Cell) (table : Table)
    (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (attempt : Storage.Allocation → Nat → Bool × Nat) (cursor : Nat) :
    insertEffectsTransaction cells table cell key deterministic attempt cursor =
      let (result, after) := observedInsertTransaction cells table cell key deterministic
        (Storage.effectPolicy deterministic attempt cursor)
      (result, { after with allocationCursor := (Storage.insertProgram.runWith
        ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ attempt {} cursor).2 }) := by
  have projected := Storage.insert_effect_projection
    ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ attempt ({} : Storage.State) cursor
  unfold insertEffectsTransaction observedInsertTransaction insertTransaction
  rw [← projected]

theorem insert_effect_transaction_safe (meaning : Meaning) (cells : List Storage.Cell) (table : Table)
    (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (attempt : Storage.Allocation → Nat → Bool × Nat) (cursor : Nat)
    (valid : Invariant meaning (observedHeap cells table))
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning (Storage.readValue cells) = some cell.value) :
    let (result, after) := insertEffectsTransaction cells table cell key deterministic attempt cursor
    Invariant meaning after ∧ Stable (observedHeap cells table) after ∧
      (match result with | .error _ => True | .ok id => after.read id = some cell.value) := by
  rw [insert_effect_transaction_projection]
  have checked := observed_insert_transaction_safe meaning cells table cell key deterministic
    (Storage.effectPolicy deterministic attempt cursor) valid binding denotation
  cases step : observedInsertTransaction cells table cell key deterministic
      (Storage.effectPolicy deterministic attempt cursor) with
  | mk result after =>
    rw [step] at checked
    exact ⟨checked.1.with_cursor _, checked.2⟩

def observedInsertWith (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (attempt : Storage.Allocation → Nat → Bool × Nat) : Action NodeId := fun before =>
  match before.representatives with
  | none => (.error .safetyFault, before)
  | some cells => insertEffectsTransaction cells before.table cell key deterministic attempt before.allocationCursor

theorem observed_insert_with_safe (meaning : Meaning) (cell : Storage.Cell) (key : Key)
    (deterministic : Bool) (attempt : Storage.Allocation → Nat → Bool × Nat) (before : Heap)
    (valid : Invariant meaning before)
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning before.read = some cell.value) :
    Safe meaning (observedInsertWith cell key deterministic attempt) before
      (fun id after => after.read id = some cell.value) := by
  cases present : before.representatives with
  | none =>
    intro result after ran
    simp only [observedInsertWith, present] at ran
    cases ran
    exact ⟨valid, fun _ _ found => found, trivial⟩
  | some cells =>
    have read := (invariant_observations meaning before valid cells present).1
    have base : Invariant meaning (observedHeap cells before.table) :=
      ⟨by simpa only [observedHeap, ← read] using valid.cache,
        rfl, (invariant_observations meaning before valid cells present).2⟩
    have checked := insert_effect_transaction_safe meaning cells before.table cell key deterministic attempt
      before.allocationCursor base binding (by simpa only [← read] using denotation)
    intro result after ran
    simp only [observedInsertWith, present] at ran
    rw [ran] at checked
    refine ⟨checked.1, ?_, ?_⟩
    · intro id value found
      exact checked.2.1 id value (by simpa only [observedHeap, ← read] using found)
    · cases result <;> exact checked.2.2

theorem insert_effect_transaction_cells (cells : List Storage.Cell) (table : Table)
    (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (attempt : Storage.Allocation → Nat → Bool × Nat) (cursor : Nat) :
    (insertEffectsTransaction cells table cell key deterministic attempt cursor).2.representatives =
      some (insertionCells cells cell (insertEffectsTransaction cells table cell key deterministic attempt cursor).1) := rfl

theorem Frames.insertWith (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (attempt : Storage.Allocation → Nat → Bool × Nat) : Frames (observedInsertWith cell key deterministic attempt) := by
  intro before cells present
  simp only [observedInsertWith, present]
  rw [insert_effect_transaction_cells]
  unfold insertionCells
  split
  · exact ⟨[cell], rfl⟩
  · exact ⟨[], by simp⟩

/-- Publication consumes the same stream as local callbacks and insertion.
A failed atomic map primitive retains its effect state and the previous table. -/
def publishWith (attempt : Nat → Bool × Nat) (key : Key) (id : NodeId) : Action Unit := fun before =>
  let (ok, cursor) := attempt before.allocationCursor
  publish ok key id { before with allocationCursor := cursor }

theorem publish_with_safe (meaning : Meaning) (attempt : Nat → Bool × Nat)
    (key : Key) (id : NodeId) (before : Heap) (value : Word)
    (valid : Invariant meaning before) (evaluated : key.eval meaning before.read = some value)
    (found : before.read id = some value) :
    Safe meaning (publishWith attempt key id) before (fun _ _ => True) := by
  cases step : attempt before.allocationCursor with
  | mk ok cursor =>
    intro result after ran
    simp only [publishWith, step] at ran
    exact publish_safe meaning ok key id { before with allocationCursor := cursor } value
      (valid.with_cursor cursor) evaluated found result after ran

theorem Frames.publishWith (attempt : Nat → Bool × Nat) (key : Key) (id : NodeId) :
    Frames (publishWith attempt key id) := by
  intro before cells present
  cases step : attempt before.allocationCursor with
  | mk ok cursor =>
    change ∃ suffix, (Interner.publishWith attempt key id before).2.representatives = some (cells ++ suffix)
    simpa only [Interner.publishWith, step] using Frames.publish ok key id
      { before with allocationCursor := cursor } cells present

end Compiler.Extraction.Interner
