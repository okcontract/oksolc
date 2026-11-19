/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerStorage
import Compiler.Extraction.ObservedHeap

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
set_option linter.unusedSimpArgs false

/-- The existing transaction proves append on success and restoration on every
error. This projection retains the corresponding cells without running a second
copy of the insertion program. -/
def insertionCells (cells : List Storage.Cell) (cell : Storage.Cell) : Except Error NodeId → List Storage.Cell
  | .ok _ => cells ++ [cell]
  | .error _ => cells

def observedInsertTransaction (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (deterministic : Bool) (succeeds : Storage.Allocation → Bool) : Except Error NodeId × Heap :=
  let (result, after) := insertTransaction cells table cell key deterministic succeeds
  (result, { after with representatives := some (insertionCells cells cell result) })

/-- This correspondence follows from the source-bound ownership/control-flow
program, not an assumption that a reported success must have appended a node. -/
theorem insert_result_read (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (deterministic : Bool) (succeeds : Storage.Allocation → Bool) :
    (insertTransaction cells table cell key deterministic succeeds).2.read =
      Storage.readValue (insertionCells cells cell (insertTransaction cells table cell key deterministic succeeds).1) := by
  let input : Storage.Input := ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), succeeds⟩
  have safe := Storage.insert_safe_any input
  cases ran : Storage.insertProgram.run input {} with
  | mk outcome state =>
    rw [ran] at safe
    dsimp only [input] at ran
    cases outcome with
    | none => exact False.elim safe
    | some outcome =>
      cases outcome with
      | success =>
        simp only [insertTransaction, insertionOutcome, ran, insertedHeap, storageHeap, insertionCells, Storage.nodesAfter,
          safe.2.1, ↓reduceIte]
      | allocationFailure | capacityFailure =>
        simp only [insertTransaction, insertionOutcome, ran, insertedHeap, storageHeap, insertionCells, Storage.nodesAfter,
          safe.2.1, Bool.false_eq_true, ↓reduceIte]

/-- The requested key binds the clone's actual item, operands and epoch.
Denotation agreement for the cloned value remains an explicit ghost invariant;
physical clone/allocation contracts are not inferred from key equality. -/
theorem observed_insert_transaction_safe (meaning : Meaning) (cells : List Storage.Cell) (table : Table)
    (cell : Storage.Cell) (key : Key) (deterministic : Bool) (succeeds : Storage.Allocation → Bool)
    (valid : Invariant meaning (observedHeap cells table))
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning (Storage.readValue cells) = some cell.value) :
    let (result, after) := observedInsertTransaction cells table cell key deterministic succeeds
    Invariant meaning after ∧ Stable (observedHeap cells table) after ∧
      (match result with | .error _ => True | .ok id => after.read id = some cell.value) := by
  have base := insert_transaction_safe meaning cells table cell key deterministic succeeds
    ⟨valid.cache, trivial⟩ denotation
  have cellDenotes : cell.item.eval meaning (Storage.readValue cells) cell.arguments cell.sequence = some cell.value :=
    (key_sound meaning (Storage.readValue cells) cell.item cell.arguments cell.sequence key binding).symm.trans denotation
  have coherent : Storage.Coherent meaning
      (insertionCells cells cell (insertTransaction cells table cell key deterministic succeeds).1) := by
    cases result : (insertTransaction cells table cell key deterministic succeeds).1 with
    | error error => exact valid.representation.2
    | ok id => exact Storage.coherent_append meaning cells cell valid.representation.2 cellDenotes
  exact ⟨⟨base.1.cache, insert_result_read cells table cell key deterministic succeeds, coherent⟩, base.2⟩

theorem observed_insert_retains_cells (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (deterministic : Bool) (succeeds : Storage.Allocation → Bool) :
    (observedInsertTransaction cells table cell key deterministic succeeds).2.representatives =
      some (insertionCells cells cell (observedInsertTransaction cells table cell key deterministic succeeds).1) := rfl

/-- Action adapter for the recursive interner's insertion interface. A missing
representative view is an explicit model fault, not an empty native graph. -/
def observedInsert (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (succeeds : Storage.Allocation → Bool) : Action NodeId := fun before =>
  match before.representatives with
  | none => (.error .safetyFault, before)
  | some cells =>
    let (result, after) := observedInsertTransaction cells before.table cell key deterministic succeeds
    (result, { after with allocationCursor := before.allocationCursor })

theorem observed_insert_safe (meaning : Meaning) (cell : Storage.Cell) (key : Key)
    (deterministic : Bool) (succeeds : Storage.Allocation → Bool) (before : Heap)
    (valid : Invariant meaning before)
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning before.read = some cell.value) :
    Safe meaning (observedInsert cell key deterministic succeeds) before
      (fun id after => after.read id = some cell.value) := by
  cases present : before.representatives with
  | none =>
    intro outcome after ran
    simp only [observedInsert, present] at ran
    cases ran
    exact ⟨valid, fun _ _ found => found, trivial⟩
  | some cells =>
    have read := (invariant_observations meaning before valid cells present).1
    have base : Invariant meaning (observedHeap cells before.table) :=
      ⟨by simpa only [observedHeap, ← read] using valid.cache,
        rfl, (invariant_observations meaning before valid cells present).2⟩
    have checked := observed_insert_transaction_safe meaning cells before.table cell key deterministic succeeds
      base binding (by simpa only [← read] using denotation)
    intro outcome after ran
    cases transaction : observedInsertTransaction cells before.table cell key deterministic succeeds with
    | mk result stored =>
      rw [transaction] at checked
      simp only [observedInsert, present, transaction] at ran
      cases ran
      refine ⟨checked.1.with_cursor before.allocationCursor, ?_, ?_⟩
      · intro id value found
        exact checked.2.1 id value (by simpa only [observedHeap, ← read] using found)
      · cases outcome <;> exact checked.2.2

/-- Every old descriptor, including allocation identities and operand slices,
remains exactly equal on success and on rollback. -/
theorem insertion_preserves_cell (cells : List Storage.Cell) (cell : Storage.Cell) (result : Except Error NodeId)
    (index : Nat) (bound : index < cells.length) :
    (insertionCells cells cell result)[index]? = cells[index]? := by
  cases result with
  | error error => rfl
  | ok id => exact List.getElem?_append_left bound

theorem insertion_preserves_constant (cells : List Storage.Cell) (cell : Storage.Cell) (result : Except Error NodeId)
    (id : NodeId) (bound : id.toNat < cells.length) :
    Storage.constantProgram.run (insertionCells cells cell result) id = Storage.constantProgram.run cells id := by
  rw [Storage.constant_correct, Storage.constant_correct, insertion_preserves_cell cells cell result id.toNat bound]

theorem insertion_preserves_operation (cells : List Storage.Cell) (cell : Storage.Cell) (result : Except Error NodeId)
    (id : NodeId) (opcode : Opcode) (bound : id.toNat < cells.length) :
    Storage.operationProgram.run (insertionCells cells cell result) id opcode = Storage.operationProgram.run cells id opcode := by
  rw [Storage.operation_correct, Storage.operation_correct, insertion_preserves_cell cells cell result id.toNat bound]

end Compiler.Extraction.Interner
