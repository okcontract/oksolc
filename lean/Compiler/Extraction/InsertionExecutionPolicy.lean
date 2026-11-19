/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionExecution
import Compiler.Extraction.StorageExecutionPolicy

namespace Compiler.Extraction.Interner.InsertionExecution
open Compiler.Algebraic Compiler.Extraction.Cache

/-- Ownership safety fixes every graph field used by the logical transaction.
The actual private state need not equal the logical ownership state. -/
theorem project_transaction (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (deterministic : Bool) (succeeds : Storage.Allocation → Bool)
    (outcome : Option Storage.Outcome) (owner : Storage.State)
    (safe : Storage.SafeResult deterministic (outcome, owner))
    (observed : (Storage.insertProgram.run
      ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), succeeds⟩ {}).1 = outcome) :
    observedInsertTransaction cells table cell key deterministic succeeds =
      (insertionOutcome cells outcome, project cells table cell key owner) := by
  have logical := Storage.insert_safe_any
    (⟨deterministic, decide (cells.length < 2 ^ 32 - 1), succeeds⟩ : Storage.Input)
  cases ran : Storage.insertProgram.run ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), succeeds⟩ {} with
  | mk result closed =>
    simp only [ran] at observed logical
    subst result
    cases outcome with
    | none => exact False.elim safe
    | some outcome =>
      cases outcome with
      | success =>
        simp only [observedInsertTransaction, insertTransaction, ran, insertionOutcome, insertionCells,
          project, insertedHeap, storageHeap, Storage.nodesAfter, safe.2.1, logical.2.1,
          safe.2.2.2.1, logical.2.2.2.1, ↓reduceIte]
      | allocationFailure | capacityFailure =>
        simp only [observedInsertTransaction, insertTransaction, ran, insertionOutcome, insertionCells,
          project, insertedHeap, storageHeap, Storage.nodesAfter, safe.2.1, logical.2.1,
          safe.2.2.1, logical.2.2.1, Bool.false_eq_true, ↓reduceIte]

/-- Actual source callbacks determine both the result and complete logical graph
projection through the existing transaction adapter. Rejection cannot satisfy
ordinary completion; neither native memory refinement nor a cursor advance is
inferred from this logical correspondence. -/
theorem observed (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (deterministic : Bool) (calls : Storage.Operations σ ε) (before : σ)
    (outcome : Option Storage.Outcome)
    (completed : (Storage.insertProgram.execute
      ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ calls {} before).1.1 = .ok outcome) :
    observedInsertTransaction cells table cell key deterministic (Storage.executionPolicy calls deterministic before) =
      (insertionOutcome cells outcome, project cells table cell key
        (Storage.insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ calls {} before).1.2) :=
  project_transaction cells table cell key deterministic _ outcome _
    (Storage.insert_execution_safe _ calls before outcome completed).1
    (Storage.insert_execution_policy _ calls before outcome completed)

/-- A candidate descriptor is observed only on success. Failed insertion uses
the unchanged rows and table regardless of hypothetical clone locals. -/
theorem project_candidate (cells : List Storage.Cell) (table : Table) (actual candidate : Storage.Cell)
    (key : Key) (deterministic : Bool) (outcome : Option Storage.Outcome) (owner : Storage.State)
    (safe : Storage.SafeResult deterministic (outcome, owner))
    (binding : outcome = some .success → actual = candidate) :
    project cells table actual key owner = project cells table candidate key owner := by
  cases outcome with
  | none => exact False.elim safe
  | some outcome =>
    cases outcome with
    | success => rw [binding rfl]
    | allocationFailure | capacityFailure =>
      simp only [project, insertedHeap, storageHeap, Storage.nodesAfter,
        safe.2.1, Bool.false_eq_true, ↓reduceIte]

end Compiler.Extraction.Interner.InsertionExecution
