/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecutionProofs
import Compiler.Extraction.ObservedStorage

namespace Compiler.Extraction.Interner.InsertionExecution
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- The existing graph projection with its representative observation attached.
It is a semantic projection, not a second execution or a native storage model. -/
def project (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (state : Storage.State) : Heap :=
  { insertedHeap cells table cell key state with representatives := some (Storage.nodesAfter cells cell state) }

/-- Word preservation needs only the publication/append relation. A rejected
prefix may retain its new cell and partial cleanup without restoring ownership. -/
theorem project_prefix_safe (meaning : Meaning) (cells : List Storage.Cell) (table : Table)
    (cell : Storage.Cell) (key : Key) (state : Storage.State)
    (prefixed : state.published = true → state.appended = true ∧ cells.length < 2 ^ 32 - 1)
    (valid : Invariant meaning (observedHeap cells table))
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning (Storage.readValue cells) = some cell.value) :
    Invariant meaning (project cells table cell key state) ∧
      Stable (observedHeap cells table) (project cells table cell key state) := by
  have stable := inserted_stable cells table cell key state
  have cellDenotes := (key_sound meaning (Storage.readValue cells) cell.item cell.arguments cell.sequence key binding).symm.trans denotation
  have coherent := Storage.coherent_nodesAfter meaning cells cell state valid.representation.2 cellDenotes
  have cache : Valid meaning (Storage.readValue (Storage.nodesAfter cells cell state))
      (if state.published then put equalityFields table key (Storage.idFor cells) else table) := by
    have previous := valid_stable meaning _ _ table valid.cache stable
    have keyAfter := key_stable meaning _ _ stable key cell.value denotation
    split
    · rename_i published
      obtain ⟨appended, room⟩ := prefixed published
      have returns : Storage.readValue (Storage.nodesAfter cells cell state) (Storage.idFor cells) = some cell.value := by
        simp [Storage.readValue, Storage.nodesAfter, appended, Storage.idFor_toNat cells room]
      exact put_valid meaning _ table previous key (Storage.idFor cells) cell.value keyAfter returns
    · exact previous
  exact ⟨⟨cache, rfl, coherent⟩, stable⟩

theorem project_safe (meaning : Meaning) (cells : List Storage.Cell) (table : Table)
    (cell : Storage.Cell) (key : Key) (deterministic : Bool) (state : Storage.State) (outcome : Option Storage.Outcome)
    (checked : Storage.InsertionPost ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ outcome state)
    (valid : Invariant meaning (observedHeap cells table))
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning (Storage.readValue cells) = some cell.value) :
    Invariant meaning (project cells table cell key state) ∧
      Stable (observedHeap cells table) (project cells table cell key state) ∧
      match insertionOutcome cells outcome with
      | .error _ => True
      | .ok id => (project cells table cell key state).read id = some cell.value := by
  cases outcome with
  | none => exact False.elim checked.1
  | some outcome =>
    cases outcome with
    | success =>
      have room : cells.length < 2 ^ 32 - 1 := of_decide_eq_true (checked.2 rfl)
      have returns : (insertedHeap cells table cell key state).read (Storage.idFor cells) = some cell.value := by
        simp only [insertedHeap, storageHeap, Storage.readValue,
          Storage.published_returns cells cell state checked.1 room, Option.map_some]
      have kept := project_prefix_safe meaning cells table cell key state
        (fun _ => ⟨checked.1.2.1, room⟩) valid binding denotation
      exact ⟨kept.1, kept.2, returns⟩
    | allocationFailure | capacityFailure =>
      have restored : project cells table cell key state = observedHeap cells table := by
        simp [project, insertedHeap, storageHeap, observedHeap,
          Storage.failure_restores cells cell state checked.1, checked.1.2.2.1]
      rw [restored]
      exact ⟨valid, fun _ _ found => found, trivial⟩

/-- One execution of the extracted insertion body supplies ownership, capacity,
representative coherence and word preservation. Allocation and cleanup effects
are arbitrary and retained. This proves the control/semantic projection;
native memory, cloning, vector and hash-map refinement remain open. -/
theorem verified (meaning : Meaning) (cells : List Storage.Cell) (table : Table)
    (cell : Storage.Cell) (key : Key) (deterministic : Bool) (operations : Storage.Operations σ ε)
    (effects : σ) (outcome : Option Storage.Outcome)
    (valid : Invariant meaning (observedHeap cells table))
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning (Storage.readValue cells) = some cell.value)
    (completed : (Storage.insertProgram.execute
      ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ operations {} effects).1.1 = .ok outcome) :
    let execution := Storage.insertProgram.execute
      ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ operations {} effects
    Storage.SafeResult deterministic (outcome, execution.1.2) ∧
      Invariant meaning (project cells table cell key execution.1.2) ∧
      Stable (observedHeap cells table) (project cells table cell key execution.1.2) ∧
      match insertionOutcome cells outcome with
      | .error _ => True
      | .ok id => (project cells table cell key execution.1.2).read id = some cell.value := by
  have checked := Storage.insert_execution_safe
    ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ operations effects outcome completed
  exact ⟨checked.1, project_safe meaning cells table cell key deterministic _ outcome checked valid binding denotation⟩

end Compiler.Extraction.Interner.InsertionExecution
