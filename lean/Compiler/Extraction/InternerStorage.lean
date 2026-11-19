/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.InternerProofs

namespace Compiler.Extraction.Interner
open Compiler.Algebraic Contract.Yul Compiler.Extraction.Cache

/-- Value/cache projection for the insertion transaction. The cloned cell has
the requested denotation; old cells retain their values. Attaching representative
observations additionally requires coherent cells and a state refinement; this
wrapper does not supply it. Allocation outcomes remain independent. -/
def storageHeap (cells : List Storage.Cell) (table : Table) : Heap := ⟨Storage.readValue cells, table, none, 0⟩

def insertedHeap (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (state : Storage.State) : Heap :=
  storageHeap (Storage.nodesAfter cells cell state)
    (if state.published then put equalityFields table key (Storage.idFor cells) else table)

def insertionOutcome (cells : List Storage.Cell) : Option Storage.Outcome → Except Error NodeId
  | some .success => .ok (Storage.idFor cells)
  | some .capacityFailure => .error .capacity
  | some .allocationFailure => .error .outOfMemory
  | none => .error .unsupported

def insertTransaction (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (deterministic : Bool) (succeeds : Storage.Allocation → Bool) : Except Error NodeId × Heap :=
  let (outcome, state) := Storage.insertProgram.run
    ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), succeeds⟩ {}
  (insertionOutcome cells outcome, insertedHeap cells table cell key state)

private theorem noRoom (deterministic : Bool) (succeeds : Storage.Allocation → Bool) :
    (Storage.insertProgram.run ⟨deterministic, false, succeeds⟩ {}).1 = some .capacityFailure := by
  cases deterministic <;> rfl

theorem inserted_stable (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (state : Storage.State) : Stable (storageHeap cells table) (insertedHeap cells table cell key state) := by
  intro id value present
  change Storage.readValue (Storage.nodesAfter cells cell state) id = some value
  change Storage.readValue cells id = some value at present
  have bound : id.toNat < cells.length := by
    by_cases h : id.toNat < cells.length
    · exact h
    · simp [Storage.readValue, List.getElem?_eq_none (Nat.le_of_not_gt h)] at present
  simpa only [Storage.readValue, Storage.published_preserves cells cell state id.toNat bound] using present

/-- The actual insertion body's ownership proof supplies the interner's semantic
insertion contract, including capacity and allocation failures. The clone,
append/pop, map and immutable-borrow contracts remain explicit primitive premises. -/
theorem insert_transaction_safe (meaning : Meaning) (cells : List Storage.Cell) (table : Table)
    (cell : Storage.Cell) (key : Key) (deterministic : Bool) (succeeds : Storage.Allocation → Bool)
    (valid : Invariant meaning (storageHeap cells table))
    (denotation : key.eval meaning (Storage.readValue cells) = some cell.value) :
    let (result, after) := insertTransaction cells table cell key deterministic succeeds
    Invariant meaning after ∧ Stable (storageHeap cells table) after ∧
      (match result with | .error _ => True | .ok id => after.read id = some cell.value) := by
  let input : Storage.Input := ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), succeeds⟩
  have safe := Storage.insert_safe_any input
  cases run : Storage.insertProgram.run input {} with
  | mk outcome state =>
    rw [run] at safe
    dsimp only [input] at run
    have stable := inserted_stable cells table cell key state
    cases outcome with
    | none => exact False.elim safe
    | some outcome =>
      cases outcome with
      | success =>
        have room : cells.length < 2 ^ 32 - 1 := by
          by_cases h : cells.length < 2 ^ 32 - 1
          · exact h
          · have impossible := noRoom deterministic succeeds
            have actual : (Storage.insertProgram.run ⟨deterministic, false, succeeds⟩ {}).1 = some .success := by
              simpa [input, h] using congrArg Prod.fst run
            rw [impossible] at actual
            contradiction
        have returns : (insertedHeap cells table cell key state).read (Storage.idFor cells) = some cell.value := by
          simp only [insertedHeap, storageHeap, Storage.readValue, Storage.published_returns cells cell state safe room,
            Option.map_some]
        have validAfter : Invariant meaning (insertedHeap cells table cell key state) := by
          have previous := valid_stable meaning _ _ table valid.cache stable
          have keyAfter := key_stable meaning _ _ stable key cell.value denotation
          apply Invariant.mk (representation := by trivial)
          change Valid meaning (Storage.readValue (Storage.nodesAfter cells cell state)) _
          unfold insertedHeap at returns
          dsimp [storageHeap] at returns
          dsimp only [insertedHeap, storageHeap]
          split
          · exact put_valid meaning _ table previous key (Storage.idFor cells) cell.value keyAfter returns
          · exact previous
        simp only [insertTransaction, insertionOutcome, run]
        exact ⟨validAfter, stable, returns⟩
      | allocationFailure | capacityFailure =>
        have restored : insertedHeap cells table cell key state = storageHeap cells table := by
          simp [insertedHeap, Storage.failure_restores cells cell state safe, safe.2.2.1]
        simp only [insertTransaction, insertionOutcome, run, restored]
        exact ⟨valid, fun _ _ h => h, trivial⟩

end Compiler.Extraction.Interner
