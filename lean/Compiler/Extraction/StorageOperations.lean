/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.StorageProofs
import Compiler.Extraction.CacheProofs

namespace Compiler.Extraction.Storage
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul
set_option linter.unusedSimpArgs false

def operationResult (cell : Cell) (opcode : Opcode) : Except ReadError (Option ArgumentSlice) :=
  if cell.item.kind = 1 then
    match cell.item.instruction with
    | none => .error .invalidOptional
    | some instruction => if instruction = opcode then .ok (some cell.argumentSlice) else .ok none
  else .ok none

/-- Exact read behavior, including the short circuit that avoids unwrapping an
instruction on non-Operation items and the fault on malformed Operation items. -/
theorem operation_correct (cells : List Cell) (id : NodeId) (opcode : Opcode) :
    operationProgram.run cells id opcode =
      match cells[id.toNat]? with
      | none => .ok none
      | some cell => operationResult cell opcode := by
  unfold operationProgram OperationRead.run
  rw [representative_correct]
  cases entry : cells[id.toNat]? with
  | none => rfl
  | some cell =>
    by_cases kind : cell.item.kind = 1#32
    · cases instruction : cell.item.instruction with
      | none => simp [kind, instruction, operationResult]
      | some value =>
        by_cases equal : value = opcode <;>
          simp [kind, instruction, equal, operationResult, ArgumentsSource.run]
    · simp [kind, operationResult]

theorem operation_found (cells : List Cell) (id : NodeId) (opcode : Opcode) (slice : ArgumentSlice)
    (found : operationProgram.run cells id opcode = .ok (some slice)) :
    ∃ cell, cells[id.toNat]? = some cell ∧ cell.item.kind = 1 ∧
      cell.item.instruction = some opcode ∧ cell.argumentSlice = slice := by
  rw [operation_correct] at found
  cases entry : cells[id.toNat]? with
  | none => simp [entry] at found
  | some cell =>
    by_cases kind : cell.item.kind = 1#32
    · cases instruction : cell.item.instruction with
      | none => simp [entry, operationResult, kind, instruction] at found
      | some value =>
        by_cases equal : value = opcode
        · subst value
          simp [entry, operationResult, kind, instruction] at found
          exact ⟨cell, rfl, kind, instruction, found⟩
        · simp [entry, operationResult, kind, instruction, equal] at found
    · simp [entry, operationResult, kind] at found

/-- An operation found in the original row prefix keeps the same source slice
when later constructors append representatives. -/
theorem operation_after_append (before added : List Cell) (id : NodeId) (opcode : Opcode)
    (slice : ArgumentSlice) (query : operationProgram.run before id opcode = .ok (some slice)) :
    operationProgram.run (before ++ added) id opcode = .ok (some slice) := by
  obtain ⟨row, found, _, _, _⟩ := operation_found before id opcode slice query
  have bound : id.toNat < before.length := by
    by_cases inside : id.toNat < before.length
    · exact inside
    · rw [List.getElem?_eq_none (Nat.le_of_not_gt inside)] at found
      cases found
  rw [operation_correct, List.getElem?_append, if_pos bound]
  rw [operation_correct] at query
  exact query

/-- Each representative denotes its actual item, operands and observation
sequence. This adds the nested-operation equations absent from cache validity;
the empty graph and every semantically valid append preserve the invariant. -/
def Coherent (meaning : Meaning) (cells : List Cell) : Prop :=
  ∀ cell ∈ cells, cell.item.eval meaning (readValue cells) cell.arguments cell.sequence = some cell.value

theorem coherent_empty (meaning : Meaning) : Coherent meaning [] := by simp [Coherent]

theorem item_stable (meaning : Meaning) (before after : Read)
    (stable : Preserves (fun read => read) before after) (cell : Cell)
    (denotation : cell.item.eval meaning before cell.arguments cell.sequence = some cell.value) :
    cell.item.eval meaning after cell.arguments cell.sequence = some cell.value := by
  cases args : readArguments before cell.arguments with
  | none => simp [Item.eval, args] at denotation
  | some values =>
    have retained := readArguments_stable before after stable cell.arguments values args
    simpa only [Item.eval, retained] using (show
      (do
        let values ← some values
        if cell.item.kind = 1 then do
          let opcode ← cell.item.instruction
          meaning.operation opcode cell.sequence values
        else meaning.atom cell.item.kind cell.item.data cell.sequence values) = some cell.value by
      simpa only [Item.eval, args] using denotation)

theorem append_read_stable (before : List Cell) (cell : Cell) :
    Preserves (fun read => read) (readValue before) (readValue (before ++ [cell])) := by
  intro id value present
  have bound : id.toNat < before.length := by
    by_cases bound : id.toNat < before.length
    · exact bound
    · simp [readValue, List.getElem?_eq_none (Nat.le_of_not_gt bound)] at present
  simpa only [readValue, List.getElem?_append_left bound] using present

theorem coherent_append (meaning : Meaning) (before : List Cell) (cell : Cell)
    (coherent : Coherent meaning before)
    (denotation : cell.item.eval meaning (readValue before) cell.arguments cell.sequence = some cell.value) :
    Coherent meaning (before ++ [cell]) := by
  intro member present
  have stable := append_read_stable before cell
  rcases List.mem_append.mp present with old | new
  · exact item_stable meaning _ _ stable member (coherent member old)
  · have same : member = cell := by simpa using new
    subst member
    exact item_stable meaning _ _ stable cell denotation

theorem coherent_nodesAfter (meaning : Meaning) (before : List Cell) (cell : Cell) (state : State)
    (coherent : Coherent meaning before)
    (denotation : cell.item.eval meaning (readValue before) cell.arguments cell.sequence = some cell.value) :
    Coherent meaning (nodesAfter before cell state) := by
  unfold nodesAfter
  split
  · exact coherent_append meaning before cell coherent denotation
  · exact coherent

/-- A successful native nested lookup supplies valid operands and the exact
operation equation. Its sequence is retained, so different memory/storage
observations cannot be identified by this theorem. -/
theorem operation_fact_sound (meaning : Meaning) (cells : List Cell)
    (coherent : Coherent meaning cells) (id : NodeId) (opcode : Opcode) (slice : ArgumentSlice)
    (found : operationProgram.run cells id opcode = .ok (some slice)) :
    ∃ sequence values value, readArguments (readValue cells) slice.items = some values ∧
      readValue cells id = some value ∧ meaning.operation opcode sequence values = some value := by
  obtain ⟨cell, entry, kind, instruction, returned⟩ := operation_found cells id opcode slice found
  have equation := coherent cell (List.mem_of_getElem? entry)
  cases args : readArguments (readValue cells) cell.arguments with
  | none => simp [Item.eval, args] at equation
  | some values =>
    refine ⟨cell.sequence, values, cell.value, ?_, ?_, ?_⟩
    · simpa only [← returned, Cell.argumentSlice] using args
    · simp [readValue, entry]
    · simpa [Item.eval, args, kind, instruction] using equation

theorem operation_no_fault (meaning : Meaning) (cells : List Cell)
    (coherent : Coherent meaning cells) (id : NodeId) (opcode : Opcode) :
    ∃ result, operationProgram.run cells id opcode = .ok result := by
  rw [operation_correct]
  cases entry : cells[id.toNat]? with
  | none => exact ⟨none, rfl⟩
  | some cell =>
    by_cases kind : cell.item.kind = 1#32
    · cases instruction : cell.item.instruction with
      | none =>
        have equation := coherent cell (List.mem_of_getElem? entry)
        simp [Item.eval, kind, instruction] at equation
      | some value =>
        by_cases equal : value = opcode <;> simp [operationResult, kind, instruction, equal]
    · simp [operationResult, kind]

/-- Existing nested slices retain both their contents and backing allocation
identity when the representative array grows or insertion rolls back. This is
the container projection; physical allocation validity is a separate invariant. -/
theorem operation_stable (before : List Cell) (cell : Cell) (state : State) (id : NodeId)
    (valid : id.toNat < before.length) (opcode : Opcode) :
    operationProgram.run (nodesAfter before cell state) id opcode = operationProgram.run before id opcode := by
  rw [operation_correct, operation_correct, published_preserves before cell state id.toNat valid]

end Compiler.Extraction.Storage
