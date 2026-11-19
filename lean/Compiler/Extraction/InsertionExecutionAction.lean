/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionExecution
import Compiler.Extraction.InternerScope

namespace Compiler.Extraction.Interner.InsertionExecution
open Compiler.Algebraic Compiler.Extraction.Cache

/-- Project the full source executor, including effectful cleanup, into the
interner action interface. Semantic faults retain the reached projection and
are classified as safety faults, never ordinary allocation failure. -/
def transaction (cells : List Storage.Cell) (table : Table) (cell : Storage.Cell) (key : Key)
    (deterministic : Bool) (operations : Storage.Operations Nat ε) (cursor : Nat) : Except Error NodeId × Heap :=
  let ((result, owner), reached) := Storage.insertProgram.execute
    ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ operations {} cursor
  let outcome := match result with
    | .error _ => .error .safetyFault
    | .ok outcome => insertionOutcome cells outcome
  (outcome, { project cells table cell key owner with allocationCursor := reached })

/-- Unlike the allocation-only `observedInsertWith`, this adapter consumes
release callbacks too. Both adapters reuse the same source program; this one
is needed when insertion replays an actual callback transcript. -/
def action (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (operations : Storage.Operations Nat ε) : Action NodeId := fun before =>
  match before.representatives with
  | none => (.error .safetyFault, before)
  | some cells => transaction cells before.table cell key deterministic operations before.allocationCursor

/-- The established ownership/word theorem supplies preservation for an
ordinary source outcome. A stopped semantic fault does not satisfy this premise
and does not acquire a preservation certificate through this adapter. -/
theorem transaction_verified (meaning : Meaning) (cells : List Storage.Cell) (table : Table)
    (cell : Storage.Cell) (key : Key) (deterministic : Bool) (operations : Storage.Operations Nat ε)
    (cursor : Nat) (outcome : Option Storage.Outcome)
    (valid : Invariant meaning (observedHeap cells table))
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning (Storage.readValue cells) = some cell.value)
    (completed : (Storage.insertProgram.execute
      ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ operations {} cursor).1.1 = .ok outcome) :
    let ran := transaction cells table cell key deterministic operations cursor
    ran.1 = insertionOutcome cells outcome ∧
      Invariant meaning ran.2 ∧ Stable (observedHeap cells table) ran.2 ∧
      match ran.1 with | .error _ => True | .ok id => ran.2.read id = some cell.value := by
  have checked := verified meaning cells table cell key deterministic operations cursor outcome valid binding denotation completed
  dsimp only [transaction]
  rw [completed]
  exact ⟨rfl, checked.2.1.with_cursor _, checked.2.2⟩

/-- The exact reached graph is safe even when an allocation or cleanup callback
rejects. This does not classify that rejection as ordinary OOM or complete cleanup. -/
theorem transaction_safe (meaning : Meaning) (cells : List Storage.Cell) (table : Table)
    (cell : Storage.Cell) (key : Key) (deterministic : Bool) (operations : Storage.Operations Nat ε)
    (cursor : Nat) (valid : Invariant meaning (observedHeap cells table))
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning (Storage.readValue cells) = some cell.value) :
    let ran := transaction cells table cell key deterministic operations cursor
    Invariant meaning ran.2 ∧ Stable (observedHeap cells table) ran.2 ∧
      match ran.1 with | .error _ => True | .ok id => ran.2.read id = some cell.value := by
  have prefixed := Storage.insert_execution_prefix
    ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ operations cursor
  have kept := project_prefix_safe meaning cells table cell key _
    (fun published => ⟨(prefixed published).1, of_decide_eq_true (prefixed published).2⟩) valid binding denotation
  cases executed : Storage.insertProgram.execute
      ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ operations {} cursor with
  | mk execution reached =>
    rcases execution with ⟨result, owner⟩
    cases result with
    | error fault =>
      simp only [executed] at kept
      simp only [transaction, executed]
      exact ⟨kept.1.with_cursor reached, kept.2, trivial⟩
    | ok outcome =>
      exact (transaction_verified meaning cells table cell key deterministic operations cursor outcome
        valid binding denotation (by rw [executed])).2

theorem action_safe (meaning : Meaning) (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (operations : Storage.Operations Nat ε) (before : Heap)
    (valid : Invariant meaning before)
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning before.read = some cell.value) :
    Safe meaning (action cell key deterministic operations) before (fun id after => after.read id = some cell.value) := by
  intro result after ran
  cases rows : before.representatives with
  | none =>
    simp only [action, rows, Prod.mk.injEq] at ran
    obtain ⟨rfl, rfl⟩ := ran
    exact ⟨valid, fun _ _ found => found, trivial⟩
  | some cells =>
    have reads := (invariant_observations meaning before valid cells rows).1
    have initial : Invariant meaning (observedHeap cells before.table) :=
      ⟨by simpa only [observedHeap, ← reads] using valid.cache,
        rfl, (invariant_observations meaning before valid cells rows).2⟩
    have checked := transaction_safe meaning cells before.table cell key deterministic operations before.allocationCursor
      initial binding (by simpa only [← reads] using denotation)
    simp only [action, rows] at ran
    rw [ran] at checked
    refine ⟨checked.1, fun id value found => checked.2.1 id value (by simpa only [observedHeap, ← reads] using found), ?_⟩
    cases result <;> exact checked.2.2

theorem action_verified (meaning : Meaning) (cell : Storage.Cell) (key : Key) (deterministic : Bool)
    (operations : Storage.Operations Nat ε) (before : Heap) (cells : List Storage.Cell) (outcome : Option Storage.Outcome)
    (rows : before.representatives = some cells) (valid : Invariant meaning before)
    (binding : keyCode.run cell.item cell.arguments cell.sequence = some key)
    (denotation : key.eval meaning before.read = some cell.value)
    (completed : (Storage.insertProgram.execute
      ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ operations {} before.allocationCursor).1.1 = .ok outcome) :
    let ran := action cell key deterministic operations before
    ran.1 = insertionOutcome cells outcome ∧
      Invariant meaning ran.2 ∧ Stable before ran.2 ∧
      match ran.1 with | .error _ => True | .ok id => ran.2.read id = some cell.value := by
  have checked := action_safe meaning cell key deterministic operations before valid binding denotation
    (action cell key deterministic operations before).1 (action cell key deterministic operations before).2 rfl
  refine ⟨by simp only [action, rows, transaction, completed], checked.1, checked.2.1, ?_⟩
  cases result : (action cell key deterministic operations before).1 with
  | error error => trivial
  | ok id => simpa only [result] using checked.2.2

end Compiler.Extraction.Interner.InsertionExecution
