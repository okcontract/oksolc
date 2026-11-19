/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecutionFaults

namespace Compiler.Extraction.Storage

theorem Release.execute_state (operations : Operations σ ε) (release : Release) (state : State)
    (effects : σ) (completed : (release.execute operations state effects).1.1 = .ok ()) :
    (release.execute operations state effects).1.2 = release.run state := by
  cases called : operations.release release state effects with
  | mk result reached =>
    cases result with
    | error fault => simp [Release.execute, called] at completed
    | ok returned => cases returned; simp only [Release.execute, called]

theorem releaseAll_state (operations : Operations σ ε) (releases : List Release) (state : State)
    (effects : σ) (completed : (releaseAll operations releases state effects).1.1 = .ok ()) :
    (releaseAll operations releases state effects).1.2 = releases.foldl (fun state release => release.run state) state := by
  induction releases generalizing state effects with
  | nil => rfl
  | cons release rest ih =>
    cases called : release.execute operations state effects with
    | mk execution reached =>
      rcases execution with ⟨result, after⟩
      cases result with
      | error fault => simp [releaseAll, called] at completed
      | ok returned =>
        cases returned
        have step := release.execute_state operations state effects (by rw [called])
        simp only [called] at step
        simp only [releaseAll, called] at completed ⊢
        rw [ih after reached completed, step]
        rfl

/-- Deferred cleanup composes at the reached ownership and effect state.
A rejected prefix stops before the suffix, retaining partial cleanup. -/
theorem releaseAll_append (operations : Operations σ ε) (first rest : List Release)
    (state : State) (effects : σ) :
    releaseAll operations (first ++ rest) state effects =
      let ((result, reached), after) := releaseAll operations first state effects
      match result with
      | .error fault => ((.error fault, reached), after)
      | .ok () => releaseAll operations rest reached after := by
  induction first generalizing state effects with
  | nil => rfl
  | cons release first ih =>
    cases called : release.execute operations state effects with
    | mk execution reached =>
      rcases execution with ⟨result, after⟩
      cases result with
      | error fault => simp only [List.cons_append, releaseAll, called]
      | ok returned =>
        cases returned
        simp only [List.cons_append, releaseAll, called]
        exact ih after reached

theorem Cleanup.execute_state (operations : Operations σ ε) (cleanup : Cleanup) (state : State)
    (effects : σ) (completed : (cleanup.execute operations state effects).1.1 = .ok ()) :
    (cleanup.execute operations state effects).1.2 = cleanup.run state := by
  cases cleanup with
  | guarded flag release =>
    by_cases active : state.flag flag = true
    · simpa only [Cleanup.execute, Cleanup.run, active, ↓reduceIte] using
        release.execute_state operations state effects (by simpa [Cleanup.execute, active] using completed)
    · simp [Cleanup.execute, Cleanup.run, active]
  | sequence releases => exact releaseAll_state operations releases state effects completed

/-- Soundness of the verification condition for all finite source programs and
all effectful callbacks. This does not assert physical refinement of callbacks. -/
theorem Program.execute_condition (program : Program) (input : Input) (operations : Operations σ ε)
    (post : Option Outcome → State → Prop) (state : State) (effects : σ)
    (checked : program.condition input post state) (outcome : Option Outcome)
    (completed : (program.execute input operations state effects).1.1 = .ok outcome) :
    post outcome (program.execute input operations state effects).1.2 := by
  have checkedAll := program.execute_conditionAll input operations post (fun _ => True) state effects
    ((program.conditionAll_ordinary input post state).mpr checked)
  simpa only [ExecutionPost, completed] using checkedAll

/-- Strong enough to connect ownership, return IDs and graph semantics without
assuming that a reported success respected the post-recursion capacity check. -/
def InsertionPost (input : Input) (outcome : Option Outcome) (state : State) : Prop :=
  SafeResult input.deterministic (outcome, state) ∧ (outcome = some .success → input.room = true)

theorem insert_condition (input : Input) : insertProgram.condition input (InsertionPost input) {} := by
  rcases input with ⟨deterministic, room, ignored⟩
  have checked : insertProgram.condition ⟨deterministic, room, fun _ => false⟩
      (InsertionPost ⟨deterministic, room, fun _ => false⟩) {} := by
    cases deterministic <;> cases room <;>
      simp [insertProgram, Program.condition, InsertionPost, Test.eval, Command.allocation, Command.success,
        State.setFlag, State.move, State.argument, Cleanup.run, Release.run, SafeResult, Published, Released] <;> decide
  exact checked

/-- Complete insertion ownership and capacity preservation for every ordinary
outcome, with no independence assumption on allocation or cleanup effects. -/
theorem insert_execution_safe (input : Input) (operations : Operations σ ε) (effects : σ)
    (outcome : Option Outcome)
    (completed : (insertProgram.execute input operations {} effects).1.1 = .ok outcome) :
    InsertionPost input outcome (insertProgram.execute input operations {} effects).1.2 :=
  insertProgram.execute_condition input operations (InsertionPost input) {} effects
    (insert_condition input) outcome completed

end Compiler.Extraction.Storage
