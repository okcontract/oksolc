/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecution

namespace Compiler.Extraction.Storage

/-- A rejected callback retains its reached ownership state. The error value
is arbitrary; it cannot supply a successful outcome or run omitted cleanup. -/
def ExecutionPost (post : α → State → Prop) (failed : State → Prop)
    (execution : Execution σ ε α) : Prop :=
  match execution.1.1 with
  | .ok value => post value execution.1.2
  | .error _ => failed execution.1.2

def releaseCondition (releases : List Release) (post failed : State → Prop) : State → Prop :=
  match releases with
  | [] => post
  | release :: rest => fun state => failed state ∧ releaseCondition rest post failed (release.run state)

def Cleanup.conditionAll (cleanup : Cleanup) (post failed : State → Prop) (state : State) : Prop :=
  match cleanup with
  | .guarded flag release => if state.flag flag then failed state ∧ post (release.run state) else post state
  | .sequence releases => releaseCondition releases post failed state

/-- The ordinary verification condition extended to each possible callback
fault, including partial deferred cleanup. Private callback effects stay arbitrary. -/
def Program.conditionAll (input : Input) : Program → (Option Outcome → State → Prop) → (State → Prop) → State → Prop
  | .done, post, _, state => post none state
  | .ret, post, _, state => post (some .success) { state with invalid := state.invalid || !state.capturedId }
  | .capacityError, post, _, state => post (some .capacityFailure) state
  | .command action next, post, failed, state =>
    next.conditionAll input post failed (action.success input state) ∧
      (action.allocation ≠ none → failed state ∧ post (some .allocationFailure) state)
  | .branch test yes no next, post, failed, state =>
    let continuation := fun outcome after => match outcome with
      | none => next.conditionAll input post failed after
      | some result => post (some result) after
    if test.eval input then yes.conditionAll input continuation failed state else no.conditionAll input continuation failed state
  | .scope errorOnly cleanup body, post, failed, state =>
    body.conditionAll input (fun outcome after =>
      if errorOnly && (outcome == some .success || outcome == none) then post outcome after
      else cleanup.conditionAll (post outcome) failed after) failed state

theorem releaseAll_condition (operations : Operations σ ε) (releases : List Release)
    (post failed : State → Prop) (state : State) (effects : σ)
    (checked : releaseCondition releases post failed state) :
    ExecutionPost (fun _ => post) failed (releaseAll operations releases state effects) := by
  induction releases generalizing state effects with
  | nil => exact checked
  | cons release rest ih =>
    rcases checked with ⟨fault, following⟩
    cases called : operations.release release state effects with
    | mk result reached =>
      cases result with
      | error error => simpa only [releaseAll, Release.execute, called, ExecutionPost] using fault
      | ok value =>
        cases value
        simpa only [releaseAll, Release.execute, called] using ih (release.run state) reached following

theorem Cleanup.execute_conditionAll (cleanup : Cleanup) (operations : Operations σ ε)
    (post failed : State → Prop) (state : State) (effects : σ)
    (checked : cleanup.conditionAll post failed state) :
    ExecutionPost (fun _ => post) failed (cleanup.execute operations state effects) := by
  cases cleanup with
  | sequence releases => exact releaseAll_condition operations releases post failed state effects checked
  | guarded flag release =>
    by_cases active : state.flag flag = true
    · simp only [Cleanup.conditionAll, active, ↓reduceIte] at checked
      cases called : operations.release release state effects with
      | mk result reached =>
        cases result with
        | error error => simpa only [Cleanup.execute, active, ↓reduceIte, Release.execute, called, ExecutionPost] using checked.1
        | ok value =>
          cases value
          simpa only [Cleanup.execute, active, ↓reduceIte, Release.execute, called, ExecutionPost] using checked.2
    · simpa only [Cleanup.conditionAll, Cleanup.execute, active, Bool.false_eq_true, ↓reduceIte, ExecutionPost] using checked

theorem Program.execute_conditionAll (program : Program) (input : Input) (operations : Operations σ ε)
    (post : Option Outcome → State → Prop) (failed : State → Prop) (state : State) (effects : σ)
    (checked : program.conditionAll input post failed state) :
    ExecutionPost post failed (program.execute input operations state effects) := by
  induction program generalizing post state effects with
  | done | ret | capacityError => exact checked
  | command command next ih =>
    rcases checked with ⟨success, failure⟩
    cases site : command.allocation with
    | none => simpa only [Program.execute, site] using ih post _ effects success
    | some siteValue =>
      have rejected := failure (by simp only [site, ne_eq, reduceCtorEq, not_false_eq_true])
      cases called : operations.attempt siteValue state effects with
      | mk result reached =>
        cases result with
        | error error => simpa only [Program.execute, site, called, ExecutionPost] using rejected.1
        | ok accepted =>
          cases accepted with
          | false => simpa only [Program.execute, site, called, ExecutionPost] using rejected.2
          | true => simpa only [Program.execute, site, called] using ih post _ reached success
  | branch test yes no next ihYes ihNo ihNext =>
    let continuation : Option Outcome → State → Prop := fun result after => match result with
      | none => next.conditionAll input post failed after
      | some value => post (some value) after
    have branch : ExecutionPost continuation failed ((if test.eval input then yes else no).execute input operations state effects) := by
      cases active : test.eval input with
      | false =>
        simp only [Program.conditionAll, active, Bool.false_eq_true, ↓reduceIte] at checked
        simpa only [active, Bool.false_eq_true, ↓reduceIte] using ihNo continuation state effects checked
      | true =>
        simp only [Program.conditionAll, active, ↓reduceIte] at checked
        simpa only [active, ↓reduceIte] using ihYes continuation state effects checked
    have selected : (if test.eval input then yes.execute input operations state effects else no.execute input operations state effects) =
        (if test.eval input then yes else no).execute input operations state effects := by split <;> rfl
    cases called : (if test.eval input then yes else no).execute input operations state effects with
    | mk execution reached =>
      rcases execution with ⟨result, after⟩
      cases result with
      | error error => simpa only [Program.execute, selected, called, ExecutionPost] using branch
      | ok result =>
        simp only [called, ExecutionPost] at branch
        cases result with
        | none => simpa only [Program.execute, selected, called] using ihNext post after reached branch
        | some value => simpa only [Program.execute, selected, called, ExecutionPost] using branch
  | scope errorOnly cleanup body ih =>
    have known := ih _ state effects checked
    cases called : body.execute input operations state effects with
    | mk execution reached =>
      rcases execution with ⟨result, after⟩
      cases result with
      | error error => simpa only [Program.execute, called, ExecutionPost] using known
      | ok result =>
        simp only [called, ExecutionPost] at known
        by_cases skipped : (errorOnly && (result == some .success || result == none)) = true
        · simpa only [Program.execute, called, skipped, ↓reduceIte, ExecutionPost] using known
        · simp only [skipped, Bool.false_eq_true, ↓reduceIte] at known
          have closed := cleanup.execute_conditionAll operations (post result) failed after reached known
          cases ran : cleanup.execute operations after reached with
          | mk execution finalEffects =>
            rcases execution with ⟨result, final⟩
            cases result <;> simpa only [Program.execute, called, skipped, Bool.false_eq_true, ↓reduceIte, ran,
              ExecutionPost, Except.map] using closed

theorem releaseCondition_ordinary (releases : List Release) (post : State → Prop) (state : State) :
    releaseCondition releases post (fun _ => True) state ↔ post (releases.foldl (fun state release => release.run state) state) := by
  induction releases generalizing state with
  | nil => rfl
  | cons release rest ih => simp only [releaseCondition, List.foldl_cons, true_and, ih]

theorem Cleanup.conditionAll_ordinary (cleanup : Cleanup) (post : State → Prop) (state : State) :
    cleanup.conditionAll post (fun _ => True) state ↔ post (cleanup.run state) := by
  cases cleanup with
  | sequence releases => exact releaseCondition_ordinary releases post state
  | guarded flag release => cases active : state.flag flag <;> simp [Cleanup.conditionAll, Cleanup.run, active]

/-- Existing ordinary clients retain their original verification condition;
the generalized executor proof supplies them by ignoring rejected outcomes. -/
theorem Program.conditionAll_ordinary (program : Program) (input : Input)
    (post : Option Outcome → State → Prop) (state : State) :
    program.conditionAll input post (fun _ => True) state ↔ program.condition input post state := by
  induction program generalizing post state with
  | done | ret | capacityError => rfl
  | command command next ih => simp only [Program.conditionAll, Program.condition, ih, true_and]
  | branch test yes no next ihYes ihNo ihNext =>
    simp only [Program.conditionAll, Program.condition, ihNext, ihYes, ihNo]
    rfl
  | scope errorOnly cleanup body ih =>
    simp only [Program.conditionAll, Program.condition, Cleanup.conditionAll_ordinary, ih, apply_ite]

/-- Cache publication can only name a retained, capacity-checked append.
This is a word-projection invariant, not a claim that rejected cleanup finished. -/
def PublishedPrefix (input : Input) (state : State) : Prop :=
  state.published = true → state.appended = true ∧ input.room = true

private theorem move_flag (state : State) (resource selected : Resource) (before after : Owner) :
    (state.move resource before after).flag selected = state.flag selected := by
  unfold State.move
  split <;> rfl

private theorem move_appended (state : State) (resource : Resource) (before after : Owner) :
    (state.move resource before after).appended = state.appended := by
  unfold State.move
  split <;> rfl

private theorem move_published (state : State) (resource : Resource) (before after : Owner) :
    (state.move resource before after).published = state.published := by
  unfold State.move
  split <;> rfl

theorem insert_condition_prefix (input : Input) :
    insertProgram.conditionAll input (fun _ => PublishedPrefix input) (PublishedPrefix input) {} := by
  rcases input with ⟨deterministic, room, ignored⟩
  have checked : insertProgram.conditionAll ⟨deterministic, room, fun _ => false⟩
      (fun _ => PublishedPrefix ⟨deterministic, room, fun _ => false⟩)
      (PublishedPrefix ⟨deterministic, room, fun _ => false⟩) {} := by
    cases deterministic <;> cases room <;>
      simp [insertProgram, Program.conditionAll, Cleanup.conditionAll, releaseCondition,
        PublishedPrefix, Test.eval, Command.allocation, Command.success, State.setFlag, Release.run,
        move_flag, move_appended, move_published, apply_ite] <;> decide
  exact checked

/-- Ordinary outcomes and stopped callback prefixes preserve the same graph
publication invariant. No successful execution or completed cleanup is assumed. -/
theorem insert_execution_prefix (input : Input) (operations : Operations σ ε) (effects : σ) :
    PublishedPrefix input (insertProgram.execute input operations {} effects).1.2 := by
  have checked := insertProgram.execute_conditionAll input operations (fun _ => PublishedPrefix input)
    (PublishedPrefix input) {} effects (insert_condition_prefix input)
  cases ran : (insertProgram.execute input operations {} effects).1.1 <;>
    simpa only [ExecutionPost, ran] using checked

end Compiler.Extraction.Storage
