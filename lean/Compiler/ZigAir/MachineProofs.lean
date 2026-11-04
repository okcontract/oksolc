/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.Machine

namespace Compiler.ZigAir.Control.Machine
variable (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value)

theorem Steps.bind_ok {id : Nat} {type : Ty} {prim : Prim} {next : Code Ty Prim Ref true}
    {env : Env Value} {state after : State} {frames : List (Frame Ty Prim Ref)} {value : Value}
    {last : Execution Ty Prim Ref Value Fault State}
    (evaluated : sem.evalPrim prim args env state = (.ok value, after))
    (typed : sem.hasType value type = true)
    (tail : Steps sem args (.suspended ⟨next, env.set id value, after, frames⟩) last) :
    Steps sem args (.suspended ⟨.bind id type prim next, env, state, frames⟩) last := by
  apply Steps.step
  simpa only [Machine.step, evaluated, if_pos typed] using tail

theorem Steps.bind_fault {id : Nat} {type : Ty} {prim : Prim} {next : Code Ty Prim Ref true}
    {env : Env Value} {state after : State} {frames : List (Frame Ty Prim Ref)} {fault : Fault}
    (evaluated : sem.evalPrim prim args env state = (.error fault, after)) :
    Steps sem args (.suspended ⟨.bind id type prim next, env, state, frames⟩) (.finished (.fault fault after)) := by
  apply Steps.step
  simp only [Machine.step, evaluated]
  exact .refl _

theorem advance_finished (fuel : Nat) (outcome : Outcome Value Fault State) :
    advance sem args fuel (.finished outcome) = .finished outcome := by
  cases fuel <;> rfl

/-- Splitting a budget is exact resumption, including all environment and state. -/
theorem advance_add (first second : Nat) (execution : Execution Ty Prim Ref Value Fault State) :
    advance sem args (first + second) execution =
      advance sem args second (advance sem args first execution) := by
  induction first generalizing execution with
  | zero => simp only [Nat.zero_add, advance]
  | succ first ih =>
    cases execution with
    | finished outcome => simp [advance_finished]
    | suspended config => simpa [Nat.succ_add, advance] using ih (step sem args config)

theorem finished_stable (fuel extra : Nat) (config : Config Ty Prim Ref Value State)
    (outcome : Outcome Value Fault State) (done : run sem args fuel config = .finished outcome) :
    run sem args (fuel + extra) config = .finished outcome := by
  rw [run, advance_add, ← run, done, advance_finished]

theorem Steps.trans {first middle last : Execution Ty Prim Ref Value Fault State}
    (left : Steps sem args first middle) (right : Steps sem args middle last) :
    Steps sem args first last := by
  induction left with
  | refl => exact right
  | step config _ ih => exact .step config (ih right)

theorem advance_steps (fuel : Nat) (execution : Execution Ty Prim Ref Value Fault State) :
    Steps sem args execution (advance sem args fuel execution) := by
  induction fuel generalizing execution with
  | zero => exact .refl _
  | succ fuel ih =>
    cases execution with
    | finished outcome => exact .refl _
    | suspended config => exact .step config (ih (step sem args config))

theorem steps_iff_fuel (first last : Execution Ty Prim Ref Value Fault State) :
    Steps sem args first last ↔ ∃ fuel, advance sem args fuel first = last := by
  constructor
  · intro execution
    induction execution with
    | refl => exact ⟨0, rfl⟩
    | step config _ ih =>
      obtain ⟨fuel, h⟩ := ih
      exact ⟨fuel + 1, h⟩
  · rintro ⟨fuel, rfl⟩
    exact advance_steps sem args fuel first

/-- Finite terminating executions have one outcome, regardless of their budgets. -/
theorem finished_unique (config : Config Ty Prim Ref Value State)
    (left right : Outcome Value Fault State)
    (hleft : Steps sem args (.suspended config) (.finished left))
    (hright : Steps sem args (.suspended config) (.finished right)) : left = right := by
  obtain ⟨n, hn⟩ := (steps_iff_fuel sem args _ _).mp hleft
  obtain ⟨m, hm⟩ := (steps_iff_fuel sem args _ _).mp hright
  have hn' := finished_stable sem args n m config left hn
  have hm' := finished_stable sem args m n config right hm
  rw [Nat.add_comm m n, hn'] at hm'
  exact Execution.finished.inj hm'

theorem jump_state (target : Nat) (value : Value) (env : Env Value) (state : State)
    (frames : List (Frame Ty Prim Ref)) : (jump sem target value env state frames).state = state := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
    cases frame with
    | block id ty next =>
      by_cases catches : target = id
      · simp only [jump, if_pos catches]
        split <;> rfl
      · simpa only [jump, if_neg catches] using ih
    | loop id body =>
      by_cases catches : target = id
      · simp only [jump, if_pos catches, Execution.state, Outcome.state]
      · simpa only [jump, if_neg catches] using ih

theorem backedge_state (target : Nat) (env : Env Value) (state : State)
    (frames : List (Frame Ty Prim Ref)) : (backedge sem target env state frames).state = state := by
  induction frames with
  | nil => rfl
  | cons frame frames ih =>
    cases frame <;> simp only [backedge] <;> split
    all_goals first | rfl | exact ih

/-- Every control transition preserves any invariant preserved by primitives.
The premise includes state-changing primitive failures. -/
theorem step_preserves (invariant : State → Prop)
    (primitive : ∀ prim args env state, invariant state →
      invariant (sem.evalPrim prim args env state).2)
    (config : Config Ty Prim Ref Value State) (initial : invariant config.state) :
    invariant (step sem args config).state := by
  rcases config with ⟨code, env, state, frames⟩
  cases code with
  | bind id ty prim next =>
    cases h : sem.evalPrim prim args env state with
    | mk result after =>
      have valid : invariant after := by simpa [h] using primitive prim args env state initial
      cases result <;> simp only [step, h]
      · exact valid
      · split <;> exact valid
  | branch condition yes no =>
    cases h : sem.evalRef condition env with
    | error reason => simpa only [step, h, Execution.state, Outcome.state] using initial
    | ok value =>
      cases flag : sem.truth value <;> simpa only [step, h, flag, Execution.state, Outcome.state] using initial
  | block id ty body next => exact initial
  | loop enabled id body => exact initial
  | «repeat» enabled target => simpa only [step, backedge_state] using initial
  | jump target ref =>
    cases h : sem.evalRef ref env with
    | error reason => simpa only [step, h, Execution.state, Outcome.state] using initial
    | ok value => simpa only [step, h, jump_state] using initial
  | ret ref =>
    cases h : sem.evalRef ref env <;>
      simpa only [step, h, Execution.state, Outcome.state] using initial

theorem Steps.preserves (invariant : State → Prop)
    (primitive : ∀ prim args env state, invariant state →
      invariant (sem.evalPrim prim args env state).2)
    {first last : Execution Ty Prim Ref Value Fault State}
    (execution : Steps sem args first last) (initial : invariant first.state) : invariant last.state := by
  induction execution with
  | refl => exact initial
  | step config _ ih => exact ih (step_preserves sem args invariant primitive config initial)

theorem run_preserves (invariant : State → Prop)
    (primitive : ∀ prim args env state, invariant state →
      invariant (sem.evalPrim prim args env state).2)
    (fuel : Nat) (config : Config Ty Prim Ref Value State) (initial : invariant config.state) :
    invariant (run sem args fuel config).state :=
  Steps.preserves sem args invariant primitive (advance_steps sem args fuel (.suspended config)) initial

end Compiler.ZigAir.Control.Machine
