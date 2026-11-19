/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpPrologue
import Compiler.ZigAir.MemoryExecutionProofs

/-! Complete captured exp256 invocation: checked entry, initialization,
unbounded loop execution and cleanup at the original allocation mark.
Native source validity and backend correspondence are separate obligations. -/
namespace Compiler.ZigAir.MemoryExp
open Memory MemoryAir Control.Machine GeneratedMemory

def specification (base exponent : Word) (state : State) : Except Fault Value × State :=
  Program.finish wordType state.nextId (preparedOutcome base exponent (prepare base exponent state))

theorem exp_accepts (base exponent : Word) (state : State) (initial : state.valid = true) :
    fn_exp256.accepts (arguments base exponent) state = true := by
  have parameters : fn_exp256.parameters = [wordType, wordType] := rfl
  simp only [Program.accepts, parameters, arguments, List.length_cons, List.length_nil,
    Nat.reduceAdd, List.zip_cons_cons, List.zip_nil_left, List.all_cons, List.all_nil,
    initial, number_typed]
  rfl

/-- Termination for every pair of words and valid incoming heap, including
checked allocation faults. No preallocated scratch cells or successful-run
premise is needed. Cleanup uses the incoming allocation mark. -/
theorem exp_terminates (base exponent : Word) (state : State) (initial : state.valid = true) :
    ∃ fuel, fn_exp256.runFuel fuel (arguments base exponent) state =
      .finished (specification base exponent state).1 (specification base exponent state).2 := by
  obtain ⟨fuel, done⟩ := (steps_iff_fuel semantics (arguments base exponent) _ _).mp
    (exp_body_steps base exponent state)
  refine ⟨fuel, ?_⟩
  simp only [Program.runFuel, Program.start, exp_accepts base exponent state initial, ↓reduceIte, Invocation.resume]
  change (match run semantics (arguments base exponent) fuel ⟨fn_exp256.body, fun _ => none, state, []⟩ with
    | .finished result => Invocation.finish fn_exp256.returnType state.nextId result
    | .suspended next => .suspended fn_exp256.returnType state.nextId (arguments base exponent) next) = _
  rw [show run semantics (arguments base exponent) fuel ⟨fn_exp256.body, fun _ => none, state, []⟩ =
    .finished (preparedOutcome base exponent (prepare base exponent state)) from done]
  rfl

theorem exp_result (base exponent : Word) (state : State) (initial : state.valid = true)
    (fuel : Nat) (result : Except Fault Value) (after : State)
    (observed : fn_exp256.runFuel fuel (arguments base exponent) state = .finished result after) :
    (result, after) = specification base exponent state := by
  obtain ⟨budget, expected⟩ := exp_terminates base exponent state initial
  exact Invocation.finished_unique (fn_exp256.start (arguments base exponent) state) fuel budget
    result (specification base exponent state).1 after (specification base exponent state).2 observed expected

theorem prepared_finish_power (base exponent : Word) (prepared : Preparation) (mark : Nat)
    (value : Value) (after : State)
    (success : Program.finish wordType mark (preparedOutcome base exponent prepared) = (.ok value, after)) :
    value = .scalar (.int false 256 ((base.toNat ^ exponent.toNat % 2^256 : Nat) : Int)) := by
  cases prepared with
  | fault reason state => simp [preparedOutcome, Program.finish] at success
  | ready baseSlot exponentSlot resultSlot state =>
    cases evaluated : effects baseSlot exponentSlot resultSlot base exponent 1 state with
    | mk status final =>
      cases status with
      | error reason =>
        simp only [preparedOutcome, evaluated, outcome, Program.finish] at success
        cases success
      | ok answer =>
        have same := congrArg Prod.fst success
        simp only [preparedOutcome, evaluated, outcome, Program.finish, number_typed, ↓reduceIte, Except.ok.injEq] at same
        have result := effects_result baseSlot exponentSlot resultSlot base exponent 1 answer state final evaluated
        have one : (1 : Word) * Contract.Interaction.WordPower.pow base exponent.toNat =
            Contract.Interaction.WordPower.pow base exponent.toNat := BitVec.one_mul _
        rw [one] at result
        rw [← same, result]
        simp only [number, Contract.Interaction.WordPower.toNat_pow]

/-- Every successful complete invocation returns mathematical modular power.
`exp_result` separately fixes every fault and its cleaned-up prefix state. -/
theorem exp_power (base exponent : Word) (state : State) (initial : state.valid = true)
    (fuel : Nat) (value : Value) (after : State)
    (observed : fn_exp256.runFuel fuel (arguments base exponent) state = .finished (.ok value) after) :
    value = .scalar (.int false 256 ((base.toNat ^ exponent.toNat % 2^256 : Nat) : Int)) :=
  prepared_finish_power base exponent (prepare base exponent state) state.nextId value after
    (exp_result base exponent state initial fuel (.ok value) after observed).symm

theorem specification_cleanup (base exponent : Word) (state : State) :
    (specification base exponent state).2 =
      cleanup state.nextId (preparedOutcome base exponent (prepare base exponent state)).state := by
  unfold specification
  cases preparedOutcome base exponent (prepare base exponent state) <;> rfl

theorem exp_rejected (args : List Value) (state : State) (fuel : Nat)
    (rejected : fn_exp256.accepts args state = false) :
    fn_exp256.runFuel fuel args state = .finished (.error .malformed) state := by
  simp [Program.runFuel, Program.start, rejected, Invocation.resume]

end Compiler.ZigAir.MemoryExp
