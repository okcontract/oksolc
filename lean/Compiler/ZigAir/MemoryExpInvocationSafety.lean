/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpPreparationSafety
import Compiler.ZigAir.MemoryExpInvocation

/-! Complete memory safety and caller-heap preservation for the captured
exp256 model. The only admitted failure on well-typed valid inputs is modeled
allocation exhaustion. This does not discharge native source/ABI obligations. -/
namespace Compiler.ZigAir.MemoryExp
open Memory MemoryAir GeneratedMemory

def powerValue (base exponent : Word) : Value :=
  .scalar (.int false 256 ((base.toNat ^ exponent.toNat % 2^256 : Nat) : Int))

def SafeResult (base exponent : Word) (before : State) (result : Except Fault Value × State) : Prop :=
  (result.1 = .ok (powerValue base exponent) ∨ result.1 = .error .outOfMemory) ∧
    result.2.heap = before.heap ∧ result.2.valid = true

theorem Progress.cleanup_heap {before after : State} (initial : before.valid = true)
    (progress : Progress before.nextId before after) : (cleanup before.nextId after).heap = before.heap :=
  (cleanup_eq_older after before.nextId progress.stack).trans
    (progress.older.trans (valid_initial_frame before initial).2)

theorem prepared_safe_result (base exponent : Word) (state : State) (prepared : Preparation)
    (initial : state.valid = true) (safe : PreparedSafe state.nextId state prepared) :
    SafeResult base exponent state (Program.finish wordType state.nextId (preparedOutcome base exponent prepared)) := by
  cases safe with
  | oom after progress =>
    exact ⟨Or.inr rfl, progress.cleanup_heap initial, cleanup_preserves_valid _ after progress.valid⟩
  | ready baseSlot exponentSlot resultSlot after progress caps fresh =>
    obtain ⟨answer, final, evaluated, next⟩ := effects_total state.nextId after baseSlot exponentSlot resultSlot
      base exponent 1 progress.valid progress.stack caps fresh
    have finished : Program.finish wordType state.nextId
        (preparedOutcome base exponent (.ready baseSlot exponentSlot resultSlot after)) =
        (.ok (number answer), cleanup state.nextId final) := by
      simp only [preparedOutcome, evaluated, outcome, Program.finish, number_typed, ↓reduceIte]
    rw [finished]
    have power := prepared_finish_power base exponent (.ready baseSlot exponentSlot resultSlot after)
      state.nextId (number answer) (cleanup state.nextId final) finished
    exact ⟨Or.inl (congrArg Except.ok power), (progress.trans next).cleanup_heap initial,
      cleanup_preserves_valid _ final next.valid⟩

theorem specification_safe (base exponent : Word) (state : State) (initial : state.valid = true) :
    SafeResult base exponent state (specification base exponent state) :=
  prepared_safe_result base exponent state _ initial
    (prepare_safe state.nextId state base exponent initial (valid_initial_frame state initial).1 (Nat.le_refl _))

/-- Construct a complete execution: modular power or OOM, with the entire
incoming heap unchanged in both cases. No store-success premise is needed. -/
theorem exp_safe_terminates (base exponent : Word) (state : State) (initial : state.valid = true) :
    ∃ fuel result after, fn_exp256.runFuel fuel (arguments base exponent) state = .finished result after ∧
      SafeResult base exponent state (result, after) := by
  obtain ⟨fuel, done⟩ := exp_terminates base exponent state initial
  exact ⟨fuel, _, _, done, specification_safe base exponent state initial⟩

theorem exp_safe_result (base exponent : Word) (state : State) (initial : state.valid = true)
    (fuel : Nat) (result : Except Fault Value) (after : State)
    (observed : fn_exp256.runFuel fuel (arguments base exponent) state = .finished result after) :
    SafeResult base exponent state (result, after) := by
  rw [exp_result base exponent state initial fuel result after observed]
  exact specification_safe base exponent state initial

theorem exp_fault_is_oom (base exponent : Word) (state : State) (initial : state.valid = true)
    (fuel : Nat) (reason : Fault) (after : State)
    (observed : fn_exp256.runFuel fuel (arguments base exponent) state = .finished (.error reason) after) :
    reason = .outOfMemory := by
  have safe := exp_safe_result base exponent state initial fuel (.error reason) after observed
  rcases safe.1 with impossible | same
  · cases impossible
  · exact Except.error.inj same

theorem exp_preserves_caller_heap (base exponent : Word) (state : State) (initial : state.valid = true)
    (fuel : Nat) (result : Except Fault Value) (after : State)
    (observed : fn_exp256.runFuel fuel (arguments base exponent) state = .finished result after) :
    after.heap = state.heap :=
  (exp_safe_result base exponent state initial fuel result after observed).2.1

end Compiler.ZigAir.MemoryExp
