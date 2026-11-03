/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpHead
import Compiler.ZigAir.MachineRefinement

/-! Unbounded execution of the initialized production exponentiation loop.
The effects specification retains memory faults; sufficient machine fuel is
proved to exist, not assumed. Allocation and invocation cleanup are separate. -/
namespace Compiler.ZigAir.MemoryExp
open Memory MemoryAir Control.Machine

def effects (baseSlot exponentSlot resultSlot : Address) (base exponent result : Word) (state : State) :
    Except Fault Word × State :=
  if _zero : exponent = 0 then (.ok result, state) else
    match step state baseSlot exponentSlot resultSlot base exponent result with
    | (.error fault, after) => (.error fault, after)
    | (.ok (), after) => effects baseSlot exponentSlot resultSlot (base * base) (exponent >>> 1)
        (nextResult base exponent result) after
termination_by exponent.toNat
decreasing_by exact halve_decreases exponent _zero

theorem effects_result (baseSlot exponentSlot resultSlot : Address) (base exponent result value : Word)
    (state after : State)
    (success : effects baseSlot exponentSlot resultSlot base exponent result state = (.ok value, after)) :
    value = result * Contract.Interaction.WordPower.pow base exponent.toNat := by
  rw [effects] at success
  split at success
  · rename_i zero
    have same := congrArg Prod.fst success
    simp only [Except.ok.injEq] at same
    subst value
    simp [zero]
  · rename_i nonzero
    cases progressed : step state baseSlot exponentSlot resultSlot base exponent result with
    | mk status middle =>
      rw [progressed] at success
      cases status with
      | error reason => simp at success
      | ok done =>
        cases done
        exact (effects_result baseSlot exponentSlot resultSlot (base * base) (exponent >>> 1)
          (nextResult base exponent result) value middle after success).trans (power_step base exponent result nonzero)
termination_by exponent.toNat
decreasing_by apply halve_decreases; assumption

def outcome : Except Fault Word × State → Control.Outcome Value Fault State
  | (.error fault, after) => .fault fault after
  | (.ok value, after) => .returned (number value) after

def returnCode : Code := .bind 39 wordType (.load (.local 8)) (.ret (.local 39))
def body : Control.Code Ty Prim Ref true := .block 12 (.scalar .unit) head.enableLoops (.repeat rfl 11)

theorem generated_loop_body : GeneratedMemory.fn_exp256.body.blockBody? 10 = some (.loop rfl 11 body) := by rfl

def loopFrames (outer : List (Frame Ty Prim Ref)) : List (Frame Ty Prim Ref) :=
  .loop 11 body :: .block 10 (.scalar .unit) returnCode.enableLoops :: outer

def loopConfig (env : Env) (state : State) (outer : List (Frame Ty Prim Ref)) : Config Ty Prim Ref Value State :=
  ⟨body, env, state, loopFrames outer⟩

theorem body_steps (args : List Value) (env : Env) (state : State) (outer : List (Frame Ty Prim Ref)) :
    Steps semantics args (.suspended (loopConfig env state outer))
      (continueOutcome semantics (head.eval semantics args env state)
        (.block 12 (.scalar .unit) (.repeat rfl 11) :: loopFrames outer)) := by
  apply Steps.step
  exact finite_steps semantics args head env state _

theorem body_next (args : List Value) (env nextEnv : Env) (state after : State) (outer : List (Frame Ty Prim Ref))
    (evaluated : head.eval semantics args env state = .jumped 12 (.scalar .unit) nextEnv after) :
    Steps semantics args (.suspended (loopConfig env state outer))
      (.suspended (loopConfig (nextEnv.set 12 (.scalar .unit)) after outer)) := by
  have path := body_steps args env state outer
  rw [evaluated] at path
  exact path.trans semantics args (.step _ (.refl _))

theorem return_eval (args : List Value) (env : Env) (state : State) (resultSlot : Address) (result : Word)
    (found : env 8 = some (slot resultSlot)) (read : load state (slot resultSlot) = .ok (number result)) :
    returnCode.eval semantics args env state = .returned (number result) state := by
  rw [returnCode, Code.eval_bind_ok (load_word args env state 8 resultSlot result found read) (number_typed result),
    Code.eval_ret, local_ref (env.set 39 (number result)) 39 (number result) (by simp [Control.Env.set]) (number_valid result)]

theorem body_stop (args : List Value) (env nextEnv : Env) (state : State) (outer : List (Frame Ty Prim Ref))
    (resultSlot : Address) (result : Word)
    (evaluated : head.eval semantics args env state = .jumped 10 (.scalar .unit) nextEnv state)
    (found : nextEnv 8 = some (slot resultSlot)) (read : load state (slot resultSlot) = .ok (number result)) :
    Steps semantics args (.suspended (loopConfig env state outer)) (.finished (.returned (number result) state)) := by
  have path := body_steps args env state outer
  rw [evaluated] at path
  apply path.trans semantics args
  have last := finite_steps semantics args returnCode (nextEnv.set 10 (.scalar .unit)) state outer
  rw [return_eval args _ state resultSlot result (by simpa [Control.Env.set] using found) read] at last
  exact last

theorem loop_effects (base exponent result : Word) (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (outer : List (Frame Ty Prim Ref))
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot) :
    Steps semantics args (.suspended (loopConfig env state outer))
      (.finished (outcome (effects baseSlot exponentSlot resultSlot base exponent result state))) := by
  rw [effects]
  split
  · rename_i zero
    obtain ⟨nextEnv, evaluated, nextLocals⟩ := head_stop args env state baseSlot exponentSlot resultSlot locals
      (by simpa only [zero] using reads.2.1)
    exact body_stop args env nextEnv state outer resultSlot result evaluated nextLocals.2.2 reads.2.2
  · rename_i nonzero
    have matched := head_continue args env state baseSlot exponentSlot resultSlot base exponent result locals reads separate nonzero
    cases progressed : step state baseSlot exponentSlot resultSlot base exponent result with
    | mk status after =>
      rw [progressed] at matched
      cases status with
      | error reason =>
        have path := body_steps args env state outer
        rw [matched.fault_eq] at path
        exact path
      | ok done =>
        cases done
        obtain ⟨nextEnv, evaluated, nextLocals⟩ := matched.next_exists
        have nextReads := step_reads state after baseSlot exponentSlot resultSlot base exponent result reads separate progressed
        exact (body_next args env nextEnv state after outer evaluated).trans semantics args
          (loop_effects (base * base) (exponent >>> 1) (nextResult base exponent result) args _ after
            baseSlot exponentSlot resultSlot outer (by simpa [Locals, Control.Env.set] using nextLocals) nextReads separate)
termination_by exponent.toNat
decreasing_by apply halve_decreases; assumption

def entry (env : Env) (state : State) (outer : List (Frame Ty Prim Ref)) : Config Ty Prim Ref Value State :=
  ⟨(GeneratedMemory.fn_exp256.body.block? 10).getD (.ret unitRef), env, state, outer⟩

theorem entry_shape (env : Env) (state : State) (outer : List (Frame Ty Prim Ref)) :
    entry env state outer = ⟨.block 10 (.scalar .unit) (.loop rfl 11 body) returnCode.enableLoops, env, state, outer⟩ := by rfl

theorem initialized_steps (base exponent result : Word) (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (outer : List (Frame Ty Prim Ref))
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot) :
    Steps semantics args (.suspended (entry env state outer))
      (.finished (outcome (effects baseSlot exponentSlot resultSlot base exponent result state))) := by
  rw [entry_shape]
  apply Steps.step
  apply Steps.step
  exact loop_effects base exponent result args env state baseSlot exponentSlot resultSlot outer locals reads separate

theorem initialized_terminates (base exponent result : Word) (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (outer : List (Frame Ty Prim Ref))
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot) :
    ∃ fuel, run semantics args fuel (entry env state outer) =
      .finished (outcome (effects baseSlot exponentSlot resultSlot base exponent result state)) :=
  (steps_iff_fuel semantics args _ _).mp
    (initialized_steps base exponent result args env state baseSlot exponentSlot resultSlot outer locals reads separate)

theorem initialized_result (base exponent result : Word) (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (outer : List (Frame Ty Prim Ref))
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot) (observed : Control.Outcome Value Fault State)
    (path : Steps semantics args (.suspended (entry env state outer)) (.finished observed)) :
    observed = outcome (effects baseSlot exponentSlot resultSlot base exponent result state) :=
  finished_unique semantics args _ _ _ path
    (initialized_steps base exponent result args env state baseSlot exponentSlot resultSlot outer locals reads separate)

/-- Every ordinary return has the power value. Faults are retained separately
by `initialized_result`; `initialized_terminates` supplies termination. -/
theorem initialized_return (base exponent result : Word) (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (outer : List (Frame Ty Prim Ref))
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot) (value : Value) (after : State)
    (path : Steps semantics args (.suspended (entry env state outer)) (.finished (.returned value after))) :
    value = number (result * Contract.Interaction.WordPower.pow base exponent.toNat) := by
  have agrees := initialized_result base exponent result args env state baseSlot exponentSlot resultSlot outer
    locals reads separate (.returned value after) path
  cases evaluated : effects baseSlot exponentSlot resultSlot base exponent result state with
  | mk status final =>
    rw [evaluated] at agrees
    cases status with
    | error reason => cases agrees
    | ok answer =>
      have valueEq : value = number answer := by cases agrees; rfl
      exact valueEq.trans (congrArg number
        (effects_result baseSlot exponentSlot resultSlot base exponent result answer state final evaluated))

theorem initialized_power (base exponent : Word) (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (outer : List (Frame Ty Prim Ref))
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (reads : Reads state baseSlot exponentSlot resultSlot base exponent 1)
    (separate : Separate baseSlot exponentSlot resultSlot) (value : Value) (after : State)
    (path : Steps semantics args (.suspended (entry env state outer)) (.finished (.returned value after))) :
    value = .scalar (.int false 256 ((base.toNat ^ exponent.toNat % 2^256 : Nat) : Int)) := by
  have result := initialized_return base exponent 1 args env state baseSlot exponentSlot resultSlot outer
    locals reads separate value after path
  have one : (1 : Word) * Contract.Interaction.WordPower.pow base exponent.toNat =
      Contract.Interaction.WordPower.pow base exponent.toNat := BitVec.one_mul _
  rw [one] at result
  simpa only [number, Contract.Interaction.WordPower.toNat_pow] using result

end Compiler.ZigAir.MemoryExp
