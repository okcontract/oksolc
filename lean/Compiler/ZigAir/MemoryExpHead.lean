/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedExp
import Compiler.ZigAir.ControlProjection
import Compiler.ZigAir.MemoryExpStep

/-! Symbolic execution of the actual captured exponentiation loop head.
The three scratch reads and allocation separation are explicit premises;
stores retain their checked outcomes rather than assuming success. -/
namespace Compiler.ZigAir.MemoryExp
open Memory MemoryAir GeneratedMemory

def head : Code :=
  ((fn_exp256.body.blockBody? 12).bind Control.Code.finite?).getD (.ret unitRef)

def halveCode : Code :=
  .bind 32 wordType (.load (.local 5))
    (.bind 33 wordType (.scalar (.shiftRight (.local 32) (.constant (.int false 8 1))))
      (.bind 34 (.scalar .unit) (.store (.local 5) (.local 33)) (.jump 12 unitRef)))

def squareCode : Code :=
  .bind 27 wordType (.load (.local 2))
    (.bind 28 wordType (.load (.local 2))
      (.bind 29 wordType (.scalar (.arithmetic .mul .wrapping (.local 27) (.local 28)))
        (.bind 30 (.scalar .unit) (.store (.local 2) (.local 29)) halveCode)))

def multiplyCode : Code :=
  .bind 20 wordType (.load (.local 8))
    (.bind 21 wordType (.load (.local 2))
      (.bind 22 wordType (.scalar (.arithmetic .mul .wrapping (.local 20) (.local 21)))
        (.bind 23 (.scalar .unit) (.store (.local 8) (.local 22)) (.jump 16 unitRef))))

def parityCode : Code :=
  .bind 17 wordType (.load (.local 5))
    (.bind 18 wordType (.scalar (.bitAnd (.local 17) (.constant (.int false 256 1))))
      (.bind 19 (.scalar .bool) (.scalar (.comparison .ne (.local 18) (.constant (.int false 256 0))))
        (.branch (.local 19) multiplyCode (.jump 16 unitRef))))

def stepCode : Code := .block 16 (.scalar .unit) parityCode squareCode

def condition (yes no : Code) : Code :=
  .bind 13 wordType (.load (.local 5))
    (.bind 14 (.scalar .bool) (.scalar (.comparison .ne (.local 13) (.constant (.int false 256 0))))
      (.branch (.local 14) yes no))

theorem generated_head : fn_exp256.body.blockBody? 12 = some head.enableLoops := by rfl
theorem head_shape : head = condition stepCode (.jump 10 unitRef) := by rfl

inductive Matches (target : Nat) (baseSlot exponentSlot resultSlot : Address) :
    Effect → Control.Outcome Value Fault State → Prop
  | fault (reason : Fault) (after : State) :
      Matches target baseSlot exponentSlot resultSlot (.error reason, after) (.fault reason after)
  | next (env : Env) (after : State) (locals : Locals env baseSlot exponentSlot resultSlot) :
      Matches target baseSlot exponentSlot resultSlot (.ok (), after) (.jumped target (.scalar .unit) env after)

theorem matches_write (args : List Value) (env : Env) (state : State) (target id : Nat)
    (baseSlot exponentSlot resultSlot : Address) (written : Except Fault State)
    (locals : Locals (env.set id (.scalar .unit)) baseSlot exponentSlot resultSlot) :
    Matches target baseSlot exponentSlot resultSlot (finishWrite state written)
      (Code.afterStore (.jump target unitRef) id args env state written) := by
  cases written with
  | error reason => exact .fault reason state
  | ok after => exact .next _ after locals

attribute [local simp] Control.Env.set

theorem halve_code (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (exponent : Word)
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (read : load state (slot exponentSlot) = .ok (number exponent)) :
    Matches 12 baseSlot exponentSlot resultSlot (halve state exponentSlot exponent)
      (halveCode.eval semantics args env state) := by
  let eR := env.set 32 (number exponent)
  let eH := eR.set 33 (number (exponent >>> 1))
  have loaded := load_word args env state 5 exponentSlot exponent locals.2.1 read
  have halved := halve_eval (.local 32) args eR state exponent (scalar_word eR 32 exponent (by simp [eR]))
  unfold halveCode
  rw [Code.eval_bind_ok loaded (number_typed exponent), Code.eval_bind_ok halved (number_typed _),
    Code.eval_store (local_ref eH 5 (slot exponentSlot) (by simp [eH, eR, locals.2.1]) rfl)
      (local_ref eH 33 (number (exponent >>> 1)) (by simp [eH]) (number_valid _))]
  apply matches_write
  simpa [Locals, eH, eR] using locals

theorem square_after_store (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (exponent : Word) (written : Except Fault State)
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (read : ∀ after, written = .ok after → load after (slot exponentSlot) = .ok (number exponent)) :
    Matches 12 baseSlot exponentSlot resultSlot (afterSquare state exponentSlot exponent written)
      (Code.afterStore halveCode 30 args env state written) := by
  cases written with
  | error reason => exact .fault reason state
  | ok after =>
    apply halve_code args (env.set 30 (.scalar .unit)) after baseSlot exponentSlot resultSlot exponent
    · simpa [Locals] using locals
    · exact read after rfl

theorem square_code (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (base exponent : Word)
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (readBase : load state (slot baseSlot) = .ok (number base))
    (readExponent : load state (slot exponentSlot) = .ok (number exponent))
    (apart : exponentSlot.allocation ≠ baseSlot.allocation) :
    Matches 12 baseSlot exponentSlot resultSlot (square state baseSlot exponentSlot base exponent)
      (squareCode.eval semantics args env state) := by
  let eA := env.set 27 (number base)
  let eB := eA.set 28 (number base)
  let eM := eB.set 29 (number (base * base))
  have first := load_word args env state 2 baseSlot base locals.1 readBase
  have second := load_word args eA state 2 baseSlot base (by simp [eA, locals.1]) readBase
  have mul := multiply_eval (.local 27) (.local 28) args eB state base base
    (scalar_word eB 27 base (by simp [eB, eA])) (scalar_word eB 28 base (by simp [eB]))
  unfold squareCode
  rw [Code.eval_bind_ok first (number_typed base), Code.eval_bind_ok second (number_typed base),
    Code.eval_bind_ok mul (number_typed _),
    Code.eval_store (local_ref eM 2 (slot baseSlot) (by simp [eM, eB, eA, locals.1]) rfl)
      (local_ref eM 29 (number (base * base)) (by simp [eM]) (number_valid _))]
  apply square_after_store
  · simpa [Locals, eM, eB, eA] using locals
  · intro after stored
    exact (slot_frame state after baseSlot exponentSlot _ stored apart).trans readExponent

theorem multiply_code (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (base result : Word)
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (readBase : load state (slot baseSlot) = .ok (number base))
    (readResult : load state (slot resultSlot) = .ok (number result)) :
    Matches 16 baseSlot exponentSlot resultSlot
      (finishWrite state (store state (slot resultSlot) (number (result * base))))
      (multiplyCode.eval semantics args env state) := by
  let eR := env.set 20 (number result)
  let eB := eR.set 21 (number base)
  let eM := eB.set 22 (number (result * base))
  have first := load_word args env state 8 resultSlot result locals.2.2 readResult
  have second := load_word args eR state 2 baseSlot base (by simp [eR, locals.1]) readBase
  have mul := multiply_eval (.local 20) (.local 21) args eB state result base
    (scalar_word eB 20 result (by simp [eB, eR])) (scalar_word eB 21 base (by simp [eB]))
  unfold multiplyCode
  rw [Code.eval_bind_ok first (number_typed result), Code.eval_bind_ok second (number_typed base),
    Code.eval_bind_ok mul (number_typed _),
    Code.eval_store (local_ref eM 8 (slot resultSlot) (by simp [eM, eB, eR, locals.2.2]) rfl)
      (local_ref eM 22 (number (result * base)) (by simp [eM]) (number_valid _))]
  apply matches_write
  simpa [Locals, eM, eB, eR] using locals

theorem parity_code (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (base exponent result : Word)
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (reads : Reads state baseSlot exponentSlot resultSlot base exponent result) :
    Matches 16 baseSlot exponentSlot resultSlot (select state resultSlot base exponent result)
      (parityCode.eval semantics args env state) := by
  let eL := env.set 17 (number exponent)
  let eP := eL.set 18 (number (exponent &&& 1))
  let eC := eP.set 19 (.scalar (.bool (decide (exponent &&& 1 ≠ 0))))
  have loaded := load_word args env state 5 exponentSlot exponent locals.2.1 reads.2.1
  have parity := parity_eval (.local 17) args eL state exponent (scalar_word eL 17 exponent (by simp [eL]))
  have tested := nonzero_eval (.local 18) args eP state (exponent &&& 1)
    (scalar_word eP 18 (exponent &&& 1) (by simp [eP]))
  have typed (flag : Bool) : (Value.scalar (.bool flag)).hasType (.scalar .bool) = true := rfl
  have readFlag : (Ref.local 19).eval eC = .ok (.scalar (.bool (decide (exponent &&& 1 ≠ 0)))) := rfl
  have nextLocals : Locals eC baseSlot exponentSlot resultSlot := by
    simpa [Locals, eC, eP, eL] using locals
  unfold parityCode
  rw [Code.eval_bind_ok loaded (number_typed _), Code.eval_bind_ok parity (number_typed _),
    Code.eval_bind_ok tested (typed _), Code.eval_branch_bool readFlag]
  by_cases odd : exponent &&& 1 ≠ 0
  · simp only [select, decide_eq_true_eq, if_pos odd]
    exact multiply_code args eC state baseSlot exponentSlot resultSlot base result nextLocals reads.1 reads.2.2
  · simp only [select, decide_eq_true_eq, if_neg odd]
    exact .next eC state nextLocals

theorem Matches.fault_eq {target : Nat} {baseSlot exponentSlot resultSlot : Address}
    {reason : Fault} {after : State} {observed : Control.Outcome Value Fault State}
    (matched : Matches target baseSlot exponentSlot resultSlot (.error reason, after) observed) :
    observed = .fault reason after := by cases matched; rfl

theorem Matches.next_exists {target : Nat} {baseSlot exponentSlot resultSlot : Address}
    {after : State} {observed : Control.Outcome Value Fault State}
    (matched : Matches target baseSlot exponentSlot resultSlot (.ok (), after) observed) :
    ∃ env, observed = .jumped target (.scalar .unit) env after ∧ Locals env baseSlot exponentSlot resultSlot := by
  cases matched with | next env _ locals => exact ⟨env, rfl, locals⟩

theorem step_code (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (base exponent result : Word)
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot) :
    Matches 12 baseSlot exponentSlot resultSlot (step state baseSlot exponentSlot resultSlot base exponent result)
      (stepCode.eval semantics args env state) := by
  have matched := parity_code args env state baseSlot exponentSlot resultSlot base exponent result locals reads
  rw [step_select]
  cases chosen : select state resultSlot base exponent result with
  | mk outcome after =>
    rw [chosen] at matched
    cases outcome with
    | error reason =>
      rw [stepCode, Control.Code.eval, matched.fault_eq]
      exact .fault reason after
    | ok done =>
      cases done
      obtain ⟨nextEnv, evaluated, nextLocals⟩ := matched.next_exists
      have nextReads := select_reads state after baseSlot exponentSlot resultSlot base exponent result reads separate chosen
      rw [stepCode, Control.Code.eval, evaluated]
      change Matches 12 baseSlot exponentSlot resultSlot (square after baseSlot exponentSlot base exponent)
        (squareCode.eval semantics args (nextEnv.set 16 (.scalar .unit)) after)
      exact square_code args _ after baseSlot exponentSlot resultSlot base exponent
        (by simpa [Locals] using nextLocals) nextReads.1 nextReads.2.1 separate.1.symm

def conditionEnv (env : Env) (exponent : Word) : Env :=
  (env.set 13 (number exponent)).set 14 (.scalar (.bool (decide (exponent ≠ 0))))

theorem condition_locals (env : Env) (exponent : Word) (baseSlot exponentSlot resultSlot : Address)
    (locals : Locals env baseSlot exponentSlot resultSlot) :
    Locals (conditionEnv env exponent) baseSlot exponentSlot resultSlot := by
  simpa [Locals, conditionEnv] using locals

theorem condition_eval (yes no : Code) (args : List Value) (env : Env) (state : State)
    (exponentSlot : Address) (exponent : Word)
    (found : env 5 = some (slot exponentSlot))
    (read : load state (slot exponentSlot) = .ok (number exponent)) :
    (condition yes no).eval semantics args env state =
      (if exponent ≠ 0 then yes else no).eval semantics args (conditionEnv env exponent) state := by
  let eL := env.set 13 (number exponent)
  have loaded := load_word args env state 5 exponentSlot exponent found read
  have tested := nonzero_eval (.local 13) args eL state exponent (scalar_word eL 13 exponent (by simp [eL]))
  have typed (flag : Bool) : (Value.scalar (.bool flag)).hasType (.scalar .bool) = true := rfl
  have readFlag : (Ref.local 14).eval (conditionEnv env exponent) = .ok (.scalar (.bool (decide (exponent ≠ 0)))) := rfl
  unfold condition
  rw [Code.eval_bind_ok loaded (number_typed _), Code.eval_bind_ok tested (typed _)]
  change (Control.Code.branch (.local 14) yes no).eval semantics args (conditionEnv env exponent) state = _
  rw [Code.eval_branch_bool readFlag]
  simp only [decide_eq_true_eq]

theorem head_continue (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (base exponent result : Word)
    (locals : Locals env baseSlot exponentSlot resultSlot)
    (reads : Reads state baseSlot exponentSlot resultSlot base exponent result)
    (separate : Separate baseSlot exponentSlot resultSlot) (nonzero : exponent ≠ 0) :
    Matches 12 baseSlot exponentSlot resultSlot (step state baseSlot exponentSlot resultSlot base exponent result)
      (head.eval semantics args env state) := by
  rw [head_shape, condition_eval _ _ args env state exponentSlot exponent locals.2.1 reads.2.1, if_pos nonzero]
  exact step_code args _ state baseSlot exponentSlot resultSlot base exponent result
    (condition_locals env exponent baseSlot exponentSlot resultSlot locals) reads separate

theorem head_stop (args : List Value) (env : Env) (state : State)
    (baseSlot exponentSlot resultSlot : Address) (locals : Locals env baseSlot exponentSlot resultSlot)
    (read : load state (slot exponentSlot) = .ok (number 0)) :
    ∃ afterEnv, head.eval semantics args env state = .jumped 10 (.scalar .unit) afterEnv state ∧
      Locals afterEnv baseSlot exponentSlot resultSlot := by
  rw [head_shape, condition_eval _ _ args env state exponentSlot 0 locals.2.1 read, if_neg (by simp)]
  exact ⟨_, rfl, condition_locals env 0 baseSlot exponentSlot resultSlot locals⟩

end Compiler.ZigAir.MemoryExp
