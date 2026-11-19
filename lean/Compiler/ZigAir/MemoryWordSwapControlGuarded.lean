/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapLaneGuarded

namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine
open Memory.WordArray (View Writable Represents)
open MemoryFill (size size_valid size_typed scalar_read_size cast_size_eval less_size_eval add_one_eval counter unitRef)

theorem condition_guarded (yes no : Code) (args : List Value) (env : Env) (state : State) (index : Nat)
    (view : View) (left right : Nat) (slot : Address) (frames : List (Control.Machine.Frame Ty Prim Ref))
    (h13 : env 13 = some (size index)) (h9 : env 9 = some (size 4)) (bound : index < addressLimit) :
    GuardedSteps semantics args (Footprint view left right slot)
      (.suspended ⟨(condition yes no).enableLoops, env, state, frames⟩)
      (.suspended ⟨(if index < 4 then yes else no).enableLoops, conditionEnv env index, state, frames⟩) := by
  have four : 4 < addressLimit := by decide
  have castIndex := cast_size_eval (.local 13) args env state index bound
    (scalar_read_size env 13 index bound h13)
  have castFour := cast_size_eval (.local 9) args (env.set 15 (size index)) state 4 four
    (scalar_read_size _ 9 4 four (by simpa [Control.Env.set] using h9))
  have compare := less_size_eval (.local 15) (.local 16) args
    ((env.set 15 (size index)).set 16 (size 4)) state index 4
    (scalar_read_size _ 15 index bound (by simp [Control.Env.set]))
    (scalar_read_size _ 16 4 four (by simp [Control.Env.set]))
  have typed (i : Nat) (bound : i < addressLimit) : semantics.hasType (size i) usize = true := by
    simpa only [semantics] using size_typed i bound
  have boolTyped (flag : Bool) : semantics.hasType (.scalar (.bool flag)) (.scalar .bool) = true := rfl
  have compareEval : semantics.evalPrim (.scalar (.comparison .lt (.local 15) (.local 16))) args
      ((env.set 15 (size index)).set 16 (size 4)) state =
      (.ok (.scalar (.bool (decide (index < 4)))), state) := by simpa only [semantics] using compare
  simp only [condition, Control.Code.enableLoops]
  apply GuardedSteps.bind_ok semantics args (Footprint view left right slot) (by trivial) castIndex (typed index bound)
  apply GuardedSteps.bind_ok semantics args (Footprint view left right slot) (by trivial) castFour (typed 4 four)
  apply GuardedSteps.bind_ok semantics args (Footprint view left right slot) (by trivial) compareEval (boolTyped _)
  apply GuardedSteps.control semantics args (Footprint view left right slot) _ rfl
  change GuardedSteps semantics args (Footprint view left right slot)
    (.suspended ⟨if decide (index < 4) then yes.enableLoops else no.enableLoops, conditionEnv env index, state, frames⟩) _
  split <;> simp_all only [decide_eq_true_eq, ↓reduceIte] <;> exact .refl _

theorem body_enter_guarded (args : List Value) (env : Env) (state : State) (view : View) (left right : Nat)
    (slot : Address) (index : Nat) (h7 : env 7 = some (counter slot)) (bound : index < addressLimit)
    (read : load state (counter slot) = .ok (size index)) :
    GuardedSteps semantics args (Footprint view left right slot) (.suspended (loopConfig env state))
      (.suspended ⟨head.enableLoops, env.set 13 (size index), state, .block 14 (.scalar .unit) tail :: frames⟩) := by
  have loaded : (Prim.load (.local 7)).eval args env state = (.ok (size index), state) := by
    simp only [Prim.eval_load, Ref.eval_local, h7, counter, Value.valid, ↓reduceIte, bind, Except.bind]
    exact congrArg (fun result => (result, state)) read
  have typed : semantics.hasType (size index) usize = true := by
    simpa only [semantics] using size_typed index bound
  refine GuardedSteps.bind_ok semantics args (Footprint view left right slot) (id := 13) (type := usize)
    (prim := .load (.local 7)) (env := env) (state := state) (after := state) (value := size index) ?_ loaded typed ?_
  · simp only [Footprint, Ref.eval_local, h7, counter, Value.valid, ↓reduceIte]
  · exact GuardedSteps.control semantics args (Footprint view left right slot) _ rfl (.refl _)

theorem tail_guarded (args : List Value) (env : Env) (caller : State) (base index : Nat) (view : View) (left right : Nat)
    (h7 : env 7 = some (counter ⟨caller.nextId, 0⟩)) (h13 : env 13 = some (size index))
    (initial : caller.valid = true) (live : (withCounter base index caller).valid = true)
    (bound : index + 1 < addressLimit) :
    GuardedSteps semantics args (Footprint view left right ⟨caller.nextId, 0⟩)
      (.suspended ⟨tail, env, withCounter base index caller, frames⟩)
      (.suspended (loopConfig (tailEnv env index) (withCounter base (index + 1) caller))) := by
  have addition := add_one_eval (.local 13) args env (withCounter base index caller) index bound
    (scalar_read_size env 13 index (by omega) h13)
  have counterRef : (Ref.local 7).eval (env.set 27 (size (index + 1))) = .ok (counter ⟨caller.nextId, 0⟩) := by
    simp only [Ref.eval_local, Control.Env.set, Nat.reduceEqDiff, ↓reduceIte, h7, counter, Value.valid]
  have valueRef : (Ref.local 27).eval (env.set 27 (size (index + 1))) = .ok (size (index + 1)) := by
    simp only [Ref.eval_local, Control.Env.set, ↓reduceIte, size_valid (index + 1) bound]
  have written := counter_store base index (index + 1) caller initial live bound
  have stored := Prim.eval_store_ok (.local 7) (.local 27) args (env.set 27 (size (index + 1))) _ _ _ _ counterRef valueRef written
  have typed : semantics.hasType (size (index + 1)) usize = true := by
    simpa only [semantics] using size_typed (index + 1) bound
  apply GuardedSteps.bind_ok semantics args (Footprint view left right ⟨caller.nextId, 0⟩) (id := 27) (type := usize)
    (prim := .scalar (.arithmetic .add .unchecked (.local 13) (.constant (.int false 64 1))))
    (env := env) (state := withCounter base index caller) (after := withCounter base index caller)
    (value := size (index + 1)) (by trivial) addition typed
  apply GuardedSteps.bind_ok semantics args (Footprint view left right ⟨caller.nextId, 0⟩) (id := 28) (type := .scalar .unit)
    (prim := .store (.local 7) (.local 27)) counterRef stored (by rfl)
  exact GuardedSteps.control semantics args (Footprint view left right ⟨caller.nextId, 0⟩) _ rfl (.refl _)

end Compiler.ZigAir.MemoryWordSwap
