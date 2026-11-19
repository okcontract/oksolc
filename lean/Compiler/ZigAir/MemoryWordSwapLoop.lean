/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapCounter

/-! Termination and caller-memory refinement of the captured counter loop.
The counter lives in a separate invocation-local prefix, and its checked
increments are bounded by the four-byte word extent. -/
namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine
open Memory.WordArray (View Writable Represents Frame)
open MemoryFill (size size_valid size_typed scalar_read_size add_one_eval counter unitRef)

def tail : Control.Code Ty Prim Ref true :=
  .bind 27 usize (.scalar (.arithmetic .add .unchecked (.local 13) (.constant (.int false 64 1))))
    (.bind 28 (.scalar .unit) (.store (.local 7) (.local 27)) (.repeat rfl 12))

def body : Control.Code Ty Prim Ref true :=
  .bind 13 usize (.load (.local 7)) (.block 14 (.scalar .unit) head.enableLoops tail)

def frames : List (Frame Ty Prim Ref) := [.loop 12 body, .block 11 (.scalar .unit) (.ret unitRef)]
def loopConfig (env : Env) (state : State) : Config Ty Prim Ref Value State := ⟨body, env, state, frames⟩

def entry : Control.Code Ty Prim Ref true := .block 11 (.scalar .unit) (.loop rfl 12 body) (.ret unitRef)

theorem generated_loop : GeneratedMemory.fn_swap_u32.program.body.block? 11 = some entry := rfl

theorem body_enter (args : List Value) (env : Env) (state : State) (slot : Address) (index : Nat)
    (h7 : env 7 = some (counter slot)) (bound : index < addressLimit)
    (read : load state (counter slot) = .ok (size index)) :
    Steps semantics args (.suspended (loopConfig env state))
      (.suspended ⟨head.enableLoops, env.set 13 (size index), state, .block 14 (.scalar .unit) tail :: frames⟩) := by
  have loaded : (Prim.load (.local 7)).eval args env state = (.ok (size index), state) := by
    simp only [Prim.eval_load, Ref.eval_local, h7, counter, Value.valid, ↓reduceIte, bind, Except.bind]
    exact congrArg (fun result => (result, state)) read
  have typed : semantics.hasType (size index) usize = true := by
    simpa only [semantics] using size_typed index bound
  apply Steps.bind_ok semantics args (id := 13) (type := usize) (prim := .load (.local 7))
    (env := env) (state := state) (after := state) (value := size index) loaded typed
  exact .step _ (.refl _)

def tailEnv (env : Env) (index : Nat) : Env := (env.set 27 (size (index + 1))).set 28 (.scalar .unit)

theorem tail_locals (env : Env) (view : View) (left right index : Nat) (slot : Address)
    (locals : Locals env view left right slot) : Locals (tailEnv env index) view left right slot := by
  simpa [Locals, tailEnv, Control.Env.set] using locals

theorem tail_steps (args : List Value) (env : Env) (caller : State) (base index : Nat)
    (h7 : env 7 = some (counter ⟨caller.nextId, 0⟩)) (h13 : env 13 = some (size index))
    (initial : caller.valid = true) (live : (withCounter base index caller).valid = true)
    (bound : index + 1 < addressLimit) :
    Steps semantics args (.suspended ⟨tail, env, withCounter base index caller, frames⟩)
      (.suspended (loopConfig (tailEnv env index) (withCounter base (index + 1) caller))) := by
  have addition := add_one_eval (.local 13) args env (withCounter base index caller) index bound
    (scalar_read_size env 13 index (by omega) h13)
  have counterRef : (Ref.local 7).eval (env.set 27 (size (index + 1))) =
      .ok (counter ⟨caller.nextId, 0⟩) := by
    simp only [Ref.eval_local, Control.Env.set, Nat.reduceEqDiff, ↓reduceIte, h7, counter, Value.valid]
  have valueRef : (Ref.local 27).eval (env.set 27 (size (index + 1))) = .ok (size (index + 1)) := by
    simp only [Ref.eval_local, Control.Env.set, ↓reduceIte, size_valid (index + 1) bound]
  have written := counter_store base index (index + 1) caller initial live bound
  have stored := Prim.eval_store_ok (.local 7) (.local 27) args (env.set 27 (size (index + 1))) _ _ _ _ counterRef valueRef written
  have typed : semantics.hasType (size (index + 1)) usize = true := by
    simpa only [semantics] using size_typed (index + 1) bound
  apply Steps.bind_ok semantics args (id := 27) (type := usize)
    (prim := .scalar (.arithmetic .add .unchecked (.local 13) (.constant (.int false 64 1))))
    (env := env) (state := withCounter base index caller) (after := withCounter base index caller)
    (value := size (index + 1)) addition typed
  apply Steps.bind_ok semantics args (id := 28) (type := .scalar .unit) (prim := .store (.local 7) (.local 27)) stored
    (show (Value.scalar .unit).hasType (.scalar .unit) = true from rfl)
  exact .step _ (.refl _)

theorem loop_stop (args : List Value) (env : Env) (caller : State) (base : Nat) (view : View) (left right : Nat)
    (initial : caller.valid = true) (live : (withCounter base 4 caller).valid = true)
    (locals : Locals env view left right ⟨caller.nextId, 0⟩) :
    Steps semantics args (.suspended (loopConfig env (withCounter base 4 caller)))
      (.finished (.returned (.scalar .unit) (withCounter base 4 caller))) := by
  have first := body_enter args env (withCounter base 4 caller) ⟨caller.nextId, 0⟩ 4 locals.2.2.1
    (by decide) (counter_read base 4 caller initial live (by decide))
  apply first.trans semantics args
  have path := finite_steps semantics args head (env.set 13 (size 4)) (withCounter base 4 caller)
    (.block 14 (.scalar .unit) tail :: frames)
  rw [head_shape, condition_eval _ _ args _ _ 4 (by simp [Control.Env.set])
    (by simpa [Control.Env.set] using locals.2.2.2) (by decide), if_neg (by decide)] at path
  apply path.trans semantics args
  exact .step _ (.refl _)

theorem loop_next (args : List Value) (env : Env) (caller : State) (base : Nat) (view : View)
    (items : List (BitVec 32)) (left right : Nat) (index : Fin 4)
    (initial : caller.valid = true) (live : (withCounter base index.val caller).valid = true)
    (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right)
    (locals : Locals env view left right ⟨caller.nextId, 0⟩) :
    ∃ after nextEnv,
      Steps semantics args (.suspended (loopConfig env (withCounter base index.val caller)))
        (.suspended (loopConfig nextEnv (withCounter base (index.val + 1) after))) ∧
      Locals nextEnv view left right ⟨after.nextId, 0⟩ ∧
      after.valid = true ∧ (withCounter base (index.val + 1) after).valid = true ∧ Writable after view ∧
      Represents after view (ByteExchange.updated items left right (WordBytes.exchangeLane .little (items[left], items[right]) index)) ∧
      Frame view caller after := by
  have bound : index.val + 1 < addressLimit := by
    have := index.isLt
    have : 4 < addressLimit := by decide
    omega
  let entered := env.set 13 (size index.val)
  have enteredLocals : Locals entered view left right ⟨caller.nextId, 0⟩ := by
    simpa [entered, Locals, Control.Env.set] using locals
  obtain ⟨after, laneEnv, evaluated, laneLocals, laneIndex, valid, laneLive, writable, rep, frame⟩ :=
    lane_counter_refines args (conditionEnv entered index.val) caller base view items left right index initial live cap represented
      hl hr apart (condition_locals entered view left right index.val _ enteredLocals) (by simp [conditionEnv, entered, Control.Env.set])
  let caught := laneEnv.set 14 (.scalar .unit)
  have caughtLocals : Locals caught view left right ⟨after.nextId, 0⟩ := by
    simpa [caught, Locals, Control.Env.set] using laneLocals
  have advanced := counter_store base index.val (index.val + 1) after valid laneLive bound
  refine ⟨after, tailEnv caught index.val, ?_, tail_locals caught view left right index.val _ caughtLocals,
    valid, store_preserves_valid _ _ _ _ laneLive advanced, writable, rep, frame⟩
  apply (body_enter args env _ ⟨caller.nextId, 0⟩ index.val locals.2.2.1 (by omega)
    (counter_read base index.val caller initial live (by omega))).trans semantics args
  have path := finite_steps semantics args head entered (withCounter base index.val caller)
    (.block 14 (.scalar .unit) tail :: frames)
  rw [head_shape, condition_eval _ _ args entered _ index.val (by simp [entered, Control.Env.set])
    enteredLocals.2.2.2 (by omega), if_pos index.isLt, evaluated] at path
  apply path.trans semantics args
  exact tail_steps args caught after base index.val caughtLocals.2.2.1
    (by simpa [caught, Control.Env.set] using laneIndex) valid laneLive bound

def lanes (index : Nat) : List (Fin 4) := [0, 1, 2, 3].drop index

theorem lanes_next (index : Nat) (inside : index < 4) : lanes index = ⟨index, inside⟩ :: lanes (index + 1) := by
  have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

/-- Induction on the remaining lanes proves termination of the actual machine
loop and its word/list effect. There is no sufficient-fuel or successful-run
premise. The complete caller heap is related through the existing Frame. -/
theorem loop_refines (remaining index : Nat) (args : List Value) (env : Env) (caller : State)
    (base : Nat) (view : View) (items : List (BitVec 32)) (left right : Nat)
    (count : index + remaining = 4) (initial : caller.valid = true) (live : (withCounter base index caller).valid = true)
    (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right)
    (locals : Locals env view left right ⟨caller.nextId, 0⟩) :
    ∃ after, Steps semantics args (.suspended (loopConfig env (withCounter base index caller)))
        (.finished (.returned (.scalar .unit) (withCounter base 4 after))) ∧
      after.valid = true ∧ (withCounter base 4 after).valid = true ∧ Writable after view ∧
      Represents after view (ByteExchange.updated items left right
        (WordBytes.exchangeLanes .little (items[left], items[right]) (lanes index))) ∧ Frame view caller after := by
  induction remaining generalizing index env caller items with
  | zero =>
    have eq : index = 4 := by omega
    subst index
    refine ⟨caller, loop_stop args env caller base view left right initial live locals,
      initial, live, cap, ?_, Frame.refl view caller⟩
    simpa only [lanes, List.drop_succ_cons, List.drop_zero, WordBytes.exchangeLanes, List.foldl_nil,
      ByteExchange.updated_self items left right hl hr] using represented
  | succ remaining ih =>
    have inside : index < 4 := by omega
    obtain ⟨middle, nextEnv, first, nextLocals, middleValid, middleLive, middleCap, middleRep, firstFrame⟩ :=
      loop_next args env caller base view items left right ⟨index, inside⟩ initial live cap represented hl hr apart locals
    obtain ⟨after, rest, afterValid, afterLive, afterCap, afterRep, restFrame⟩ :=
      ih (index + 1) nextEnv middle _ (by omega) middleValid middleLive middleCap middleRep
        (by simpa [ByteExchange.updated] using hl) (by simpa [ByteExchange.updated] using hr) nextLocals
    refine ⟨after, first.trans semantics args rest, afterValid, afterLive, afterCap, ?_, firstFrame.trans restFrame⟩
    simpa only [ByteExchange.updated_left _ _ _ _ _ apart, ByteExchange.updated_right,
      ByteExchange.updated_updated items left right _ _ apart, lanes_next index inside,
      WordBytes.exchangeLanes, List.foldl_cons] using afterRep

theorem initialized_swap (args : List Value) (env : Env) (caller : State) (base : Nat)
    (view : View) (items : List (BitVec 32)) (left right : Nat)
    (initial : caller.valid = true) (live : (withCounter base 0 caller).valid = true)
    (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right)
    (locals : Locals env view left right ⟨caller.nextId, 0⟩) :
    ∃ after, Steps semantics args (.suspended ⟨entry, env, withCounter base 0 caller, []⟩)
        (.finished (.returned (.scalar .unit) (withCounter base 4 after))) ∧
      after.valid = true ∧ (withCounter base 4 after).valid = true ∧ Writable after view ∧
      Represents after view ((items.set left items[right]).set right items[left]) ∧ Frame view caller after := by
  obtain ⟨after, ran, valid, live, cap, rep, frame⟩ :=
    loop_refines 4 0 args env caller base view items left right rfl initial live cap represented hl hr apart locals
  refine ⟨after, ?_, valid, live, cap, ?_, frame⟩
  · exact .step _ (.step _ ran)
  · simpa only [lanes, List.drop_zero, WordBytes.exchange_four, ByteExchange.updated] using rep

end Compiler.ZigAir.MemoryWordSwap
