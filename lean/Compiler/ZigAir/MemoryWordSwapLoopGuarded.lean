/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapControlGuarded

namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine
open Memory.WordArray (View Writable Represents)
open MemoryFill (size counter unitRef)

theorem loop_stop_guarded (args : List Value) (env : Env) (caller : State) (base : Nat) (view : View) (left right : Nat)
    (initial : caller.valid = true) (live : (withCounter base 4 caller).valid = true)
    (locals : Locals env view left right ⟨caller.nextId, 0⟩) :
    GuardedSteps semantics args (Footprint view left right ⟨caller.nextId, 0⟩)
      (.suspended (loopConfig env (withCounter base 4 caller)))
      (.finished (.returned (.scalar .unit) (withCounter base 4 caller))) := by
  have first := body_enter_guarded args env (withCounter base 4 caller) view left right ⟨caller.nextId, 0⟩ 4
    locals.2.2.1 (by decide) (counter_read base 4 caller initial live (by decide))
  apply first.trans semantics args _
  have condition := condition_guarded lane (.jump 11 unitRef) args (env.set 13 (size 4)) (withCounter base 4 caller) 4
    view left right ⟨caller.nextId, 0⟩ (.block 14 (.scalar .unit) tail :: frames)
    (by simp [Control.Env.set]) (by simpa [Control.Env.set] using locals.2.2.2) (by decide)
  simp only [if_neg (show ¬(4 < 4) from by decide)] at condition
  apply condition.trans semantics args _
  apply GuardedSteps.control semantics args _ _ rfl
  apply GuardedSteps.control semantics args _ _ rfl
  exact .refl _

theorem loop_next_guarded (args : List Value) (env : Env) (caller : State) (base : Nat) (view : View)
    (items : List (BitVec 32)) (left right : Nat) (index : Fin 4)
    (initial : caller.valid = true) (live : (withCounter base index.val caller).valid = true)
    (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right)
    (locals : Locals env view left right ⟨caller.nextId, 0⟩) :
    ∃ after nextEnv,
      GuardedSteps semantics args (Footprint view left right ⟨caller.nextId, 0⟩)
        (.suspended (loopConfig env (withCounter base index.val caller)))
        (.suspended (loopConfig nextEnv (withCounter base (index.val + 1) after))) ∧
      Locals nextEnv view left right ⟨after.nextId, 0⟩ ∧ after.valid = true ∧
      (withCounter base (index.val + 1) after).valid = true ∧ Writable after view ∧
      Represents after view (ByteExchange.updated items left right (WordBytes.exchangeLane .little (items[left], items[right]) index)) ∧
      WordArray.Frame view caller after := by
  have bound : index.val + 1 < addressLimit := by
    have := index.isLt
    have : 4 < addressLimit := by decide
    omega
  let entered := env.set 13 (size index.val)
  have enteredLocals : Locals entered view left right ⟨caller.nextId, 0⟩ := by
    simpa [entered, Locals, Control.Env.set] using locals
  have conditionLocals := condition_locals entered view left right index.val _ enteredLocals
  have indexLocal : conditionEnv entered index.val 13 = some (size index.val) := by
    simp [conditionEnv, entered, Control.Env.set]
  obtain ⟨after, laneEnv, evaluated, laneLocals, laneIndex, valid, laneLive, writable, rep, frame⟩ :=
    lane_counter_refines args (conditionEnv entered index.val) caller base view items left right index initial live cap represented
      hl hr apart conditionLocals indexLocal
  let caught := laneEnv.set 14 (.scalar .unit)
  have caughtLocals : Locals caught view left right ⟨after.nextId, 0⟩ := by
    simpa [caught, Locals, Control.Env.set] using laneLocals
  have advanced := counter_store base index.val (index.val + 1) after valid laneLive bound
  refine ⟨after, tailEnv caught index.val, ?_, tail_locals caught view left right index.val _ caughtLocals,
    valid, store_preserves_valid _ _ _ _ laneLive advanced, writable, rep, frame⟩
  apply (body_enter_guarded args env _ view left right ⟨caller.nextId, 0⟩ index.val locals.2.2.1 (by omega)
    (counter_read base index.val caller initial live (by omega))).trans semantics args _
  have condition := condition_guarded lane (.jump 11 unitRef) args entered (withCounter base index.val caller) index.val
    view left right ⟨caller.nextId, 0⟩ (.block 14 (.scalar .unit) tail :: frames)
    (by simp [entered, Control.Env.set]) enteredLocals.2.2.2 (by omega)
  simp only [if_pos index.isLt] at condition
  apply condition.trans semantics args _
  have guarded := lane_guarded args (conditionEnv entered index.val) laneEnv (withCounter base index.val caller)
    (withCounter base index.val after) view items left right index ⟨caller.nextId, 0⟩
    (.block 14 (.scalar .unit) tail :: frames) live (counter_writable base index.val caller view initial cap)
    (counter_represents base index.val caller view items initial cap represented) hl hr apart conditionLocals indexLocal evaluated
  apply guarded.trans semantics args _
  have last := tail_guarded args caught after base index.val view left right caughtLocals.2.2.1
    (by simpa [caught, Control.Env.set] using laneIndex) valid laneLive bound
  simpa only [frame.nextId] using last

/-- The same decreasing lane count proves a checked terminal path. All four
byte operations and both counter accesses are checked on each iteration. -/
theorem loop_guarded (remaining index : Nat) (args : List Value) (env : Env) (caller : State) (base : Nat)
    (view : View) (items : List (BitVec 32)) (left right : Nat)
    (count : index + remaining = 4) (initial : caller.valid = true) (live : (withCounter base index caller).valid = true)
    (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right)
    (locals : Locals env view left right ⟨caller.nextId, 0⟩) :
    ∃ after, GuardedSteps semantics args (Footprint view left right ⟨caller.nextId, 0⟩)
      (.suspended (loopConfig env (withCounter base index caller))) (.finished (.returned (.scalar .unit) (withCounter base 4 after))) := by
  induction remaining generalizing index env caller items with
  | zero =>
    have same : index = 4 := by omega
    subst index
    exact ⟨caller, loop_stop_guarded args env caller base view left right initial live locals⟩
  | succ remaining ih =>
    have inside : index < 4 := by omega
    obtain ⟨middle, nextEnv, first, nextLocals, middleValid, middleLive, middleCap, middleRep, frame⟩ :=
      loop_next_guarded args env caller base view items left right ⟨index, inside⟩ initial live cap represented hl hr apart locals
    obtain ⟨after, rest⟩ := ih (index + 1) nextEnv middle _ (by omega) middleValid middleLive middleCap middleRep
      (by simpa [ByteExchange.updated] using hl) (by simpa [ByteExchange.updated] using hr) nextLocals
    rw [frame.nextId] at rest
    exact ⟨after, first.trans semantics args _ rest⟩

theorem initialized_guarded (args : List Value) (env : Env) (caller : State) (base : Nat)
    (view : View) (items : List (BitVec 32)) (left right : Nat)
    (initial : caller.valid = true) (live : (withCounter base 0 caller).valid = true)
    (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right)
    (locals : Locals env view left right ⟨caller.nextId, 0⟩) :
    ∃ after, GuardedSteps semantics args (Footprint view left right ⟨caller.nextId, 0⟩)
      (.suspended ⟨entry, env, withCounter base 0 caller, []⟩) (.finished (.returned (.scalar .unit) (withCounter base 4 after))) := by
  obtain ⟨after, path⟩ := loop_guarded 4 0 args env caller base view items left right rfl initial live cap represented hl hr apart locals
  refine ⟨after, ?_⟩
  apply GuardedSteps.control semantics args _ _ rfl
  exact GuardedSteps.control semantics args _ _ rfl path

end Compiler.ZigAir.MemoryWordSwap
