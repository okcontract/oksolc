/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirRemainder

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Suffix
open Memory AggregateAir Compiler.Extraction Control.Machine
abbrev Code := Round.Code

def copy : Code := (do
  let .block _ _ _ next := Remainder.suffix.dropBindings 4 | none
  let .branch _ yes _ := next | none
  pure yes).getD (.ret (.constant (.value (.scalar .unit))))

def skip : Code := .jump 595 (.constant (.value (.scalar .unit)))

def secondary : Code :=
  .bind 602 usize (.primitive (.load (.local 50))) $
  .bind 603 usize (.primitive (.memory (.scalar (.cast .bitcast (.int false 64) (.local 602))))) $
  .bind 604 (.scalar .bool) (.primitive (.memory (.scalar (.comparison .ge (.local 603) (.constant (.int false 64 48)))))) $
  .jump 600 (.local 604)

def decision : Code := .block 600 (.scalar .bool)
  (.branch (.local 599) secondary (.jump 600 (.constant (.value (.scalar (.bool false))))))
  (.branch (.local 600) copy skip)

def guard : Code :=
  .bind 596 (.pointer false false usize) (.primitive (.memory (.pointerField true (.local 594)))) $
  .bind 597 usize (.primitive (.load (.local 596))) $
  .bind 598 usize (.primitive (.memory (.scalar (.cast .bitcast (.int false 64) (.local 597))))) $
  .bind 599 (.scalar .bool) (.primitive (.memory (.scalar (.comparison .lt (.local 598) (.constant (.int false 64 16)))))) decision

theorem generated_guard : Remainder.suffix = guard := by decide +kernel

def guardEnv (env : Env) (restSlot count : Nat) : Env :=
  let env := env.set 596 (.value (.pointer (.pointer false false usize) ⟨restSlot, 8⟩))
  let env := env.set 597 (size count)
  let env := env.set 598 (size count)
  env.set 599 (.value (.scalar (.bool (decide (count < 16)))))

theorem prefix_steps (state : State) (restSlot count : Nat) (bound : count < addressLimit)
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) = .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundRest : env 594 = some (.value (slot false inputType restSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨Remainder.suffix, env, state, outer⟩)
      (.suspended ⟨decision, guardEnv env restSlot count, state, outer⟩) := by
  let e596 := env.set 596 (.value (.pointer (.pointer false false usize) ⟨restSlot, 8⟩))
  let e597 := e596.set 597 (size count)
  let e598 := e597.set 598 (size count)
  have p596 := count_pointer state args env restSlot 594 foundRest
  have p597 := eval_load (.local 596) args e596 state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) _
    (value_local _ _ _ (by simp [e596, Control.Env.set]) rfl) (congrArg (Except.map Register.value) countRead)
  have p598 := size_bitcast state args e597 597 count bound (by simp [e597, Control.Env.set])
  have p599 := size_comparison state args e598 .lt (.local 598) (.constant (.int false 64 16)) count 16
    (SliceBytesAir.scalar_size e598 598 count bound (by simp [e598, Control.Env.set])) rfl
  simp only [Scalar.Comparison.eval, Int.ofNat_lt] at p599
  rw [generated_guard, guard]
  exact AggregateCall.primitive_steps args p596 rfl <|
    AggregateCall.primitive_steps args p597 (SliceBytesAir.size_typed _ bound) <|
    AggregateCall.primitive_steps args p598 (SliceBytesAir.size_typed _ bound) <|
    AggregateCall.primitive_steps args p599 rfl (.refl _)

/-- Preserve the source short-circuit order: the index load occurs only after
the remaining length has passed the first comparison. -/
theorem decision_steps (state : State) (index count indexSlot : Nat) (bound : index < addressLimit)
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot)))
    (foundCount : env 599 = some (.value (.scalar (.bool (decide (count < 16)))))) :
    ∃ nextEnv, Steps AggregateCall.semantics args (.suspended ⟨decision, env, state, outer⟩)
        (.suspended ⟨if count < 16 ∧ 48 ≤ index then copy else skip, nextEnv, state, outer⟩) ∧
      ∀ query < 596, nextEnv query = env query := by
  let inner := Frame.block 600 (.scalar .bool) (.branch (.local 600) copy skip) :: outer
  have first : Steps AggregateCall.semantics args (.suspended ⟨decision, env, state, outer⟩)
      (.suspended ⟨.branch (.local 599) secondary (.jump 600 (.constant (.value (.scalar (.bool false))))), env, state, inner⟩) :=
    .step _ (.refl _)
  by_cases short : count < 16
  · have branch := Loop.branch_steps secondary (.jump 600 (.constant (.value (.scalar (.bool false))))) state args env inner
      599 true (by simpa only [decide_eq_true short] using foundCount)
    let e602 := env.set 602 (size index)
    let e603 := e602.set 603 (size index)
    let e604 := e603.set 604 (.value (.scalar (.bool (decide (48 ≤ index)))))
    let next := e604.set 600 (.value (.scalar (.bool (decide (48 ≤ index)))))
    have p602 := eval_load (.local 50) args env state _ _ (value_local _ _ _ foundIndex rfl)
      (congrArg (Except.map Register.value) indexRead)
    have p603 := size_bitcast state args e602 602 index bound (by simp [e602, Control.Env.set])
    have p604 := size_comparison state args e603 .ge (.local 603) (.constant (.int false 64 48)) index 48
      (SliceBytesAir.scalar_size e603 603 index bound (by simp [e603, Control.Env.set])) rfl
    simp only [Scalar.Comparison.eval, Int.ofNat_le] at p604
    have load : Steps AggregateCall.semantics args (.suspended ⟨secondary, env, state, inner⟩)
        (.suspended ⟨.branch (.local 600) copy skip, next, state, outer⟩) :=
      AggregateCall.primitive_steps args p602 (SliceBytesAir.size_typed _ bound) <|
        AggregateCall.primitive_steps args p603 (SliceBytesAir.size_typed _ bound) <|
        AggregateCall.primitive_steps args p604 rfl (.step _ (.refl _))
    have chosen := Loop.branch_steps copy skip state args next outer 600 (decide (48 ≤ index))
      (by simp [next, Control.Env.set])
    refine ⟨next, ?_, ?_⟩
    · simpa only [short, true_and, decide_eq_true_eq, ↓reduceIte] using
        first.trans AggregateCall.semantics args (branch.trans AggregateCall.semantics args
          (load.trans AggregateCall.semantics args chosen))
    · intro query earlier
      simp (disch := omega) only [next, e604, e603, e602, Control.Env.set, if_neg]
  · have branch := Loop.branch_steps secondary (.jump 600 (.constant (.value (.scalar (.bool false))))) state args env inner
      599 false (by simpa only [decide_eq_false short] using foundCount)
    let next := env.set 600 (.value (.scalar (.bool false)))
    have jump : Steps AggregateCall.semantics args
        (.suspended ⟨.jump 600 (.constant (.value (.scalar (.bool false)))), env, state, inner⟩)
        (.suspended ⟨.branch (.local 600) copy skip, next, state, outer⟩) := .step _ (.refl _)
    have chosen := Loop.branch_steps copy skip state args next outer 600 false (by simp [next, Control.Env.set])
    refine ⟨next, ?_, ?_⟩
    · simpa only [short, false_and, ↓reduceIte] using first.trans AggregateCall.semantics args
        (branch.trans AggregateCall.semantics args (jump.trans AggregateCall.semantics args chosen))
    · intro query earlier
      simp (disch := omega) only [next, Control.Env.set, if_neg]

theorem guard_steps (state : State) (index count restSlot indexSlot : Nat)
    (indexBound : index < addressLimit) (countBound : count < addressLimit)
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨restSlot, 8⟩) = .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot)))
    (foundRest : env 594 = some (.value (slot false inputType restSlot))) :
    ∃ nextEnv, Steps AggregateCall.semantics args (.suspended ⟨Remainder.suffix, env, state, outer⟩)
        (.suspended ⟨if count < 16 ∧ 48 ≤ index then copy else skip, nextEnv, state, outer⟩) ∧
      ∀ query < 596, nextEnv query = env query := by
  have head := prefix_steps state restSlot count countBound countRead args env outer foundRest
  obtain ⟨next, path, before⟩ := decision_steps state index count indexSlot indexBound indexRead args
    (guardEnv env restSlot count) outer (by simp [guardEnv, Control.Env.set, foundIndex])
    (by simp [guardEnv, Control.Env.set])
  refine ⟨next, head.trans AggregateCall.semantics args path, ?_⟩
  intro query earlier
  rw [before query earlier]
  simp (disch := omega) only [guardEnv, Control.Env.set, if_neg]

end Compiler.ZigAir.WyhashUpdateAir.Suffix
