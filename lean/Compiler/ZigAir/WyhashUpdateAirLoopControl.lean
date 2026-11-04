/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirRoundRefinement
import Compiler.ZigAir.WyhashUpdateAirPrefix

set_option maxRecDepth 8192

namespace Compiler.ZigAir.WyhashUpdateAir.Loop
open Memory AggregateAir Compiler.Extraction Control.Machine
abbrev Code := Round.Code

def condition : Code :=
  (GeneratedWyhashUpdate.update.body.blockBody? 328).getD (.ret (.constant (.value (.scalar .unit))))

def body : Code := .block 328 (.scalar .unit) condition (.repeat rfl 327)

def continuation : Code :=
  (do
    let .block _ _ _ next ← GeneratedWyhashUpdate.update.body.block? 326 | none
    pure next).getD (.ret (.constant (.value (.scalar .unit))))

def entry : Code := .block 326 (.scalar .unit) (.loop rfl 327 body) continuation

def frames (outer : List (Frame Ty AggregateCall.Prim Ref)) :=
  .loop 327 body :: .block 326 (.scalar .unit) continuation :: outer

def innerFrames (outer : List (Frame Ty AggregateCall.Prim Ref)) :=
  .block 328 (.scalar .unit) (.repeat rfl 327) :: frames outer

theorem generated_entry : GeneratedWyhashUpdate.update.body.block? 326 = some entry := by decide +kernel

def guardCode : Code :=
  .bind 329 usize (.primitive (.load (.local 50))) $
  .bind 330 usize (.primitive (.memory (.scalar (.arithmetic .add .unchecked (.local 329) (.constant (.int false 64 48)))))) $
  .bind 331 (.pointer false false usize) (.primitive (.memory (.pointerField true (.local 7)))) $
  .bind 332 usize (.primitive (.load (.local 331))) $
  .bind 333 usize (.primitive (.memory (.scalar (.cast .bitcast (.int false 64) (.local 330))))) $
  .bind 334 usize (.primitive (.memory (.scalar (.cast .bitcast (.int false 64) (.local 332))))) $
  .bind 335 (.scalar .bool) (.primitive (.memory (.scalar (.comparison .lt (.local 333) (.local 334))))) $
  .branch (.local 335) Round.loopBody (.jump 326 (.constant (.value (.scalar .unit))))

theorem generated_guard : condition = guardCode := by decide +kernel

def guardEnv (env : Env) (inputSlot index count : Nat) : Env :=
  let env := env.set 329 (size index)
  let env := env.set 330 (size (index + 48))
  let env := env.set 331 (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩))
  let env := env.set 332 (size count)
  let env := env.set 333 (size (index + 48))
  let env := env.set 334 (size count)
  env.set 335 (.value (.scalar (.bool (decide (index + 48 < count)))))

theorem guard_before (env : Env) (inputSlot index count query : Nat) (earlier : query < 329) :
    guardEnv env inputSlot index count query = env query := by
  simp (disch := omega) only [guardEnv, Control.Env.set, if_neg]

theorem size_lt (state : State) (args : List Register) (env : Env) (left right a b : Nat)
    (aBound : a < addressLimit) (bBound : b < addressLimit)
    (ha : env left = some (size a)) (hb : env right = some (size b)) :
    (AggregateAir.Prim.memory (.scalar (.comparison .lt (.local left) (.local right)))).eval args env state =
      (.ok (.value (.scalar (.bool (decide (a < b))))), state) := by
  apply eval_scalar
  simp only [Scalar.Prim.eval, Scalar.Ref.eval, MemoryAir.scalarEnv, values, ha, hb, size,
    Scalar.unsigned_nat_valid a 64 aBound, Scalar.unsigned_nat_valid b 64 bBound,
    ↓reduceIte, bind, Except.bind, and_self, Scalar.Comparison.eval, Int.ofNat_lt]

theorem branch_steps (yes no : Code) (state : State) (args : List Register) (env : Env)
    (outer : List (Frame Ty AggregateCall.Prim Ref)) (reg : Nat) (flag : Bool)
    (found : env reg = some (.value (.scalar (.bool flag)))) :
    Steps AggregateCall.semantics args (.suspended ⟨.branch (.local reg) yes no, env, state, outer⟩)
      (.suspended ⟨if flag then yes else no, env, state, outer⟩) := by
  apply Steps.step
  simp only [step, AggregateCall.semantics, AggregateAir.semantics, Ref.eval, found,
    Register.valid, Value.valid, Scalar.Value.valid, ↓reduceIte, bind, Except.bind]
  exact .refl _

theorem guard_steps (state : State) (inputSlot indexSlot index count : Nat)
    (bound : index + 48 < addressLimit) (countBound : count < addressLimit)
    (indexRead : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (countRead : Memory.load state (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) =
      .ok (.scalar (.int false 64 count)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (foundIndex : env 50 = some (.value (slot true usize indexSlot)))
    (foundInput : env 7 = some (.value (slot false inputType inputSlot))) :
    Steps AggregateCall.semantics args (.suspended ⟨condition, env, state, outer⟩)
      (.suspended ⟨if index + 48 < count then Round.loopBody else .jump 326 (.constant (.value (.scalar .unit))),
        guardEnv env inputSlot index count, state, outer⟩) := by
  let e329 := env.set 329 (size index)
  let e330 := e329.set 330 (size (index + 48))
  let e331 := e330.set 331 (.value (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩))
  let e332 := e331.set 332 (size count)
  let e333 := e332.set 333 (size (index + 48))
  let e334 := e333.set 334 (size count)
  have p329 := eval_load (.local 50) args env state _ _ (value_local _ _ _ foundIndex rfl)
    (congrArg (Except.map Register.value) indexRead)
  have p330 := size_add_constant state index 48 329 args e329 bound (by simp [e329, Control.Env.set])
  have p331 := count_pointer state args e330 inputSlot 7 (by simp [e330, e329, Control.Env.set, foundInput])
  have p332 := eval_load (.local 331) args e331 state (.pointer (.pointer false false usize) ⟨inputSlot, 8⟩) _
    (value_local _ _ _ (by simp [e331, Control.Env.set]) rfl) (congrArg (Except.map Register.value) countRead)
  have p333 := size_bitcast state args e332 330 (index + 48) bound
    (by simp [e332, e331, e330, Control.Env.set])
  have p334 := size_bitcast state args e333 332 count countBound (by simp [e333, e332, Control.Env.set])
  have p335 := size_lt state args e334 333 334 (index + 48) count bound countBound
    (by simp [e334, e333, Control.Env.set]) (by simp [e334, Control.Env.set])
  rw [generated_guard]
  apply AggregateCall.primitive_steps args p329 (SliceBytesAir.size_typed _ (by omega))
  apply AggregateCall.primitive_steps args p330 (SliceBytesAir.size_typed _ bound)
  apply AggregateCall.primitive_steps args p331 rfl
  apply AggregateCall.primitive_steps args p332 (SliceBytesAir.size_typed _ countBound)
  apply AggregateCall.primitive_steps args p333 (SliceBytesAir.size_typed _ bound)
  apply AggregateCall.primitive_steps args p334 (SliceBytesAir.size_typed _ countBound)
  apply AggregateCall.primitive_steps args p335 rfl
  simpa only [decide_eq_true_eq] using branch_steps Round.loopBody
    (.jump 326 (.constant (.value (.scalar .unit)))) state args (guardEnv env inputSlot index count)
    outer 335 (decide (index + 48 < count)) (by simp [guardEnv, Control.Env.set])

def tail : Code :=
  .bind 578 usize (.primitive (.load (.local 50))) $
  .bind 579 usize (.primitive (.memory (.scalar (.arithmetic .add .unchecked (.local 578) (.constant (.int false 64 48)))))) $
  .bind 580 (.scalar .unit) (.primitive (.store (.local 50) (.local 579))) $
  .jump 328 (.constant (.value (.scalar .unit)))

theorem generated_tail : Round.lanesAt true 3 = tail := by decide +kernel

def tailEnv (env : Env) (index : Nat) : Env :=
  ((env.set 578 (size index)).set 579 (size (index + 48))).set 580 (.value (.scalar .unit))

theorem tail_before (env : Env) (index query : Nat) (earlier : query < 578) :
    tailEnv env index query = env query := by
  simp (disch := omega) only [tailEnv, Control.Env.set, if_neg]

/-- The counter store is derived from its actual writable root. It preserves
the model's strict comparison, and the back edge unwinds only the inner block. -/
theorem tail_steps {state : State} {indexSlot : Nat} (counter : CellFrame state indexSlot)
    (typed : counter.cell.type = usize) (index : Nat) (bound : index + 48 < addressLimit)
    (read : Memory.load state (slot true usize indexSlot) = .ok (.scalar (.int false 64 index)))
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref))
    (found : env 50 = some (.value (slot true usize indexSlot))) :
    ∃ cells, counter.cell.cells.write usize 0 (.scalar (.int false 64 (index + 48))) = .ok cells ∧
      Steps AggregateCall.semantics args (.suspended ⟨Round.lanesAt true 3, env, state, innerFrames outer⟩)
        (.suspended ⟨body, (tailEnv env index).set 328 (.value (.scalar .unit)), counter.install cells, frames outer⟩) ∧
      Memory.load (counter.install cells) (slot true usize indexSlot) = .ok (.scalar (.int false 64 (index + 48))) := by
  have valueValid : (Value.scalar (.int false 64 (index + 48))).valid = true :=
    Scalar.unsigned_nat_valid _ _ bound
  obtain ⟨cells, written⟩ := Cells.write_root counter.cell.cells (.scalar (.int false 64 (index + 48))) valueValid
  change counter.cell.cells.write usize 0 (.scalar (.int false 64 (index + 48))) = .ok cells at written
  have stored := counter.store_current (.scalar (.int false 64 (index + 48)))
    (by simpa [Value.hasType, typed, Value.type, Scalar.Value.type, usize] using valueValid)
  rw [typed, written] at stored
  change Memory.store state (slot true usize indexSlot) (.scalar (.int false 64 (index + 48))) =
    .ok (counter.install cells) at stored
  let e578 := env.set 578 (size index)
  let e579 := e578.set 579 (size (index + 48))
  have p578 := eval_load (.local 50) args env state _ _ (value_local _ _ _ found rfl)
    (congrArg (Except.map Register.value) read)
  have p579 := size_add_constant state index 48 578 args e578 bound (by simp [e578, Control.Env.set])
  have p580 := eval_store (.local 50) (.local 579) args e579 state (counter.install cells)
    (slot true usize indexSlot) (size (index + 48))
    (value_local _ _ _ (by simp [e579, e578, Control.Env.set, found]) rfl)
    (ref_local _ _ _ (by simp [e579, Control.Env.set]) valueValid) stored
  refine ⟨cells, written, ?_, ?_⟩
  · rw [generated_tail]
    apply AggregateCall.primitive_steps args p578 (SliceBytesAir.size_typed _ (by omega))
    apply AggregateCall.primitive_steps args p579 (SliceBytesAir.size_typed _ bound)
    apply AggregateCall.primitive_steps args p580 rfl
    exact .step _ (.step _ (.refl _))
  · exact load_after_store state (slot true usize indexSlot)
      (.scalar (.int false 64 (index + 48))) (counter.install cells) stored

end Compiler.ZigAir.WyhashUpdateAir.Loop
