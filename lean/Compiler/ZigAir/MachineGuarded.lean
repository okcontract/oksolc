/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MachineObservations

/-! Compositional path certificates over the existing step relation. Every
attempted primitive must satisfy the observation predicate, including a failing
last attempt. A terminal certificate covers every execution budget; suspension
at a chosen intermediate point is not a certificate for its continuation. -/
namespace Compiler.ZigAir.Control.Machine

inductive GuardedSteps (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value)
    (allowed : Observation Ty Prim Value State → Prop) :
    Execution Ty Prim Ref Value Fault State → Execution Ty Prim Ref Value Fault State → Prop
  | refl (execution) : GuardedSteps sem args allowed execution execution
  | step (config) {last}
      (checked : ∀ event ∈ observe config, allowed event)
      (tail : GuardedSteps sem args allowed (step sem args config) last) :
      GuardedSteps sem args allowed (.suspended config) last

variable (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value)
    (allowed : Observation Ty Prim Value State → Prop)

theorem GuardedSteps.erases {first last : Execution Ty Prim Ref Value Fault State}
    (path : GuardedSteps sem args allowed first last) : Steps sem args first last := by
  induction path with
  | refl => exact .refl _
  | step config _ _ ih => exact .step config ih

theorem GuardedSteps.trans {first middle last : Execution Ty Prim Ref Value Fault State}
    (left : GuardedSteps sem args allowed first middle) (right : GuardedSteps sem args allowed middle last) :
    GuardedSteps sem args allowed first last := by
  induction left with
  | refl => exact right
  | step config checked _ ih => exact .step config checked (ih right)

theorem GuardedSteps.bind_ok {id : Nat} {type : Ty} {prim : Prim} {next : Code Ty Prim Ref true}
    {env : Env Value} {state after : State} {frames : List (Frame Ty Prim Ref)} {value : Value}
    {last : Execution Ty Prim Ref Value Fault State}
    (checked : allowed ⟨(id, type, prim), env, state⟩)
    (evaluated : sem.evalPrim prim args env state = (.ok value, after))
    (typed : sem.hasType value type = true)
    (tail : GuardedSteps sem args allowed (.suspended ⟨next, env.set id value, after, frames⟩) last) :
    GuardedSteps sem args allowed (.suspended ⟨.bind id type prim next, env, state, frames⟩) last := by
  apply GuardedSteps.step _ (by simpa only [observe, List.mem_singleton, forall_eq] using checked)
  simpa only [Machine.step, evaluated, if_pos typed] using tail

theorem GuardedSteps.bind_fault {id : Nat} {type : Ty} {prim : Prim} {next : Code Ty Prim Ref true}
    {env : Env Value} {state after : State} {frames : List (Frame Ty Prim Ref)} {fault : Fault}
    (checked : allowed ⟨(id, type, prim), env, state⟩)
    (evaluated : sem.evalPrim prim args env state = (.error fault, after)) :
    GuardedSteps sem args allowed (.suspended ⟨.bind id type prim next, env, state, frames⟩)
      (.finished (.fault fault after)) := by
  apply GuardedSteps.step _ (by simpa only [observe, List.mem_singleton, forall_eq] using checked)
  simp only [Machine.step, evaluated]
  exact .refl _

theorem GuardedSteps.control (config : Config Ty Prim Ref Value State)
    {last : Execution Ty Prim Ref Value Fault State} (silent : observe config = [])
    (tail : GuardedSteps sem args allowed (Machine.step sem args config) last) :
    GuardedSteps sem args allowed (.suspended config) last :=
  .step config (by simp only [silent, List.not_mem_nil, false_implies, implies_true]) tail

/-- Every budget is covered, including budgets that suspend before termination
and budgets larger than the path. No event after a failing primitive is invented. -/
theorem GuardedSteps.terminal_trace {first : Execution Ty Prim Ref Value Fault State}
    {outcome : Outcome Value Fault State} (path : GuardedSteps sem args allowed first (.finished outcome)) (fuel : Nat) :
    ∀ event ∈ (trace sem args fuel first).1, allowed event := by
  generalize lastEq : Execution.finished outcome = last at path
  induction path generalizing fuel with
  | refl => rw [← lastEq]; simp [trace_finished]
  | step config checked rest ih =>
    cases fuel with
    | zero => simp [trace]
    | succ fuel =>
      intro event present
      have member : event ∈ observe config ∨ event ∈ (trace sem args fuel (Machine.step sem args config)).1 := by
        simpa only [trace, List.mem_append] using present
      rcases member with here | later
      · exact checked event here
      · exact ih fuel lastEq event later

end Compiler.ZigAir.Control.Machine
