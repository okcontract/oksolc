/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateExecution
import Compiler.ZigAir.AggregateSavedValue
import Compiler.ZigAir.MemoryStackFrameMutation

namespace Compiler.ZigAir.AggregateAir.SavedValue
open Memory

/-- The address bound comes from the actual allocation reached by save. It is
not a premise reserving spare capacity for a subsequent allocation. -/
theorem success_cursors (state after : State) (value : Value)
    (ran : save state value = (.ok (), after)) :
    after.nextId = state.nextId + 1 ∧ after.nextAddress < addressLimit := by
  cases allocated : Memory.allocate state value.type with
  | error fault => simp only [save, allocated] at ran; cases ran
  | ok pair =>
    obtain ⟨pointer, middle⟩ := pair
    cases stored : Memory.store middle pointer value with
    | error fault => simp only [save, allocated, stored] at ran; cases ran
    | ok reached =>
      simp only [save, allocated, stored, Prod.mk.injEq, true_and] at ran
      subst after
      have same := store_keeps_counters middle pointer value reached stored
      exact ⟨same.1.trans (allocate_pointer state value.type pointer middle allocated).2,
        same.2 ▸ allocate_end_bound state value.type pointer middle allocated⟩

end Compiler.ZigAir.AggregateAir.SavedValue

namespace Compiler.ZigAir.AggregateCall
open Memory AggregateAir Control.Machine

theorem primitive_bind (id : Nat) (type : Ty) (prim : AggregateAir.Prim) (next : Code)
    (args : List Register) (env : Env) (state after : State) (value : Register)
    (evaluated : prim.eval args env state = (.ok value, after)) (typed : value.hasType type = true) :
    (Control.Code.bind id type (.primitive prim) next).eval semantics args env state =
      next.eval semantics args (env.set id value) after :=
  bind_ok id type (.primitive prim) next args env state after value evaluated typed

theorem primitive_steps (args : List Register) {id : Nat} {type : Ty} {prim : AggregateAir.Prim}
    {next : Control.Code Ty Prim Ref true} {env : Env} {state after : State}
    {frames : List (Frame Ty Prim Ref)} {value : Register}
    {last : Execution Ty Prim Ref Register Fault State}
    (evaluated : prim.eval args env state = (.ok value, after)) (typed : value.hasType type = true)
    (tail : Steps semantics args (.suspended ⟨next, env.set id value, after, frames⟩) last) :
    Steps semantics args (.suspended ⟨.bind id type (.primitive prim) next, env, state, frames⟩) last :=
  Steps.bind_ok semantics args evaluated typed tail

/-- Reuse native save semantics in a loop-capable continuation. Neither an
allocation nor a store is replaced by a caller-supplied successful outcome. -/
theorem save_steps (value : Value) (reference : Ref) (allocationReg storeReg : Nat)
    (next : Control.Code Ty Prim Ref true) (frames : List (Frame Ty Prim Ref))
    (args : List Register) (env : Env) (state : State)
    (read : reference.eval (env.set allocationReg
      (.value (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩))) = .ok (.value value)) :
    Steps semantics args
      (.suspended ⟨.bind allocationReg (.pointer true false value.type) (.primitive (.memory (.alloc value.type)))
        (.bind storeReg (.scalar .unit) (.primitive (.store (.local allocationReg) reference)) next), env, state, frames⟩)
      (match SavedValue.save state value with
      | (.error fault, after) => .finished (.fault fault after)
      | (.ok (), after) => .suspended ⟨next,
          (env.set allocationReg (.value (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩))).set
            storeReg (.value (.scalar .unit)), after, frames⟩) := by
  cases allocation : Memory.allocate state value.type with
  | error fault =>
    simp only [SavedValue.save, allocation]
    exact Steps.bind_fault semantics args (by
      simp only [semantics, Prim.eval, AggregateAir.Prim.eval, AggregateAir.Prim.transition,
        MemoryAir.Prim.transition, allocation, bind, Except.bind])
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    have pointerEq := (allocate_pointer state value.type pointer allocated allocation).1
    rw [pointerEq] at allocation
    have allocates := AggregateAir.eval_alloc value.type args env state allocated _ allocation
    have first := Steps.bind_ok semantics args (frames := frames) (id := allocationReg)
      (type := .pointer true false value.type) (prim := .primitive (.memory (.alloc value.type)))
      (env := env) (state := state) (after := allocated)
      (next := .bind storeReg (.scalar .unit) (.primitive (.store (.local allocationReg) reference)) next)
      (show Prim.eval (.primitive (.memory (.alloc value.type))) args env state = _ from allocates)
      (pointer_typed _ _) (.refl _)
    have selected := value_local (env.set allocationReg
      (.value (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩))) allocationReg
      (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩) (by simp [Control.Env.set]) rfl
    cases written : Memory.store allocated (.pointer (.pointer true false value.type) ⟨state.nextId, 0⟩) value with
    | error fault =>
      simp only [SavedValue.save, allocation, written]
      apply first.trans semantics args
      apply Steps.bind_fault
      simp only [semantics, Prim.eval, AggregateAir.Prim.eval, AggregateAir.Prim.transition,
        selected, read, AggregateAir.store, written, bind, Except.bind]
    | ok after =>
      simp only [SavedValue.save, allocation, written]
      apply first.trans semantics args
      apply Steps.bind_ok
      · exact AggregateAir.eval_store _ _ _ _ _ _ _ _ selected read written
      · rfl
      · exact .refl _

/-- A finite path through the original machine supplies a sufficient budget.
The wrapper applies exactly its terminal return checks and cleanup. -/
theorem Program.run_of_steps (program : Program) (args : List Register) (state : State)
    (outcome : Control.Outcome Register Fault State)
    (checked : (state.valid && decide (args.length = program.parameters.length) &&
      (args.zip program.parameters).all (fun (value, type) => value.hasType type)) = true)
    (path : Steps semantics args (.suspended ⟨program.body, fun _ => none, state, []⟩) (.finished outcome)) :
    ∃ fuel, program.runFuel fuel args state = Invocation.finish program.returnType state.nextId outcome := by
  obtain ⟨fuel, run⟩ := (steps_iff_fuel semantics args _ _).mp path
  exact ⟨fuel, by simp only [Program.runFuel, Program.start, checked, ↓reduceIte, Invocation.resume,
    Control.Machine.run, run]⟩

end Compiler.ZigAir.AggregateCall
