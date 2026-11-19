/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateCall
import Compiler.ZigAir.MachineRefinement

/-! Resumable aggregate AIR with finite callees. The existing control machine
owns loop progress. Suspension retains the invocation mark, arguments, locals
and reached writes; only terminal return/failure cleans invocation locals. -/
namespace Compiler.ZigAir.AggregateCall
open Memory AggregateAir Control.Machine

structure Program where
  parameters : List Ty
  returnType : Ty
  body : Control.Code Ty Prim Ref true
  deriving DecidableEq, Repr

inductive Invocation where
  | finished (result : Except Fault Register) (state : State)
  | suspended (returnType : Ty) (mark : Nat) (args : List Register)
      (config : Config Ty Prim Ref Register State)

def Invocation.state : Invocation → State
  | .finished _ state => state
  | .suspended _ _ _ config => config.state

def Invocation.finish (returnType : Ty) (mark : Nat)
    (outcome : Control.Outcome Register Fault State) : Invocation :=
  let result := AggregateAir.Program.finish returnType mark outcome
  .finished result.1 result.2

def Invocation.resume (fuel : Nat) : Invocation → Invocation
  | .finished result state => .finished result state
  | .suspended returnType mark args config =>
    match run semantics args fuel config with
    | .finished outcome => Invocation.finish returnType mark outcome
    | .suspended next => .suspended returnType mark args next

def Program.start (program : Program) (args : List Register) (state : State) : Invocation :=
  if state.valid && args.length = program.parameters.length &&
      (args.zip program.parameters).all (fun (value, type) => value.hasType type) then
    .suspended program.returnType state.nextId args ⟨program.body, fun _ => none, state, []⟩
  else .finished (.error .malformed) state

def Program.runFuel (program : Program) (fuel : Nat) (args : List Register) (state : State) : Invocation :=
  (program.start args state).resume fuel

theorem Invocation.resume_add (first second : Nat) (invocation : Invocation) :
    invocation.resume (first + second) = (invocation.resume first).resume second := by
  cases invocation with
  | finished result state => rfl
  | suspended returnType mark args config =>
    simp only [Invocation.resume, run, advance_add]
    cases h : advance semantics args first (.suspended config) <;>
      simp only [advance_finished, Invocation.finish]

/-- Different sufficient budgets cannot select a different hash execution. -/
theorem Invocation.finished_unique (invocation : Invocation) (first second : Nat)
    (left right : Except Fault Register) (leftState rightState : State)
    (hleft : invocation.resume first = .finished left leftState)
    (hright : invocation.resume second = .finished right rightState) :
    (left, leftState) = (right, rightState) := by
  have a : invocation.resume (first + second) = .finished left leftState := by
    rw [Invocation.resume_add, hleft]
    rfl
  have b : invocation.resume (first + second) = .finished right rightState := by
    rw [Nat.add_comm, Invocation.resume_add, hright]
    rfl
  have same := a.symm.trans b
  injection same with values states
  exact Prod.ext values states

end Compiler.ZigAir.AggregateCall
