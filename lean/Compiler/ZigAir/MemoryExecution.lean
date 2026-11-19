/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAir
import Compiler.ZigAir.Machine

/-! Invocation boundaries for resumable memory AIR. Suspensions carry the
original arguments, return type and stack mark. Only a terminal machine outcome
crosses `Program.finish`; no stack cleanup or argument revalidation occurs when
fuel runs out. Calls between invocations remain outside this model. -/
namespace Compiler.ZigAir.MemoryAir
open Memory Control.Machine

inductive Invocation where
  | finished (result : Except Fault Value) (state : State)
  | suspended (returnType : Ty) (mark : Nat) (args : List Value)
      (config : Config Ty Prim Ref Value State)

def Invocation.state : Invocation → State
  | .finished _ state => state
  | .suspended _ _ _ config => config.state

def Invocation.finish (returnType : Ty) (mark : Nat) (outcome : Control.Outcome Value Fault State) : Invocation :=
  let result := Program.finish returnType mark outcome
  .finished result.1 result.2

def Invocation.resume (fuel : Nat) : Invocation → Invocation
  | .finished result state => .finished result state
  | .suspended returnType mark args config =>
    match run semantics args fuel config with
    | .finished outcome => Invocation.finish returnType mark outcome
    | .suspended next => .suspended returnType mark args next

def Program.enableLoops (program : Program) : Program true :=
  { program with body := program.body.enableLoops }

def Program.start (program : Program true) (args : List Value) (state : State) : Invocation :=
  if program.accepts args state then
    .suspended program.returnType state.nextId args ⟨program.body, fun _ => none, state, []⟩
  else .finished (.error .malformed) state

def Program.runFuel (program : Program true) (fuel : Nat) (args : List Value) (state : State) : Invocation :=
  (program.start args state).resume fuel

end Compiler.ZigAir.MemoryAir
