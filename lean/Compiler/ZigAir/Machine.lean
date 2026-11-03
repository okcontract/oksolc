/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.ControlSafety

/-! Resumable structured AIR execution. Fuel counts control transitions, not gas,
CPU time or allocation. A suspended configuration retains all effects and can
be resumed; suspension is neither divergence nor a modeled program fault.

Frames retain code, not entry environments or heap snapshots: `br` and `repeat`
carry the current SSA environment and state. Invocation cleanup belongs to the
caller, after a terminal outcome, never at suspension. Calls are not modeled. -/
namespace Compiler.ZigAir.Control.Machine

inductive Frame (Ty Prim Ref : Type) where
  | block (id : Nat) (type : Ty) (next : Code Ty Prim Ref true)
  | loop (id : Nat) (body : Code Ty Prim Ref true)

structure Config (Ty Prim Ref Value State : Type) where
  code : Code Ty Prim Ref true
  env : Env Value
  state : State
  frames : List (Frame Ty Prim Ref) := []

inductive Execution (Ty Prim Ref Value Fault State : Type) where
  | finished (outcome : Outcome Value Fault State)
  | suspended (config : Config Ty Prim Ref Value State)

def Execution.state : Execution Ty Prim Ref Value Fault State → State
  | .finished outcome => outcome.state
  | .suspended config => config.state

/-- A block result unwinds intervening frames and binds at its matching block.
A loop cannot receive a block result: AIR `repeat` is a distinct instruction. -/
def jump (sem : Semantics Ty Prim Ref Value Fault State) (target : Nat) (value : Value)
    (env : Env Value) (state : State) :
    List (Frame Ty Prim Ref) → Execution Ty Prim Ref Value Fault State
  | [] => .finished (.jumped target value env state)
  | .block id ty next :: frames =>
    if target = id then
      if sem.hasType value ty then .suspended ⟨next, env.set id value, state, frames⟩
      else .finished (.fault sem.malformed state)
    else jump sem target value env state frames
  | .loop id _ :: frames =>
    if target = id then .finished (.fault sem.malformed state)
    else jump sem target value env state frames

/-- A back edge keeps its matching loop frame, dropping only inner frames. -/
def backedge (sem : Semantics Ty Prim Ref Value Fault State) (target : Nat)
    (env : Env Value) (state : State) :
    List (Frame Ty Prim Ref) → Execution Ty Prim Ref Value Fault State
  | [] => .finished (.fault sem.malformed state)
  | .block id _ _ :: frames =>
    if target = id then .finished (.fault sem.malformed state)
    else backedge sem target env state frames
  | .loop id body :: frames =>
    if target = id then .suspended ⟨body, env, state, .loop id body :: frames⟩
    else backedge sem target env state frames

def step (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value)
    (config : Config Ty Prim Ref Value State) : Execution Ty Prim Ref Value Fault State :=
  let ⟨code, env, state, frames⟩ := config
  match code with
  | .bind id ty prim next =>
    let (result, after) := sem.evalPrim prim args env state
    match result with
    | .error reason => .finished (.fault reason after)
    | .ok value =>
      if sem.hasType value ty then .suspended ⟨next, env.set id value, after, frames⟩
      else .finished (.fault sem.malformed after)
  | .branch condition yes no =>
    match sem.evalRef condition env with
    | .error reason => .finished (.fault reason state)
    | .ok value => match sem.truth value with
      | none => .finished (.fault sem.malformed state)
      | some flag => .suspended ⟨if flag then yes else no, env, state, frames⟩
  | .block id ty body next => .suspended ⟨body, env, state, .block id ty next :: frames⟩
  | .loop _ id body => .suspended ⟨body, env, state, .loop id body :: frames⟩
  | .repeat _ target => backedge sem target env state frames
  | .jump target ref =>
    match sem.evalRef ref env with
    | .error reason => .finished (.fault reason state)
    | .ok value => jump sem target value env state frames
  | .ret ref =>
    match sem.evalRef ref env with
    | .error reason => .finished (.fault reason state)
    | .ok value => .finished (.returned value state)

def advance (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value) :
    Nat → Execution Ty Prim Ref Value Fault State → Execution Ty Prim Ref Value Fault State
  | 0, execution => execution
  | _ + 1, .finished outcome => .finished outcome
  | fuel + 1, .suspended config => advance sem args fuel (step sem args config)

def run (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value) (fuel : Nat)
    (config : Config Ty Prim Ref Value State) : Execution Ty Prim Ref Value Fault State :=
  advance sem args fuel (.suspended config)

/-- Arbitrary finite executions, independent of any particular fuel budget.
There are no transitions out of terminal outcomes. -/
inductive Steps (sem : Semantics Ty Prim Ref Value Fault State) (args : List Value) :
    Execution Ty Prim Ref Value Fault State → Execution Ty Prim Ref Value Fault State → Prop
  | refl (execution) : Steps sem args execution execution
  | step (config) {last} : Steps sem args (step sem args config) last →
      Steps sem args (.suspended config) last

end Compiler.ZigAir.Control.Machine
