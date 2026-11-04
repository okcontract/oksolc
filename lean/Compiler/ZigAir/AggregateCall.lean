/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.AggregateAirProofs

/-! Finite calls into concrete aggregate AIR programs. Callees use the existing
argument checks and scoped return/cleanup evaluator. A failing call retains its
reached heap and allocation cursors; reference failure has no effects. This does
not admit recursive or looping callees. -/
namespace Compiler.ZigAir.AggregateCall
open Memory AggregateAir

inductive Prim where
  | primitive (operation : AggregateAir.Prim)
  | invoke (program : AggregateAir.Program) (arguments : List Ref)
  /-- Byte copy retains completed writes if a later access fails. -/
  | copyBytes (target source : Ref)
  deriving DecidableEq, Repr

def Prim.eval (prim : Prim) (args : List Register) (env : Env) (state : State) : Except Fault Register × State :=
  match prim with
  | .primitive operation => operation.eval args env state
  | .invoke program arguments =>
    match arguments.mapM (fun ref => ref.eval env) with
    | .error fault => (.error fault, state)
    | .ok values => program.run values state
  | .copyBytes target source =>
    match (do return (← target.value env, ← source.value env)) with
    | .error fault => (.error fault, state)
    | .ok (target, source) =>
      let (result, after) := ByteRange.copy state target source
      (result.map (fun _ => .value (.scalar .unit)), after)

def semantics : Control.Semantics Ty Prim Ref Register Fault State where
  hasType := Register.hasType
  truth := AggregateAir.semantics.truth
  evalRef := Ref.eval
  evalPrim := Prim.eval
  malformed := .malformed

abbrev Code := Control.Code Ty Prim Ref

/-- Three consecutive caller instructions, with the callee supplied as an
executable program rather than an assumed callback result. -/
def allocateCallStore (allocationReg resultReg storeReg : Nat)
    (callee : AggregateAir.Program) (arguments : List Ref) (next : Code) : Code :=
  .bind allocationReg (.pointer true false callee.returnType) (.primitive (.memory (.alloc callee.returnType)))
    (.bind resultReg callee.returnType (.invoke callee arguments)
      (.bind storeReg (.scalar .unit) (.primitive (.store (.local allocationReg) (.local resultReg))) next))

theorem bind_ok (id : Nat) (type : Ty) (prim : Prim) (next : Code)
    (args : List Register) (env : Env) (state after : State) (value : Register)
    (executed : prim.eval args env state = (.ok value, after)) (typed : value.hasType type = true) :
    (Control.Code.bind id type prim next).eval semantics args env state =
      next.eval semantics args (env.set id value) after := by
  simp only [Control.Code.eval, semantics, executed, typed, ↓reduceIte]

theorem bind_fault (id : Nat) (type : Ty) (prim : Prim) (next : Code)
    (args : List Register) (env : Env) (state after : State) (fault : Fault)
    (executed : prim.eval args env state = (.error fault, after)) :
    (Control.Code.bind id type prim next).eval semantics args env state = .fault fault after := by
  simp only [Control.Code.eval, semantics, executed]

theorem invoke_constant (program : AggregateAir.Program) (value : Register)
    (args : List Register) (env : Env) (state : State) (valid : value.valid = true) :
    (Prim.invoke program [.constant value]).eval args env state = program.run [value] state := by
  simp [Prim.eval, ref_constant value valid]
  rfl

end Compiler.ZigAir.AggregateCall
