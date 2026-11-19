/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ConstructionProofs

namespace Compiler.Algebraic.ConstructionTests
open Contract.Yul

inductive Event where
  | constant (value : Word) (debug : Nat)
  | operation (op : BuildOp) (ids : List NodeId) (debug : Nat)
  deriving DecidableEq, Repr

structure Trace where
  events : List Event := []
  next : NodeId := 7
  budget : Nat := 2
  deriving DecidableEq, Repr

/-- Record attempted callbacks, including the failed one. This observer checks
effect order and annotations independently of the numerical graph model. -/
def request (event : Event) : Effect Trace String NodeId := fun before =>
  let after := { before with events := before.events ++ [event] }
  if before.budget = 0 then (.error "allocation", after)
  else (.ok before.next, { after with next := before.next + 1, budget := before.budget - 1 })

def callbacks : Builder (Effect Trace String) Nat := {
  makeConstant := fun value debug => request (.constant value debug)
  makeOperation := fun op ids debug => request (.operation op ids debug)
}

def observe (replacement : Replacement) (budget : Nat := 2) : Except String NodeId × Trace :=
  zigApply replacement callbacks 2 3 9 { budget := budget }

example : observe .left 0 = (.ok 2, { budget := 0 }) := by rfl
example : observe .not_right = (.ok 7,
    { events := [.operation .NOT [3] 9], next := 8, budget := 1 }) := by rfl
example : observe .bool_left = (.ok 8,
    { events := [.operation .ISZERO [2] 9, .operation .ISZERO [7] 9], next := 9, budget := 0 }) := by rfl
example : observe .neg_right 1 = (.error "allocation",
    { events := [.constant 0 9, .operation .SUB [7, 3] 9], next := 8, budget := 0 }) := by rfl
example : observe .neg_left 0 = (.error "allocation",
    { events := [.constant 0 9], next := 7, budget := 0 }) := by rfl

end Compiler.Algebraic.ConstructionTests
