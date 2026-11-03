/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Algebraic.Model

namespace Compiler.Algebraic
open Contract.Yul

abbrev NodeId := BitVec 32

inductive BuildOp where
  | NOT | SUB | ISZERO
  deriving DecidableEq, Repr

def BuildOp.eval : BuildOp → List Word → Option Word
  | .NOT, [a] => some (Unary.bitnot.eval a)
  | .SUB, [a, b] => some (Binary.sub.eval a b)
  | .ISZERO, [a] => some (Unary.iszero.eval a)
  | _, _ => none

/-- The callback boundary of Zig's generic `apply`. No allocator is assumed
infallible, and no new node is assumed distinct from an interned old node. -/
structure Builder (m : Type → Type) (Debug : Type) where
  makeConstant : Word → Debug → m NodeId
  makeOperation : BuildOp → List NodeId → Debug → m NodeId

/-- Independent construction specification. Its monad retains call order,
failures and callback arguments, not just the final numerical observation. -/
def Replacement.build {m : Type → Type} [Monad m] {Debug : Type}
    (replacement : Replacement) (classes : Builder m Debug)
    (left right : NodeId) (debug : Debug) : m NodeId :=
  match replacement with
  | .left => pure left
  | .right => pure right
  | .zero => classes.makeConstant 0 debug
  | .one => classes.makeConstant 1 debug
  | .max => classes.makeConstant (BitVec.allOnes 256) debug
  | .not_right => classes.makeOperation .NOT [right] debug
  | .neg_left => do
    let zero ← classes.makeConstant 0 debug
    classes.makeOperation .SUB [zero, left] debug
  | .neg_right => do
    let zero ← classes.makeConstant 0 debug
    classes.makeOperation .SUB [zero, right] debug
  | .iszero_left => classes.makeOperation .ISZERO [left] debug
  | .iszero_right => classes.makeOperation .ISZERO [right] debug
  | .bool_left => do
    let first ← classes.makeOperation .ISZERO [left] debug
    classes.makeOperation .ISZERO [first] debug
  | .bool_right => do
    let first ← classes.makeOperation .ISZERO [right] debug
    classes.makeOperation .ISZERO [first] debug

end Compiler.Algebraic
