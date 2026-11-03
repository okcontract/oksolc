/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AlternatingMaskProofs
import Compiler.Extraction.AddressMaskProofs
import Compiler.Extraction.SignExtendMaskProofs
import Compiler.Extraction.OppositeShiftsProofs
import Compiler.Extraction.ShiftMasksProofs
import Compiler.Extraction.BinaryLogarithmProofs
import Compiler.Extraction.FoldingProofs

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

inductive Version where
  | homestead | tangerineWhistle | spuriousDragon | byzantium | constantinople
  | petersburg | istanbul | berlin | london | paris | shanghai | cancun
  | prague | osaka | amsterdam | future
  deriving DecidableEq, Repr

structure Options where
  forYul : Bool := false
  evmVersion : Option Version := none
  deriving DecidableEq, Repr

/-- Native integer faults remain failures, never a missing rewrite. -/
def arithmetic {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m] (result : Except Folding.Fault α) : m α :=
  match result with
  | .ok value => pure value
  | .error _ => monadLift (Except.error (ε := Interner.Error) .safetyFault)

def addWord {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m] (left right : Word) : m Word := do
  return BitVec.ofNat 256 (← arithmetic (Folding.Zig.checkedAdd 256 left.toNat right.toNat))

def subWord {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m] (left right : Word) : m Word := do
  return BitVec.ofNat 256 (← arithmetic (Folding.Zig.checkedSub left.toNat right.toNat))

/-- A continuation is entered only on a normal miss. Intermediate heap changes
remain visible to it; errors and successful matches stop the ordered search. -/
def orNext {m : Type → Type} [Monad m] (stage next : m (Option NodeId)) : m (Option NodeId) := do
  let result ← stage
  match result with
  | some id => return some id
  | none => next

end Compiler.Extraction.Dispatch
