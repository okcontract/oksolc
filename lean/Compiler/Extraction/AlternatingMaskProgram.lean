/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AlternatingMask

namespace Compiler.Extraction.AlternatingMask
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Interner Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
def andOpcode : Opcode := 22
def orOpcode : Opcode := 23

def choices : List Choice :=
  [⟨false, false, false⟩, ⟨false, false, true⟩,
   ⟨false, true, false⟩, ⟨false, true, true⟩,
   ⟨true, false, false⟩, ⟨true, false, true⟩,
   ⟨true, true, false⟩, ⟨true, true, true⟩]

def matchCandidate (reads : Reads) (choice : Choice) (outerLeft outerRight : NodeId) :
    Except ReadError (Option Capture) := do
  let secondId := pick choice.outerSecond outerLeft outerRight
  let outerMaskId := pick choice.outerSecond outerRight outerLeft
  let some outerMask ← reads.constant outerMaskId | return none
  let some alternatives ← reads.operation secondId orOpcode | return none
  let [altLeft, altRight] := alternatives.items | return none
  let some inner ← reads.operation (pick choice.innerSecond altLeft altRight) andOpcode | return none
  let [innerLeft, innerRight] := inner.items | return none
  let some innerMask ← reads.constant (pick choice.constantFirst innerRight innerLeft) | return none
  return some ⟨pick choice.constantFirst innerLeft innerRight,
    pick choice.innerSecond altRight altLeft, outerMaskId, innerMask, outerMask,
    inner, alternatives, if choice.constantFirst then 1 else 0, if choice.innerSecond then 0 else 1⟩

@[reducible] def buildCandidateWithInputs (constructors : Constructors Debug m) (capture : Capture) (debug : Debug) (operand : OperandRead m := logicalOperand) : m NodeId := do
  let expression ← operand capture.inner capture.expressionIndex capture.expression
  let constant ← constructors.constant (capture.innerMask &&& capture.outerMask) debug
  let left ← constructors.operation andOpcode [expression, constant] debug
  let materialized ← constructors.materialize capture.outerMaskId capture.outerMask debug
  let right ← constructors.operation andOpcode [← operand capture.alternatives capture.otherIndex capture.otherExpression, materialized] debug
  ConstructorPair.scalars constructors orOpcode left right debug


/-- Logical projection of the same source body. -/
def buildCandidate (constructors : Constructors Debug m) (capture : Capture) (debug : Debug) : m NodeId :=
  buildCandidateWithInputs constructors capture debug

@[reducible] def searchWithInputs (reads : Reads) (constructors : Constructors Debug m) (outerLeft outerRight : NodeId)
    (debug : Debug) (candidates : List Choice) (operand : OperandRead m := logicalOperand)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) :=
  match candidates with
  | [] => pure none
  | choice :: rest => do
    let some capture ← query (fun reads => matchCandidate reads choice outerLeft outerRight) |
      searchWithInputs reads constructors outerLeft outerRight debug rest operand query
    return some (← buildCandidateWithInputs constructors capture debug operand)


/-- Logical projection of the same source body. -/
def search (reads : Reads) (constructors : Constructors Debug m) (outerLeft outerRight : NodeId)
    (debug : Debug) (candidates : List Choice) : m (Option NodeId) :=
  searchWithInputs reads constructors outerLeft outerRight debug candidates

@[reducible] def distributeAlternatingMaskWithInputs (reads : Reads) (constructors : Constructors Debug m)
    (outerLeft outerRight : NodeId) (debug : Debug)
    (operand : OperandRead m := logicalOperand)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) :=
  searchWithInputs reads constructors outerLeft outerRight debug choices operand query


/-- Logical projection of the same source body. -/
def distributeAlternatingMask (reads : Reads) (constructors : Constructors Debug m)
    (outerLeft outerRight : NodeId) (debug : Debug) : m (Option NodeId) :=
  distributeAlternatingMaskWithInputs reads constructors outerLeft outerRight debug

end Compiler.Extraction.AlternatingMask
