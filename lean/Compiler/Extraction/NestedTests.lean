/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.NestedProofs

namespace Compiler.Extraction.Nested.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul

def fallback : Meaning where
  operation := fun _ _ _ => none
  atom := fun kind value _ arguments => if kind = 2 ∧ arguments = [] then some value else none

def literal (value : Word) : Cell := { item := ⟨2, none, value⟩, otherValue := 99, itemAddress := 0 }
def operation (opcode : Opcode) (arguments : List NodeId) (value : Word) : Cell := {
  item := ⟨1, some opcode, 0⟩, arguments, otherValue := value, itemAddress := 0
}
def cells := [literal 7, literal 2, operation 24 [0, 1] 5,
  operation 22 [0, 1] 2, operation 23 [0, 1] 7, operation 25 [0] (~~~7), literal 0]

theorem coherent : Coherent (Folding.wordMeaning fallback) cells := by
  simp [Coherent, cells, literal, operation, Item.eval, readArguments, readValue,
    Cell.value, Cell.isPush, Cell.dataValue, Folding.wordMeaning, Folding.decodeWord,
    Folding.wordOperations, Folding.Op.opcode, Folding.Op.eval, Folding.Op.arity,
    Folding.Op.value, Binary.eval, Unary.eval, fallback]

example : cancelNestedBinary (storageReads cells) 24 0 2 = .ok (some 1) := by rfl
example : cancelNestedBinary (storageReads cells) 24 1 2 = .ok (some 0) := by rfl
example : cancelNestedBinary (storageReads cells) 24 6 2 = .ok none := by rfl
example : cancelNestedBinary (storageReads cells) 24 0 99 = .ok none := by rfl
example : absorbedOccurrence (storageReads cells) 0 3 22 = .ok (some 0) := by rfl
example : absorbedOccurrence (storageReads cells) 1 4 23 = .ok (some 1) := by rfl
example : absorbedOccurrence (storageReads cells) 6 3 22 = .ok none := by rfl
example : isNegation (storageReads cells) 0 5 = .ok true := by rfl
example : isNegation (storageReads cells) 1 5 = .ok false := by rfl
example : splitConstant (storageReads cells) [0, 1] = .ok (some ⟨0, 1, 2⟩) := by rfl
example : splitConstant (storageReads cells) [1, 0] = .ok (some ⟨1, 0, 7⟩) := by rfl
example : splitConstant (storageReads cells) [1, 6] = .ok (some ⟨1, 6, 0⟩) := by rfl
example : splitConstant (storageReads cells) [0, 5] = .ok (some ⟨5, 0, 7⟩) := by rfl
example : splitConstant (storageReads cells) [2, 5] = .ok none := by rfl
example : splitConstant (storageReads cells) [0] = .ok none := by rfl
example : splitConstant (storageReads cells) [0, 1, 6] = .ok none := by rfl
example : cancelNestedBinary (storageReads [operation 24 [0] 0]) 24 0 0 = .ok none := by rfl
example : isNegation (storageReads [operation 25 [0, 1] 0]) 0 0 = .ok false := by rfl

-- Behavior of the polymorphic equality branch; soundness additionally requires
-- Sound.equal, and this deliberately indiscriminate predicate has no such proof.
def indiscriminate : Reads := { storageReads cells with overrideEquality := some (fun _ _ => true) }
example : cancelNestedBinary indiscriminate 24 6 2 = .ok (some 1) := by rfl
example : absorbedOccurrence indiscriminate 6 3 22 = .ok (some 0) := by rfl

def corrupt : List Cell := [{ item := ⟨1, none, 0⟩, otherValue := 0, itemAddress := 0 }]
example : isNegation (storageReads corrupt) 0 0 = .error .invalidOptional := by rfl
example : cancelNestedBinary (storageReads corrupt) 24 0 0 = .error .invalidOptional := by rfl
example : absorbedOccurrence (storageReads corrupt) 0 0 22 = .error .invalidOptional := by rfl

end Compiler.Extraction.Nested.Tests
