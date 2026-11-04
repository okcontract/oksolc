/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.StorageOperations

namespace Compiler.Extraction.Storage.OperationTests
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

-- The sequence affects the value deliberately: a nested lookup must retain
-- observation identity even when opcode and operand IDs match.
def meaning : Meaning where
  operation := fun opcode sequence values =>
    if opcode = 1 then match values with
      | [a, b] => some (a + b + sequence.setWidth 256)
      | _ => none
    else none
  atom := fun kind value _ values => if kind = 2 ∧ values = [] then some value else none

def left : Cell := { item := ⟨2, none, 7⟩, otherValue := 99, itemAddress := 4 }
def right : Cell := { item := ⟨2, none, 2⟩, otherValue := 99, itemAddress := 8 }
def nested : Cell := {
  item := ⟨1, some 1, 0⟩, otherValue := 18, itemAddress := 12,
  arguments := [0, 1], sequence := 9, argumentsAddress := 16
}
def cells := [left, right, nested]

theorem coherent : Coherent meaning cells := by
  simp [Coherent, cells, left, right, nested, Item.eval, meaning, readArguments,
    readValue, Cell.value, Cell.isPush, Cell.dataValue]

example : operationProgram.run cells 2 1 = .ok (some ⟨16, [0, 1]⟩) := by rfl
example : operationProgram.run cells 2 3 = .ok none := by rfl
example : operationProgram.run cells 0 1 = .ok none := by rfl
example : operationProgram.run cells 3 1 = .ok none := by rfl
example : operationProgram.run [{ nested with item := ⟨1, none, 0⟩ }] 0 1 =
    .error .invalidOptional := by rfl
example : operationProgram.run [{ nested with item := ⟨2, none, 0⟩ }] 0 1 = .ok none := by rfl
example : operationProgram.run [{ nested with arguments := [] }] 0 1 = .ok (some ⟨16, []⟩) := by rfl
example : operationProgram.run (nodesAfter cells left { appended := true }) 2 1 =
    .ok (some ⟨16, [0, 1]⟩) := by rfl
example : operationProgram.run (nodesAfter cells left { appended := false }) 2 1 =
    .ok (some ⟨16, [0, 1]⟩) := by rfl

end Compiler.Extraction.Storage.OperationTests
