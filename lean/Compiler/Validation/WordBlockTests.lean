/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Validation.SolidityWord

namespace Compiler.Validation.WordBlock.Tests
open Contract.Yul

example : decode [0x61, 0x01, 0x02] = some (.push 258, 3, []) := by decide
example : decode [0x5f] = some (.push 0, 2, []) := by decide
example : decode [0x60, 0] = some (.push 0, 3, []) := by decide
example : decode [0x61, 0x01] = none := by decide
example : decode [0x54] = none := by decide
example : decode [0x56] = none := by decide
example : decode [0x90] = none := by decide
example : execute [0x81] [7] = none := by decide
example : execute [0x01] [7] = none := by decide
example : execute [0x15] [] = none := by decide
example (stack : List Word) (full : stack.length = 1024) : execute [0x5f] stack = none := by
  unfold execute
  rw [run.eq_def]
  simp only [full, Nat.lt_irrefl, ↓reduceIte]
  change (run wordAlgebra 0 [] (0 :: stack)).bind _ = none
  rw [run.eq_def]
  simp [full]
example (stack : List Word) (over : 1024 < stack.length) : execute [] stack = none := by
  unfold execute
  rw [run.eq_def]
  simp [over]
example : execute [0x61, 0x01, 0x02] [] = some (3, [258]) := by decide
example : execute [0x04] [7, 0] = some (5, [0]) := by decide
example : execute [0x06] [7, 0] = some (5, [0]) := by decide
example : metered [0x5f] [] 2 = some (0, [0]) := by decide
example : metered [0x5f] [] 1 = none := by decide
example : validate 8 [0x80] ["x"] (.variable "x") = true := by decide
example : validate 8 [0x80] ["x"] (.literal 0) = false := by decide
example : validate 8 [0x5f] ["x"] (.variable "x") = false := by decide
-- ADD alone destroys the input frame even when its result is correct.
example : validate 8 [0x01] ["x", "y"] (.binary .add (.variable "x") (.variable "y")) = false := by decide
example : validate 8 [0x81, 0x81, 0x03] ["x", "y"]
    (.binary .sub (.variable "x") (.variable "y")) = true := by decide
example : validate 8 [0x80, 0x82, 0x03] ["x", "y"]
    (.binary .sub (.variable "x") (.variable "y")) = false := by decide
example : validate 8 [0x80, 0x82, 0x1b] ["x", "y"]
    (SolidityWord.Expr.binary .shl (.input "x") (.input "y")).lower = true := by decide
example : validate 8 [0x81, 0x81, 0x1b] ["x", "y"]
    (SolidityWord.Expr.binary .shl (.input "x") (.input "y")).lower = false := by decide
example : execute [0x1b] [256, 7] = some (3, [0]) := by decide
example : execute [0x1c] [256, 7] = some (3, [0]) := by decide
example : run expressions 0 [0x80] [.variable "x"] = none := by decide
example : (SolidityWord.Expr.binary .add (.literal (2^256 - 1)) (.literal 1)).eval (fun _ => 0) = 0 := by decide

end Compiler.Validation.WordBlock.Tests
