/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Validation.Graph

namespace Compiler.Validation.Tests

private def addZero : List Node := [.input "x", .literal 0, .binary .add 0 1]
private def x : List Node := [.input "x"]
private def zero : List Node := [.literal 0]

example : validate 4 addZero x 2 0 = true := by decide
example : validate 0 addZero x 2 0 = false := by decide
example : validate 4 addZero zero 2 0 = false := by decide
example : validate 4 [.input "x", .literal 0, .binary .add 0 1, .literal 1, .binary .mul 2 3]
    x 4 0 = true := by decide
example : validate 4 [.literal (2^256 - 1), .literal 1, .binary .add 0 1] zero 2 0 = true := by decide
example : validate 4 [.input "x", .input "x", .binary .sub 0 1] zero 2 0 = true := by decide
example : validate 4 [.input "x", .input "y", .binary .sub 0 1] zero 2 0 = false := by decide
example : validate 4 [.input "x", .input "y", .binary .add 0 1]
    [.input "y", .input "x", .binary .add 0 1] 2 2 = true := by decide
example : validate 4 [.input "x", .input "y", .binary .sub 0 1]
    [.input "y", .input "x", .binary .sub 0 1] 2 2 = false := by decide
example : validate 4 [.input "x", .unary .bitnot 0, .unary .bitnot 1] x 2 0 = true := by decide
example : validate 4 [.literal 0, .input "x", .binary .shl 0 1] x 2 0 = true := by decide
example : validate 4 [.input "x", .literal 0, .binary .shl 0 1] x 2 0 = false := by decide
example : validate 4 [.literal 256, .input "x", .binary .shl 0 1] zero 2 0 = true := by decide
example : validate 4 [.literal (2^256 - 1), .input "x", .binary .shr 0 1] zero 2 0 = true := by decide
example : validate 4 [.literal 255, .input "x", .binary .shl 0 1] zero 2 0 = false := by decide
-- The cutoff observes a 256-bit count, not an unbounded literal.
example : validate 4 [.literal (2^256), .input "x", .binary .shr 0 1] x 2 0 = true := by decide

-- Invalid references reject the entire graph, including unused nodes.
example : validate 4 [.unary .bitnot 0] [.unary .bitnot 0] 0 0 = false := by decide
example : validate 4 [.unary .bitnot 1, .unary .bitnot 0] x 0 0 = false := by decide
example : validate 4 [.input "x", .binary .add 0 7] x 0 0 = false := by decide
example : validate 4 x x 1 1 = false := by decide
example : validate 4 [] [] 0 0 = false := by decide

end Compiler.Validation.Tests
