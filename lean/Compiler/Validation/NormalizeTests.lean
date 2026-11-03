/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.Normalize

namespace Compiler.Validation.NormalizeTests
open Contract.Yul

def x : Expression := .variable "x"
def y : Expression := .variable "y"

def forms (op : Binary) : Bool :=
  let inner := Expression.binary op x (.literal 3)
  let folded := Expression.binary op x (.literal (op.eval 3 5).toNat)
  let moved := Expression.binary op (.binary op x y) (.literal 3)
  let both := Expression.binary op (.binary op x y) (.literal (op.eval 3 5).toNat)
  equivalent 8 (.binary op inner (.literal 5)) folded &&
  equivalent 8 (.binary op (.literal 5) inner) folded &&
  equivalent 8 (.binary op inner y) moved &&
  equivalent 8 (.binary op y inner) moved &&
  equivalent 8 (.binary op inner (.binary op y (.literal 5))) both

theorem production_forms : [Binary.add, .mul, .and, .or, .xor].all forms = true := by decide

theorem subtraction_rejects : equivalent 8
    (.binary .sub (.binary .sub x (.literal 3)) (.literal 5))
    (.binary .sub x (.binary .sub (.literal 3) (.literal 5))) = false := by decide

theorem mixed_operators_reject : equivalent 8
    (.binary .mul (.binary .add x (.literal 3)) (.literal 5))
    (.binary .add x (.literal 15)) = false := by decide

theorem wrapped_sum : equivalent 8
    (.binary .add (.binary .add x (.literal (2^256-1))) (.literal 1)) x = true := by decide

theorem cancelled_xor : equivalent 8
    (.binary .xor (.binary .xor x (.literal 3)) (.literal 3)) x = true := by decide

theorem exhausted_fuel_rejects : equivalent 0
    (.binary .add (.binary .add x (.literal 3)) (.literal 5))
    (.binary .add x (.literal 8)) = false := by decide

end Compiler.Validation.NormalizeTests
