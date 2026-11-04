/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityStorageConstructor
import Compiler.Validation.SolidityStorageInitializationTests

namespace Compiler.Validation.SolidityStorage.Constructor.Tests
open Contract.Evm
open Contract.Interaction (Word)

attribute [local simp] Layout.words Layout.write Layout.read Layout.names
  Layout.locate Layout.locateFrom Location.allocate Variable.read

def observe : Outcome → Option (List Word)
  | .returned _ cells => some [cells 0, cells 1, cells 2]
  | _ => none

def sequential : Body := ⟨[.assign 1 (.binary .add (.input "first") (.literal 1)),
  .assign 0 (.input "second")], true, false⟩

theorem initializers_before_body :
    observe (result (Layout.words ["first", "second"]) [(0, .literal 7)] sequential {}) = some [8, 8, 0] := by
  simp +decide [result, statements, statement, expression, Initialization.evaluate,
    SolidityWord.Expr.evalChecked, SolidityWord.Binary.evalChecked, Contract.CheckedOp.eval, locals, observe, sequential]

def early : Body := ⟨[.assign 0 (.literal 9), .ret (.literal 0), .assign 1 (.literal 42)], true, false⟩

theorem return_stops_without_abi_bytes :
    (match result (Layout.words ["first", "second"]) [] early {} with
     | .returned bytes cells => bytes = [] ∧ cells 0 = 9 ∧ cells 1 = 0 | _ => False) := by
  simp +decide [result, statements, statement, expression, Initialization.evaluate,
    SolidityWord.Expr.evalChecked, early]

def branch : Body := ⟨[.branch (.compare .eq (.input "cell") (.literal 7))
  [.assign 0 (.literal 8)] [.assign 0 (.literal 9)]], true, false⟩

theorem branch_reads_initialized_store :
    observe (result (Layout.words ["cell"]) [(0, .literal 7)] branch {}) = some [8, 0, 0] := by
  simp +decide [result, statements, statement, Condition.eval, expression, Initialization.evaluate,
    SolidityWord.Expr.evalChecked, locals, Comparison.test, observe, branch]

def underflow : Body := ⟨[.assign 0 (.binary .sub (.input "cell") (.literal 1))], true, false⟩

theorem checked_body_panics :
    (match result (Layout.words ["cell"]) [] underflow {} with
     | .reverted bytes => bytes = Contract.panic 0x11 | _ => False) := by
  simp +decide [result, statements, statement, expression, Initialization.evaluate,
    SolidityWord.Expr.evalChecked, SolidityWord.Binary.evalChecked, Contract.CheckedOp.eval, locals, underflow]
  rfl

theorem unchecked_body_wraps :
    observe (result (Layout.words ["cell"]) [] { underflow with checked := false } {}) = some [-1, 0, 0] := by
  simp +decide [result, statements, statement, expression, Initialization.evaluate,
    SolidityWord.Expr.eval, SolidityWord.Binary.eval, locals, observe, underflow]

theorem unchecked_body_does_not_change_initializer_mode :
    (match result (Layout.words ["cell"]) [(0, .binary .sub (.literal 0) (.literal 1))]
       { underflow with checked := false } {} with
     | .reverted bytes => bytes = Contract.panic 0x11 | _ => False) := rfl

theorem nonpayable_before_initialization :
    (match result (Layout.words ["cell"]) [(0, .binary .sub (.literal 0) (.literal 1))] underflow { value := 1 } with
     | .reverted bytes => bytes = [] | _ => False) := rfl

theorem payable_accepts_value :
    observe (result (Layout.words ["cell"]) [] { branch with payable := true } { value := 1 }) = some [9, 0, 0] := by
  simp +decide [result, statements, statement, Condition.eval, expression, Initialization.evaluate,
    SolidityWord.Expr.evalChecked, locals, observe, branch]

theorem payable_does_not_hide_panic :
    (match result (Layout.words ["cell"]) [] { underflow with payable := true } { value := 1 } with
     | .reverted bytes => bytes = Contract.panic 0x11 | _ => False) := by
  simp +decide [result, statements, statement, expression, Initialization.evaluate,
    SolidityWord.Expr.evalChecked, SolidityWord.Binary.evalChecked, Contract.CheckedOp.eval, locals, underflow]
  rfl

theorem source_fault_stays_fault : Creation.expected [0] .fault = .fault := rfl

end Compiler.Validation.SolidityStorage.Constructor.Tests
