/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityStorageDeployment

namespace Compiler.Validation.SolidityStorage.Tests
open Contract.Evm Contract.Interaction

attribute [local simp] Layout.words Layout.write Layout.read Layout.names
  Layout.locate Layout.locateFrom Location.allocate Variable.read

def abi : SolidityFunction.Source := { name := "f", parameters := [], body := .literal 0, checked := true }
def cells : Stateful.Slots := fun _ => 9
def overflow : SolidityWord.Expr := .binary .add (.literal (2^256 - 1)) (.literal 1)
def run (body : List Statement) (isStatic := false) :=
  Function.result (Layout.words ["cell"]) { abi := abi, body := body } ⟨[], 0⟩ cells isStatic

theorem return_skips_write_and_panic :
    run [.ret (.literal 7), .assign 0 overflow] true = .returned (wordBytes 7) cells := by
  simp +decide [run, Function.result, bodyResult, statements, statement, expression, abi, overflow,
    SolidityWord.Expr.evalChecked]

theorem untaken_arm_skipped :
    run [.branch (.compare .lt (.literal 1) (.literal 2)) [.ret (.literal 7)] [.assign 0 overflow]] true =
      .returned (wordBytes 7) cells := by
  simp +decide [run, Function.result, bodyResult, statements, statement, Condition.eval, expression, abi, overflow,
    SolidityWord.Expr.evalChecked]

theorem condition_panics_before_arms :
    run [.branch (.compare .eq overflow (.literal 0)) [.ret (.literal 1)] [.ret (.literal 2)]] =
      .reverted (Contract.panic 0x11) := by
  simp +decide [run, Function.result, bodyResult, statements, statement, Condition.eval, expression, abi, overflow,
    Comparison.test, SolidityWord.Expr.evalChecked, SolidityWord.Binary.evalChecked,
    Contract.CheckedOp.eval]
  rfl

theorem taken_static_write_faults :
    run [.branch (.compare .ge (.literal 1) (.literal 1)) [.assign 0 (.literal 7)] [], .ret (.input "cell")] true =
      .fault := by
  simp +decide [run, Function.result, bodyResult, statements, statement, Condition.eval, expression, abi,
    SolidityWord.Expr.evalChecked]

theorem rhs_panic_precedes_static_fault :
    run [.assign 0 overflow, .ret (.literal 0)] true = .reverted (Contract.panic 0x11) := by
  simp +decide [run, Function.result, bodyResult, statements, statement, expression, abi, overflow,
    SolidityWord.Expr.evalChecked, SolidityWord.Binary.evalChecked,
    Contract.CheckedOp.eval]
  rfl

theorem join_reads_written_value :
    run [.branch (.compare .ne (.literal 1) (.literal 2)) [.assign 0 (.literal 7)] [.assign 0 (.literal 8)],
         .ret (.input "cell")] = .returned (wordBytes 7) (Stateful.write cells 0 7) := by
  simp +decide [run, Function.result, bodyResult, statements, statement, Condition.eval, expression, abi,
    SolidityWord.Expr.evalChecked, locals, Stateful.write]

theorem return_preserves_prior_write :
    run [.assign 0 (.literal 7), .branch (.compare .le (.literal 2) (.literal 2)) [.ret (.input "cell")] [],
         .assign 0 (.literal 8), .ret (.input "cell")] = .returned (wordBytes 7) (Stateful.write cells 0 7) := by
  simp +decide [run, Function.result, bodyResult, statements, statement, Condition.eval, expression, abi,
    SolidityWord.Expr.evalChecked, locals, Stateful.write]

def panicCondition : Condition := .compare .eq overflow (.literal 0)

theorem short_circuit_skips_panic :
    (Condition.and (.literal false) panicCondition).eval (Layout.words ["cell"]) abi ⟨[], 0⟩ cells = .ok false ∧
    (Condition.or (.literal true) panicCondition).eval (Layout.words ["cell"]) abi ⟨[], 0⟩ cells = .ok true := by
  simp [Condition.eval]

theorem reached_operand_panics :
    (Condition.and (.literal true) panicCondition).eval (Layout.words ["cell"]) abi ⟨[], 0⟩ cells = .error (Contract.panic 0x11) ∧
    (Condition.or (.literal false) panicCondition).eval (Layout.words ["cell"]) abi ⟨[], 0⟩ cells = .error (Contract.panic 0x11) := by
  simp +decide [Condition.eval, panicCondition, expression, abi, overflow,
    SolidityWord.Expr.evalChecked, SolidityWord.Binary.evalChecked, Contract.CheckedOp.eval]
  rfl

theorem left_panic_is_not_masked :
    (Condition.and panicCondition (.literal false)).eval (Layout.words ["cell"]) abi ⟨[], 0⟩ cells = .error (Contract.panic 0x11) ∧
    (Condition.or panicCondition (.literal true)).eval (Layout.words ["cell"]) abi ⟨[], 0⟩ cells = .error (Contract.panic 0x11) := by
  simp +decide [Condition.eval, panicCondition, expression, abi, overflow,
    SolidityWord.Expr.evalChecked, SolidityWord.Binary.evalChecked, Contract.CheckedOp.eval]
  exact ⟨rfl, rfl⟩

theorem negated_short_circuit_skips_static_write :
    run [.branch (.not (.or (.literal true) panicCondition)) [.assign 0 overflow] [],
      .ret (.input "cell")] true = .returned (wordBytes 9) cells := by
  simp +decide [run, Function.result, bodyResult, statements, statement, Condition.eval, expression, abi,
    SolidityWord.Expr.evalChecked, locals, cells]

theorem condition_panic_discards_prior_write :
    run [.assign 0 (.literal 7), .branch (.and (.literal true) panicCondition) [] [],
      .ret (.input "cell")] = .reverted (Contract.panic 0x11) := by
  simp +decide [run, Function.result, bodyResult, statements, statement, Condition.eval, panicCondition,
    expression, abi, overflow, SolidityWord.Expr.evalChecked, SolidityWord.Binary.evalChecked,
    Contract.CheckedOp.eval]
  rfl

end Compiler.Validation.SolidityStorage.Tests
