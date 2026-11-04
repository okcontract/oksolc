/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.GraphInventory

namespace Compiler.Validation.Inventory.Tests
open Contract.Yul

def before : List Node := [.input "x", .literal 0, .binary .add 0 1]
def after : List Node := [.input "x", .literal 0]
def cache : List Entry := [⟨.input "x", 0⟩, ⟨.literal 0, 1⟩, ⟨.binary .add 0 1, 0⟩]

theorem complete (locals : String → Word) : Preserves before after [0, 1, 0] cache locals ∧
    ∃ value, evaluate before 2 locals = some value ∧ evaluate after 0 locals = some value :=
  certify 8 before after [0, 1, 0] cache 2 0 (by decide) (by decide) locals

theorem old_check_misses_unused_id : Compiler.Validation.validate 8 before after 2 0 = true := by decide
theorem wrong_unused_id : validate 8 before after [0, 0, 0] cache = false := by decide
theorem missing_id : validate 8 before after [0, 0] cache = false := by decide
theorem wrong_cache_value : validate 8 before after [0, 1, 0] [⟨.binary .add 0 1, 1⟩] = false := by decide
theorem wrong_cache_operand : validate 8 before after [0, 1, 0] [⟨.binary .add 0 0, 0⟩] = false := by decide
theorem invalid_cache_reference : validate 8 before after [0, 1, 0] [⟨.unary .bitnot 2, 0⟩] = false := by decide
theorem invalid_unused_representative : validate 8 before (after ++ [.unary .bitnot 2]) [0, 1, 0] cache = false := by decide
theorem duplicate_source_values : validate 8 [.input "x", .input "x"] [.input "x"] [0, 0] [] = true := by decide

end Compiler.Validation.Inventory.Tests
