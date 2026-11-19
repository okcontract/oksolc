/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityStorageInitialization

namespace Compiler.Validation.SolidityStorage.Initialization.Tests
open Contract.Evm

def forward : List Initializer :=
  [(0, .binary .add (.input "second") (.literal 1)), (1, .literal 9)]

theorem declaration_order_and_zero_forward_reference :
    ((result (Layout.words ["first", "second"]) forward {}).toOption.map fun cells => [cells 0, cells 1, cells 2]) =
      some [1, 9, 0] := by decide

theorem reads_previous_initializer :
    ((result (Layout.words ["first", "second"]) [(0, .literal 7), (1, .input "first")] {}).toOption.map fun cells => cells 1) =
      some 7 := by decide

def fails : List Initializer := [(0, .literal 7), (1, .binary .sub (.input "second") (.literal 1))]

theorem arithmetic_panic :
    (match result (Layout.words ["first", "second"]) fails {} with
     | .error bytes => bytes = Contract.panic 0x11 | .ok _ => False) := by rfl

theorem value_rejection_precedes_initializers :
    (match result (Layout.words ["first", "second"]) fails { value := 1 } with
     | .error bytes => bytes = [] | .ok _ => False) := by rfl

def world : World := { balances := fun _ => 20 }
def transaction : Stateful.Transaction := { original := fun _ _ => 0, refund := 17 }
def ctx : Contract.Context := ⟨1, 2⟩
def changed : Stateful.Effects := ⟨.returned [0], Stateful.write (fun _ => 0) 0 7, fun _ => true, 42⟩

theorem gas_sentry_rolls_back :
    observation world transaction ctx {} (.finished 100 2301 changed) 2300 =
      ⟨⟨.exceptional, [], world, 0⟩, transaction⟩ := rfl

theorem deposit_failure_rolls_back :
    observation world transaction ctx {} (.finished 100 100 changed) 299 =
      ⟨⟨.exceptional, [], world, 0⟩, transaction⟩ := rfl

theorem initializer_revert_rolls_back :
    observation world transaction ctx {} (.finished 100 100 { changed with halt := .reverted (Contract.panic 0x11) }) 1000 =
      ⟨⟨.reverted, Contract.panic 0x11, world, 900⟩, transaction⟩ := rfl

def deployed := observation world transaction ctx {} (.finished 100 2301 changed) 2301

theorem successful_store_and_code : deployed.world.storage ctx.self 0 = 7 ∧
    deployed.world.code ctx.self = [0] ∧ deployed.world.nonces ctx.self = 1 ∧
    deployed.transaction.refund = 42 ∧ deployed.transaction.warm ctx.self 0 = true ∧
    deployed.gasRemaining = 2001 := by decide

theorem other_storage_unchanged (slot : Contract.Interaction.Word) :
    deployed.world.storage 3 slot = world.storage 3 slot := rfl

end Compiler.Validation.SolidityStorage.Initialization.Tests
