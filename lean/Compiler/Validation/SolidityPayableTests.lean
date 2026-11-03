/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityContract

/-! Independent expected frame observations for the payability extension.
Exact native-byte traces are exercised by the contract-artifact gate. -/
namespace Compiler.Validation.SolidityPayable.Tests
open Contract.Evm SolidityFunction SolidityCall

private def paid : Source :=
  { name := "f", parameters := [], body := .literal 7, payable := true }
private def rejected : Source := { paid with payable := false }
private def panic : Source :=
  { paid with checked := true, body := .binary .add (.literal (2^256 - 1)) (.literal 1) }

private theorem selector : paid.selector = 0x26121ff0 := by decide +kernel
private def input : Input := ⟨[0x26, 0x12, 0x1f, 0xf0], 13⟩
private def world : World :=
  { balances := fun address => if address = 1 then 100 else 9,
    storage := fun _ _ => 42, code := fun _ => [0x60, 0x07],
    nonces := fun _ => 3, other := fun _ => 11 }

private theorem accepted : Accepts paid input := by
  unfold Accepts AcceptsArguments
  rw [selector]
  decide

/-- Success debits the sender, credits the recipient and preserves the entire
remaining world, including unrelated accounts and contract storage/code. -/
theorem paid_success : observation paid input world ⟨1, 2⟩ 100 107 =
    ⟨.returned, Contract.Interaction.wordBytes 7,
      { world with balances := fun address =>
          if address = 1 then 87 else if address = 2 then 22 else 9 }, 7⟩ := by
  rw [observation, if_pos (by decide), outcome_accepts paid input accepted]
  change Observation.mk .returned _ (world.transfer 1 2 13) _ = _
  congr 1
  simp [World.transfer, world]
  funext address
  split <;> simp_all

/-- A self-call must not debit and then credit the same account twice. -/
theorem paid_self_call : observation paid input world ⟨2, 2⟩ 100 107 =
    ⟨.returned, Contract.Interaction.wordBytes 7, world, 7⟩ := by
  rw [observation, if_pos (by decide), outcome_accepts paid input accepted]
  rfl

theorem nonpayable_rollback : observation rejected input world ⟨1, 2⟩ 100 107 =
    ⟨.reverted, [], world, 7⟩ := by
  have invalid : ¬Accepts rejected input := by
    intro valid
    have := valid.1
    simp [AcceptsValue, rejected, input] at this
  rw [observation, if_pos (by decide), outcome_rejects rejected input invalid]

theorem panic_rolls_back_value : observation panic input world ⟨1, 2⟩ 100 107 =
    ⟨.reverted, Contract.panic 0x11, world, 7⟩ := by
  have valid : Accepts panic input := accepted
  rw [observation, if_pos (by decide), outcome_accepts panic input valid]
  rfl

theorem out_of_gas_rolls_back_value : observation paid input world ⟨1, 2⟩ 100 99 =
    ⟨.exceptional, [], world, 0⟩ := by
  simp [observation]

end Compiler.Validation.SolidityPayable.Tests
