/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Interaction.Basic

namespace Contract.Interaction.WordPower

/-- Squaring keeps every intermediate a word. A word exponent needs at most
256 recursive steps; neither the full natural power nor a linear-length
`BitVec.pow` computation is materialized. -/
def pow (base : Word) (exponent : Nat) : Word :=
  if _zero : exponent = 0 then 1 else
    let half := pow (base * base) (exponent / 2)
    if exponent % 2 = 0 then half else base * half
termination_by exponent
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero _zero) (by decide)

@[simp] theorem pow_zero (base : Word) : pow base 0 = 1 := by rw [pow]; simp

/-- The mathematical EVM result, without evaluating the huge power in the
executable model. This is a word-operation fact, not an exporter proof. -/
theorem toNat_pow (base : Word) (exponent : Nat) :
    (pow base exponent).toNat = base.toNat ^ exponent % 2^256 := by
  induction exponent using Nat.strongRecOn generalizing base with
  | ind exponent ih =>
    rw [pow]
    split
    · rename_i zero
      subst exponent
      simp
    · rename_i nonzero
      have smaller : exponent / 2 < exponent := Nat.div_lt_self (Nat.pos_of_ne_zero nonzero) (by decide)
      have half := ih (exponent / 2) smaller (base * base)
      have squared : ((base * base).toNat) ^ (exponent / 2) % 2^256 =
          base.toNat ^ (2 * (exponent / 2)) % 2^256 := by
        rw [BitVec.toNat_mul, ← Nat.pow_mod, ← Nat.pow_two, ← Nat.pow_mul]
      rw [squared] at half
      split
      · rename_i even
        rw [half]
        congr 2
        omega
      · rename_i odd
        rw [BitVec.toNat_mul, half, Nat.mul_mod_mod, ← Nat.pow_add_one']
        congr 2
        have remainder := Nat.mod_lt exponent (by decide : 0 < 2)
        omega

end Contract.Interaction.WordPower
