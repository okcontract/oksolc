/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.Scalar
import Init.Data.Nat.Bitwise.Lemmas

/-! Unsigned AIR bit operations. These laws cover mathematical results and
their range, including the parity and strict-decrease facts used by exp256.
They do not establish source-to-AIR or native-backend preservation. -/
namespace Compiler.ZigAir.Scalar

theorem unsigned_nat_valid (x n : Nat) (bound : x < 2 ^ n) :
    (Value.int false n x).valid = true := by
  simp only [Value.valid, Ty.contains, Ty.lower, Ty.upper, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg x, by exact_mod_cast bound⟩

theorem bitAnd_eval (left right : Ref) (args : List Value) (env : Env) (x y n : Nat)
    (hx : left.eval env = .ok (.int false n x))
    (hy : right.eval env = .ok (.int false n y)) :
    (Prim.bitAnd left right).eval args env = .ok (.int false n (x &&& y)) := by
  simp [Prim.eval, hx, hy, bind, Except.bind]

theorem bitAnd_valid (x y n : Nat) (bound : y < 2 ^ n) :
    (Value.int false n (x &&& y)).valid = true :=
  unsigned_nat_valid _ _ (Nat.and_lt_two_pow x bound)

theorem shiftRight_eval (left right : Ref) (args : List Value) (env : Env) (x k n : Nat)
    (hx : left.eval env = .ok (.int false n x))
    (hk : right.eval env = .ok (.int false (shiftCountWidth n) k))
    (bound : k < n) :
    (Prim.shiftRight left right).eval args env = .ok (.int false n (x >>> k)) := by
  have positive : n ≠ 0 := by omega
  simp [Prim.eval, hx, hk, bind, Except.bind, positive, bound]

theorem shiftRight_valid (x k n : Nat) (bound : x < 2 ^ n) :
    (Value.int false n (x >>> k)).valid = true :=
  unsigned_nat_valid _ _ (Nat.lt_of_le_of_lt (Nat.shiftRight_le x k) bound)

theorem bitAnd_one (x : Nat) : x &&& 1 = x % 2 := Nat.and_one_is_mod x

theorem shiftRight_one (x : Nat) : x >>> 1 = x / 2 := by
  simp [Nat.shiftRight_eq_div_pow]

theorem shiftRight_one_decreases (x : Nat) (positive : 0 < x) : x >>> 1 < x := by
  rw [shiftRight_one]
  exact Nat.div_lt_self positive (by decide)

theorem exponent_decomposition (x : Nat) : (x &&& 1) + 2 * (x >>> 1) = x := by
  rw [bitAnd_one, shiftRight_one]
  exact Nat.mod_add_div x 2

end Compiler.ZigAir.Scalar
