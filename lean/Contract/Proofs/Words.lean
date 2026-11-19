/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Semantics.Eval

/-! Mathematical specifications of the unsigned EVM primitives used by the
printer. This checks primitive equations/guards, not whole-program lowering. -/
namespace Contract.WordProofs

def evm (op : WordOp) (a b : Nat) : Nat := match op with
  | .mul => a * b % 2^256
  | .div => a / b
  | .mod => if b = 0 then 0 else a % b
  | .and => a &&& b
  | .or => a ||| b
  | .xor => a ^^^ b
  | .shl => if b < 256 then (a <<< b) % 2^256 else 0
  | .shr => if b < 256 then a >>> b else 0

theorem primitive (op : WordOp) (a b : BitVec 256) :
    (op.eval a b).toNat = evm op a.toNat b.toNat := by
  cases op <;> simp [WordOp.eval, evm, BitVec.toNat_udiv]
  · split <;> rename_i h
    · simp_all
    · have h' : b.toNat ≠ 0 := by intro hz; apply h; exact BitVec.eq_of_toNat_eq hz
      simp [h']
  · split <;> simp_all
  · split <;> simp_all

theorem add_guard (a b : BitVec 256) :
    a + b < a ↔ 2^256 ≤ a.toNat + b.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.lt_def, BitVec.toNat_add]
  omega

theorem complement (a : BitVec 256) : (~~~a).toNat = 2^256 - 1 - a.toNat := BitVec.toNat_not

theorem comparison (a b : BitVec 256) :
    a.ult b = decide (a.toNat < b.toNat) ∧ a.ule b = decide (a.toNat ≤ b.toNat) := ⟨rfl, rfl⟩

theorem mul_guard (a b : BitVec 256) :
    (a.toNat ≠ 0 ∧ (2^256 - 1) / a.toNat < b.toNat) ↔ 2^256 ≤ a.toNat * b.toNat := by
  by_cases ha : a.toNat = 0
  · simp [ha]
  · have positive : 0 < a.toNat := by omega
    simp only [Nat.div_lt_iff_lt_mul positive]
    rw [Nat.mul_comm b.toNat a.toNat]
    omega

/-- The original V2 multiplication guard accepts exactly nonoverflowing
products (including either zero operand). -/
theorem multiplication_guard_exact (a b : BitVec 256) :
    (b = 0 ∨ (a*b)/b = a) ↔ a.toNat*b.toNat < 2^256 := by
  constructor
  · intro h
    rcases h with hb | hq
    · simp [hb]
    · have bound := Nat.div_mul_le_self (a*b).toNat b.toNat
      have eqn : (a*b).toNat / b.toNat = a.toNat := by
        simpa only [BitVec.toNat_udiv] using congrArg BitVec.toNat hq
      rw [eqn] at bound
      exact Nat.lt_of_le_of_lt bound (a*b).isLt
  · intro h
    by_cases hb : b = 0
    · exact Or.inl hb
    · right
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_udiv, BitVec.toNat_mul_of_lt h]
      have hp : 0 < b.toNat := by
        have : b.toNat ≠ 0 := by intro z; apply hb; exact BitVec.eq_of_toNat_eq z
        omega
      exact Nat.mul_div_left _ hp

theorem subtraction_guard_exact (a b : BitVec 256) :
    (a-b ≤ a) ↔ b ≤ a := by
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.le_def, BitVec.toNat_sub]
  omega

theorem checked_add_exact (a b : BitVec 256) (h : a.toNat + b.toNat < 2^256) :
    CheckedOp.eval .add a b = .ok (a + b) ∧ (a + b).toNat = a.toNat + b.toNat := by
  exact ⟨by simp [CheckedOp.eval, h], BitVec.toNat_add_of_lt h⟩

theorem checked_mul_exact (a b : BitVec 256) (h : a.toNat * b.toNat < 2^256) :
    CheckedOp.eval .mul a b = .ok (a * b) ∧ (a * b).toNat = a.toNat * b.toNat := by
  exact ⟨by simp [CheckedOp.eval, h], BitVec.toNat_mul_of_lt h⟩

theorem checked_sub_exact (a b : BitVec 256) (h : b ≤ a) :
    CheckedOp.eval .sub a b = .ok (a - b) ∧ (a - b).toNat = a.toNat - b.toNat := by
  exact ⟨by simp [CheckedOp.eval, h], BitVec.toNat_sub_of_le h⟩

theorem failed_assert_rolls_back (before : Storage slots) (ctx : Context) (env : Env vars)
    (slot : Fin slots) (value : Expr slots vars .word) (next : Stmt slots returns vars) :
    (Stmt.store slot value (.assert_ (.bool false) next)).eval before ctx env =
      .revert (panic 1) := rfl

/-- One requested primitive property permits fresh-kernel replay of every
operation and the exact overflow guards used by the printer. -/
def Correct : Prop :=
  (∀ op a b, (op.eval a b).toNat = evm op a.toNat b.toNat) ∧
  (∀ a b : BitVec 256, a + b < a ↔ 2^256 ≤ a.toNat + b.toNat) ∧
  (∀ a b : BitVec 256, (a.toNat ≠ 0 ∧ (2^256 - 1) / a.toNat < b.toNat) ↔
    2^256 ≤ a.toNat * b.toNat) ∧
  (∀ a : BitVec 256, (~~~a).toNat = 2^256 - 1 - a.toNat) ∧
  (∀ a b : BitVec 256, a.ult b = decide (a.toNat < b.toNat) ∧ a.ule b = decide (a.toNat ≤ b.toNat))

theorem correct : Correct := ⟨primitive, add_guard, mul_guard, complement, comparison⟩

end Contract.WordProofs
