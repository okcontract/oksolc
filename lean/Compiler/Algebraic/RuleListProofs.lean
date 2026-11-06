/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Algebraic.Proofs

/-! Kernel-checked soundness theorems for the procedural rewrite families in
`src/libevmasm/rule_list.zig` beyond the 50-entry `productionRules` table:
byte/mask rules, boolean/comparison/ISZERO/NOT chains, XOR/AND/OR cancellations
and absorptions, SIGNEXTEND compositions and masks, environmental 160-bit address
masks, associative/subtractive constant motion, same-direction and opposite
shifts, shift-mask distributivity and coverage, power-of-two MUL/DIV/MOD/SHL/SHR
identities, and EVM `EXP` base rules (`0`, `1`, `2`, `2^256 - 1`). -/
namespace Compiler.Algebraic.RuleList
open Contract
open Contract.Yul

private theorem one_shiftLeft_toNat (k : Nat) (hk : k < 256) :
    (1#256 <<< k).toNat = 2 ^ k := by
  rw [BitVec.toNat_shiftLeft]
  have h1 : (1#256).toNat = 1 := rfl
  rw [h1, Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega : 1 < 2) hk)

private theorem one_shiftLeft_ne_zero (k : Nat) (hk : k < 256) :
    (1#256 <<< k) ≠ 0#256 := by
  intro hz
  have h := congrArg BitVec.toNat hz
  rw [one_shiftLeft_toNat k hk] at h
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h0 : (0#256).toNat = 0 := rfl
  omega

private theorem low_mask_getLsbD (k : Nat) (hk : k < 256) (i : Nat) (hi : i < 256) :
    ((1#256 <<< k) - 1#256).getLsbD i = decide (i < k) := by
  have hpow : ((1#256 <<< k) - 1#256).toNat = 2 ^ k - 1 := by
    rw [BitVec.toNat_sub_of_le]
    · rw [one_shiftLeft_toNat k hk]; rfl
    · rw [BitVec.le_def, one_shiftLeft_toNat k hk]
      exact Nat.one_le_two_pow
  rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat, hpow, Nat.testBit_two_pow_sub_one]

/-! ## Part 2 & Part 5: `BYTE` / `SIGNEXTEND` / `SHL` / `SHR` boundary & mask rules -/

theorem and_byte_mask (i x : Word) :
    Binary.and.eval (Binary.byte.eval i x) 0xff#256 = Binary.byte.eval i x := by
  simp only [Binary.eval, evmByte]
  split
  · apply BitVec.eq_of_getLsbD_eq
    intro k _
    simp only [BitVec.getLsbD_and, Bool.and_assoc, Bool.and_self]
  · rfl

theorem byte_31_eq_and (x : Word) :
    Binary.byte.eval 31#256 x = Binary.and.eval x 0xff#256 := by
  simp [Binary.eval, evmByte]

theorem shl_ge_256 (s x : Word) (h : 256 ≤ s.toNat) :
    Binary.shl.eval s x = 0#256 := by
  simp only [Binary.eval, evmShl]
  have hnlt : ¬(s.ult 256#256 = true) := by
    simp [BitVec.ult]; omega
  simp [hnlt]

theorem shr_ge_256 (s x : Word) (h : 256 ≤ s.toNat) :
    Binary.shr.eval s x = 0#256 := by
  simp only [Binary.eval, evmShr]
  have hnlt : ¬(s.ult 256#256 = true) := by
    simp [BitVec.ult]; omega
  simp [hnlt]

theorem byte_ge_32 (i x : Word) (h : 32 ≤ i.toNat) :
    Binary.byte.eval i x = 0#256 := by
  simp only [Binary.eval, evmByte]
  have hnlt : ¬(i.ult 32#256 = true) := by
    simp [BitVec.ult]; omega
  simp [hnlt]

theorem signextend_ge_31 (b x : Word) (h : 31 ≤ b.toNat) :
    Binary.signextend.eval b x = x := by
  simp only [Binary.eval, evmSignextend]
  have hnlt : ¬(b.ult 31#256 = true) := by
    simp [BitVec.ult]; omega
  simp [hnlt]

/-! ## Part 4 & Part 6: Boolean, bitwise, cancellation, absorption, and `ISZERO` chains -/

theorem xor_cancel_left (a b : Word) :
    Binary.xor.eval a (Binary.xor.eval a b) = b := by
  change a ^^^ (a ^^^ b) = b
  rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem xor_cancel_right (a b : Word) :
    Binary.xor.eval a (Binary.xor.eval b a) = b := by
  change a ^^^ (b ^^^ a) = b
  rw [BitVec.xor_comm b a, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem add_sub_cancel_left (a b : Word) :
    Binary.sub.eval (Binary.add.eval a b) a = b := by
  change (a + b) - a = b
  rw [BitVec.add_comm a b, BitVec.add_sub_cancel]

theorem add_sub_cancel_right (a b : Word) :
    Binary.sub.eval (Binary.add.eval a b) b = a := by
  change (a + b) - b = a
  exact BitVec.add_sub_cancel a b

theorem sub_add_cancel_left (a b : Word) :
    Binary.add.eval (Binary.sub.eval a b) b = a := by
  change (a - b) + b = a
  exact BitVec.sub_add_cancel a b

theorem sub_add_cancel_right (a b : Word) :
    Binary.add.eval b (Binary.sub.eval a b) = a := by
  change b + (a - b) = a
  rw [BitVec.add_comm, BitVec.sub_add_cancel]

theorem sub_sub_cancel (a b : Word) :
    Binary.sub.eval a (Binary.sub.eval a b) = b := by
  change a - (a - b) = b
  rw [BitVec.sub_eq_add_neg a (a - b), BitVec.neg_sub, ← BitVec.add_assoc,
    ← BitVec.sub_eq_add_neg a a, BitVec.sub_self, BitVec.zero_add]

theorem not_add_one_eq_neg (a : Word) :
    Binary.add.eval (Unary.bitnot.eval a) 1#256 = Binary.sub.eval 0#256 a ∧
    Binary.add.eval 1#256 (Unary.bitnot.eval a) = Binary.sub.eval 0#256 a := by
  have h : ~~~a + 1#256 = 0#256 - a := by
    rw [BitVec.zero_sub, BitVec.neg_eq_not_add]
  exact ⟨h, (BitVec.add_comm 1#256 (~~~a)).trans h⟩

theorem demorgan_not_or (a b : Word) :
    Binary.and.eval (Unary.bitnot.eval a) (Unary.bitnot.eval b) =
      Unary.bitnot.eval (Binary.or.eval a b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Binary.eval, Unary.eval, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem demorgan_not_and (a b : Word) :
    Binary.or.eval (Unary.bitnot.eval a) (Unary.bitnot.eval b) =
      Unary.bitnot.eval (Binary.and.eval a b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Binary.eval, Unary.eval, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem or_absorb_and_left (a b : Word) :
    Binary.or.eval a (Binary.and.eval a b) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [Binary.eval, BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem or_absorb_and_right (a b : Word) :
    Binary.or.eval a (Binary.and.eval b a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [Binary.eval, BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem and_absorb_or_left (a b : Word) :
    Binary.and.eval a (Binary.or.eval a b) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [Binary.eval, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem and_absorb_or_right (a b : Word) :
    Binary.and.eval a (Binary.or.eval b a) = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [Binary.eval, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl

theorem or_complement (a : Word) :
    Binary.or.eval a (Unary.bitnot.eval a) = BitVec.allOnes 256 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Binary.eval, Unary.eval, BitVec.getLsbD_or, BitVec.getLsbD_not, hi,
    BitVec.getLsbD_allOnes]
  cases a.getLsbD i <;> rfl

theorem and_complement (a : Word) :
    Binary.and.eval a (Unary.bitnot.eval a) = 0#256 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [Binary.eval, Unary.eval, BitVec.getLsbD_and, BitVec.getLsbD_not, hi,
    BitVec.getLsbD_zero]
  cases a.getLsbD i <;> rfl

theorem and_drop_repeated_right (a b : Word) :
    Binary.and.eval (Binary.and.eval a b) b = Binary.and.eval a b := by
  change (a &&& b) &&& b = a &&& b
  rw [BitVec.and_assoc, BitVec.and_self]

theorem and_drop_repeated_left (a b : Word) :
    Binary.and.eval (Binary.and.eval a b) a = Binary.and.eval a b := by
  change (a &&& b) &&& a = a &&& b
  rw [BitVec.and_comm (a &&& b) a, ← BitVec.and_assoc, BitVec.and_self]

theorem or_drop_repeated_right (a b : Word) :
    Binary.or.eval (Binary.or.eval a b) b = Binary.or.eval a b := by
  change (a ||| b) ||| b = a ||| b
  rw [BitVec.or_assoc, BitVec.or_self]

theorem or_drop_repeated_left (a b : Word) :
    Binary.or.eval (Binary.or.eval a b) a = Binary.or.eval a b := by
  change (a ||| b) ||| a = a ||| b
  rw [BitVec.or_comm (a ||| b) a, ← BitVec.or_assoc, BitVec.or_self]

theorem bitnot_bitnot (a : Word) :
    Unary.bitnot.eval (Unary.bitnot.eval a) = a := by
  change ~~~(~~~a) = a
  exact BitVec.not_not

theorem iszero_triple (a : Word) :
    Unary.iszero.eval (Unary.iszero.eval (Unary.iszero.eval a)) = Unary.iszero.eval a := by
  simp only [Unary.eval, boolWord]
  by_cases h : a = 0#256 <;> simp [h]

private theorem iszero_iszero_boolWord (p : Bool) :
    Unary.iszero.eval (Unary.iszero.eval (boolWord p)) = boolWord p := by
  cases p <;> decide

theorem iszero_iszero_eq (a b : Word) :
    Unary.iszero.eval (Unary.iszero.eval (Binary.eq.eval a b)) = Binary.eq.eval a b :=
  iszero_iszero_boolWord _

theorem iszero_iszero_lt (a b : Word) :
    Unary.iszero.eval (Unary.iszero.eval (Binary.lt.eval a b)) = Binary.lt.eval a b :=
  iszero_iszero_boolWord _

theorem iszero_iszero_gt (a b : Word) :
    Unary.iszero.eval (Unary.iszero.eval (Binary.gt.eval a b)) = Binary.gt.eval a b :=
  iszero_iszero_boolWord _

theorem iszero_iszero_slt (a b : Word) :
    Unary.iszero.eval (Unary.iszero.eval (Binary.slt.eval a b)) = Binary.slt.eval a b :=
  iszero_iszero_boolWord _

theorem iszero_iszero_sgt (a b : Word) :
    Unary.iszero.eval (Unary.iszero.eval (Binary.sgt.eval a b)) = Binary.sgt.eval a b :=
  iszero_iszero_boolWord _

theorem iszero_xor_eq (a b : Word) :
    Unary.iszero.eval (Binary.xor.eval a b) = Binary.eq.eval a b := by
  change boolWord ((a ^^^ b) == 0#256) = boolWord (a == b)
  congr 1
  by_cases hab : a = b
  · subst hab; simp
  · have hne : a ^^^ b ≠ 0#256 := by
      intro hz
      apply hab
      have h := congrArg (fun w => w ^^^ b) hz
      simpa [BitVec.xor_assoc] using h
    have h1 : (a ^^^ b == 0#256) = false := beq_false_of_ne hne
    have h2 : (a == b) = false := beq_false_of_ne hab
    rw [h1, h2]

theorem iszero_sub_eq (a b : Word) :
    Unary.iszero.eval (Binary.sub.eval a b) = Binary.eq.eval a b := by
  change boolWord ((a - b) == 0#256) = boolWord (a == b)
  congr 1
  by_cases hab : a = b
  · subst hab; simp
  · have hne : a - b ≠ 0#256 := by
      intro hz
      apply hab
      have h := congrArg (fun w => w + b) hz
      simpa [BitVec.sub_add_cancel] using h
    have h1 : (a - b == 0#256) = false := beq_false_of_ne hne
    have h2 : (a == b) = false := beq_false_of_ne hab
    rw [h1, h2]

/-! ## Part 4.5 & Part 5: `SIGNEXTEND` idempotence/composition & 160-bit address masks -/

private theorem evmSignextend_getLsbD (b x : Word) (hb : b.toNat < 31) (i : Nat) (hi : i < 256) :
    (evmSignextend b x).getLsbD i =
      if i ≤ b.toNat * 8 + 7 then x.getLsbD i else x.getLsbD (b.toNat * 8 + 7) := by
  unfold evmSignextend
  have hult : b.ult 31#256 = true := by
    simp [BitVec.ult]; omega
  rw [if_pos hult]
  dsimp only
  have hbit_lt : b.toNat * 8 + 7 < 256 := by omega
  have htest : ((x &&& (1#256 <<< (b.toNat * 8 + 7))) != 0#256) = x.getLsbD (b.toNat * 8 + 7) := by
    cases hxb : x.getLsbD (b.toNat * 8 + 7)
    · apply Bool.eq_false_iff.mpr
      simp only [bne_iff_ne, ne_eq, Decidable.not_not]
      apply BitVec.eq_of_getLsbD_eq
      intro k _
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, BitVec.getLsbD_zero]
      by_cases hkb : k = b.toNat * 8 + 7
      · subst hkb; simp [hxb]
      · have hne : k - (b.toNat * 8 + 7) ≠ 0 ∨ k < b.toNat * 8 + 7 := by omega
        rcases hne with h1 | h2
        · simp [h1]
        · simp [h2]
    · by_cases hnz : x &&& (1#256 <<< (b.toNat * 8 + 7)) = 0#256
      · exfalso
        have hbit0 : (x &&& (1#256 <<< (b.toNat * 8 + 7))).getLsbD (b.toNat * 8 + 7) =
            (0#256 : Word).getLsbD (b.toNat * 8 + 7) :=
          congrArg (fun w => BitVec.getLsbD w (b.toNat * 8 + 7)) hnz
        rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero, hxb] at hbit0
        simp [hbit_lt] at hbit0
      · exact bne_iff_ne.mpr hnz
  by_cases hxbit : x.getLsbD (b.toNat * 8 + 7) = true
  · have hcond : ((x &&& (1#256 <<< (b.toNat * 8 + 7))) != 0#256) = true := htest.trans hxbit
    rw [if_pos hcond]
    simp only [BitVec.getLsbD_or, BitVec.getLsbD_not, hi, decide_true, Bool.true_and,
      low_mask_getLsbD (b.toNat * 8 + 7) hbit_lt i hi]
    by_cases hle : i ≤ b.toNat * 8 + 7
    · by_cases heq : i = b.toNat * 8 + 7
      · subst heq; simp [hxbit]
      · have hlt : i < b.toNat * 8 + 7 := by omega
        simp [hle, hlt]
    · have hnlt : ¬(i < b.toNat * 8 + 7) := by omega
      simp [hle, hnlt, hxbit]
  · have hxf : x.getLsbD (b.toNat * 8 + 7) = false := Bool.eq_false_iff.mpr hxbit
    have hcond : ((x &&& (1#256 <<< (b.toNat * 8 + 7))) != 0#256) = false := htest.trans hxf
    rw [if_neg (by simp [hcond])]
    simp only [BitVec.getLsbD_and, low_mask_getLsbD (b.toNat * 8 + 7) hbit_lt i hi]
    by_cases hle : i ≤ b.toNat * 8 + 7
    · by_cases heq : i = b.toNat * 8 + 7
      · subst heq; simp [hxf]
      · have hlt : i < b.toNat * 8 + 7 := by omega
        simp [hle, hlt]
    · have hnlt : ¬(i < b.toNat * 8 + 7) := by omega
      simp [hle, hnlt, hxf]

theorem signextend_nested_min (b1 b2 x : Word) :
    Binary.signextend.eval b1 (Binary.signextend.eval b2 x) =
      Binary.signextend.eval (if b1.toNat ≤ b2.toNat then b1 else b2) x := by
  simp only [Binary.eval]
  by_cases hb2 : 31 ≤ b2.toNat
  · have hs2 : evmSignextend b2 x = x := signextend_ge_31 b2 x hb2
    rw [hs2]
    by_cases hle : b1.toNat ≤ b2.toNat
    · simp [hle]
    · simp only [hle, ↓reduceIte]
      exact (signextend_ge_31 b1 x (by omega)).trans hs2.symm
  · have hb2lt : b2.toNat < 31 := by omega
    by_cases hb1 : 31 ≤ b1.toNat
    · have hs1 : evmSignextend b1 (evmSignextend b2 x) = evmSignextend b2 x :=
        signextend_ge_31 b1 _ hb1
      have hnle : ¬(b1.toNat ≤ b2.toNat) := by omega
      simp [hs1, hnle]
    · have hb1lt : b1.toNat < 31 := by omega
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [evmSignextend_getLsbD b1 _ hb1lt i hi]
      by_cases hle : b1.toNat ≤ b2.toNat
      · simp only [hle, ↓reduceIte]
        rw [evmSignextend_getLsbD b1 x hb1lt i hi]
        by_cases hi1 : i ≤ b1.toNat * 8 + 7
        · simp only [hi1, ↓reduceIte]
          rw [evmSignextend_getLsbD b2 x hb2lt i hi]
          have hi2 : i ≤ b2.toNat * 8 + 7 := by omega
          simp [hi2]
        · simp only [hi1, ↓reduceIte]
          rw [evmSignextend_getLsbD b2 x hb2lt (b1.toNat * 8 + 7) (by omega)]
          have hb12 : b1.toNat * 8 + 7 ≤ b2.toNat * 8 + 7 := by omega
          simp [hb12]
      · simp only [hle, ↓reduceIte]
        rw [evmSignextend_getLsbD b2 x hb2lt i hi]
        by_cases hi1 : i ≤ b1.toNat * 8 + 7
        · simp only [hi1, ↓reduceIte]
        · simp only [hi1, ↓reduceIte]
          have hn2 : ¬(i ≤ b2.toNat * 8 + 7) := by omega
          have hb12 : ¬(b1.toNat * 8 + 7 ≤ b2.toNat * 8 + 7) := by omega
          rw [evmSignextend_getLsbD b2 x hb2lt (b1.toNat * 8 + 7) (by omega)]
          simp [hn2, hb12]

theorem signextend_idempotent (b x : Word) :
    Binary.signextend.eval b (Binary.signextend.eval b x) = Binary.signextend.eval b x := by
  simpa using signextend_nested_min b b x

theorem strip_signextend_low_mask (mask b x : Word)
    (hb : b.toNat < 31)
    (hmask : mask &&& ((1#256 <<< ((b.toNat + 1) * 8)) - 1#256) = mask) :
    Binary.and.eval mask (Binary.signextend.eval b x) = Binary.and.eval mask x := by
  simp only [Binary.eval]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  by_cases hle : i ≤ b.toNat * 8 + 7
  · rw [evmSignextend_getLsbD b x hb i hi]
    simp [hle]
  · have hm0 : mask.getLsbD i = false := by
      have hbit := congrArg (fun w => BitVec.getLsbD w i) hmask.symm
      simp only [BitVec.getLsbD_and] at hbit
      have hlow0 : (((1#256 <<< ((b.toNat + 1) * 8)) - 1#256)).getLsbD i = false := by
        rw [low_mask_getLsbD ((b.toNat + 1) * 8) (by omega) i hi]
        have : ¬(i < (b.toNat + 1) * 8) := by omega
        simp [this]
      rw [hbit, hlow0, Bool.and_false]
    simp [hm0]

theorem address_mask_idempotent (ctx : Context) (op : Nullary) :
    Binary.and.eval (op.eval ctx) ((1#256 <<< 160) - 1#256) = op.eval ctx ∧
    Binary.and.eval ((1#256 <<< 160) - 1#256) (op.eval ctx) = op.eval ctx := by
  constructor
  · exact Nullary.eval_masked ctx op
  · simp only [Binary.eval]
    rw [BitVec.and_comm]
    exact Nullary.eval_masked ctx op

/-! ## Part 5 & EVM tail: Power-of-two `MOD`, `MUL`, `DIV`, and `EXP` base rules -/

theorem mod_pow2_eq_and (x : Word) (k : Nat) (hk : k < 256) :
    Binary.mod.eval x (1#256 <<< k) = Binary.and.eval x ((1#256 <<< k) - 1#256) := by
  simp only [Binary.eval, evmMod, one_shiftLeft_ne_zero k hk, ↓reduceIte]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, low_mask_getLsbD k hk i hi]
  rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat, BitVec.toNat_umod,
    one_shiftLeft_toNat k hk, Nat.testBit_mod_two_pow]
  rw [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_eq_testBit_toNat, Bool.and_comm]

theorem mul_pow2_eq_shl (x : Word) (k : Nat) (hk : k < 256) :
    Binary.mul.eval x (1#256 <<< k) = Binary.shl.eval (BitVec.ofNat 256 k) x ∧
    Binary.mul.eval (1#256 <<< k) x = Binary.shl.eval (BitVec.ofNat 256 k) x := by
  have hk_nat : (BitVec.ofNat 256 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
  have hmul : x * (1#256 <<< k) = x <<< k := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, one_shiftLeft_toNat k hk, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  refine ⟨?_, ?_⟩
  · simp [Binary.eval, evmShl_eq_shiftLeft, hk_nat, hmul]
  · simp [Binary.eval, BitVec.mul_comm, evmShl_eq_shiftLeft, hk_nat, hmul]

theorem div_pow2_eq_shr (x : Word) (k : Nat) (hk : k < 256) :
    Binary.div.eval x (1#256 <<< k) = Binary.shr.eval (BitVec.ofNat 256 k) x := by
  have hk_nat : (BitVec.ofNat 256 k).toNat = k := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
  simp only [Binary.eval, evmDiv, one_shiftLeft_ne_zero k hk, ↓reduceIte, evmShr_eq_ushiftRight, hk_nat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, one_shiftLeft_toNat k hk, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem mul_shl_one_eq_shl (x s : Word) :
    Binary.mul.eval x (Binary.shl.eval s 1#256) = Binary.shl.eval s x ∧
    Binary.mul.eval (Binary.shl.eval s 1#256) x = Binary.shl.eval s x := by
  by_cases hs : s.toNat < 256
  · have h1 : Binary.shl.eval s 1#256 = 1#256 <<< s.toNat := evmShl_eq_shiftLeft s 1#256
    have ⟨hl, hr⟩ := mul_pow2_eq_shl x s.toNat hs
    have hs256 : BitVec.ofNat 256 s.toNat = s := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt s.isLt]
    rw [hs256] at hl hr
    exact ⟨by simpa [h1] using hl, by simpa [h1] using hr⟩
  · have hz1 : evmShl s 1#256 = 0#256 := shl_ge_256 s 1#256 (by omega)
    have hzx : evmShl s x = 0#256 := shl_ge_256 s x (by omega)
    simp [Binary.eval, hz1, hzx]

theorem div_shl_one_eq_shr (x s : Word) :
    Binary.div.eval x (Binary.shl.eval s 1#256) = Binary.shr.eval s x := by
  by_cases hs : s.toNat < 256
  · have h1 : Binary.shl.eval s 1#256 = 1#256 <<< s.toNat := evmShl_eq_shiftLeft s 1#256
    have hd := div_pow2_eq_shr x s.toNat hs
    have hs256 : BitVec.ofNat 256 s.toNat = s := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt s.isLt]
    rw [hs256] at hd
    simpa [h1] using hd
  · have hz1 : evmShl s 1#256 = 0#256 := shl_ge_256 s 1#256 (by omega)
    have hzx : evmShr s x = 0#256 := shr_ge_256 s x (by omega)
    simp [Binary.eval, evmDiv, hz1, hzx]

theorem exp_zero_base (e : Word) :
    Binary.exp.eval 0#256 e = Unary.iszero.eval e := by
  simp only [Binary.eval, evmExp_eq_pow, Unary.eval, boolWord]
  have h0 : (0#256 : Word).toNat = 0 := rfl
  rw [h0]
  by_cases he : e = 0#256
  · subst he; rfl
  · have hpos : e.toNat ≠ 0 := by
      intro hz; exact he (BitVec.eq_of_toNat_eq hz)
    simp [he, Nat.zero_pow (Nat.pos_of_ne_zero hpos)]

theorem exp_one_base (e : Word) :
    Binary.exp.eval 1#256 e = 1#256 := by
  simp [Binary.eval, evmExp_eq_pow]

theorem exp_two_base (e : Word) :
    Binary.exp.eval 2#256 e = Binary.shl.eval e 1#256 := by
  simp only [Binary.eval, evmExp_eq_pow, evmShl_eq_shiftLeft]
  have h2 : (2#256 : Word).toNat = 2 := rfl
  have h1 : (1#256 : Word).toNat = 1 := rfl
  rw [h2]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, h1, Nat.shiftLeft_eq, Nat.one_mul]

private def maxPowIter : Nat → Word
  | 0 => 1#256
  | n + 1 => maxPowIter n * (-1#256)

private theorem allOnes_eq_neg_one : BitVec.allOnes 256 = -1#256 :=
  BitVec.neg_one_eq_allOnes.symm

private theorem maxPowIter_eq_pow (n : Nat) :
    BitVec.ofNat 256 ((BitVec.allOnes 256).toNat ^ n) = maxPowIter n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.pow_succ, maxPowIter, ← ih, ← allOnes_eq_neg_one]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.mod_mul_mod]

private theorem maxPowIter_parity (n : Nat) :
    maxPowIter n = if n % 2 = 0 then 1#256 else -1#256 := by
  have hmul1 : (1#256 : Word) * (-1#256) = -1#256 := BitVec.one_mul _
  have hmul2 : (-1#256 : Word) * (-1#256) = 1#256 := by
    rw [BitVec.neg_mul_neg, BitVec.one_mul]
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [maxPowIter, ih]
    have hrem : n % 2 = 0 ∨ n % 2 = 1 := by omega
    rcases hrem with h0 | h1
    · have h1' : (n + 1) % 2 = 1 := by omega
      rw [if_pos h0, if_neg (by omega), hmul1]
    · have h0' : (n + 1) % 2 = 0 := by omega
      rw [if_neg (by omega), if_pos h0', hmul2]

theorem exp_max_base (e : Word) :
    Binary.exp.eval (BitVec.allOnes 256) e =
      Binary.sub.eval (Unary.iszero.eval (Binary.and.eval e 1#256)) (Binary.and.eval e 1#256) := by
  simp only [Binary.eval, evmExp_eq_pow, maxPowIter_eq_pow, maxPowIter_parity]
  have hand : (e &&& 1#256) = if e.toNat % 2 = 0 then 0#256 else 1#256 := by
    apply BitVec.eq_of_toNat_eq
    have hbit : (e &&& 1#256).toNat = e.toNat % 2 := by
      have h1 : (1#256 : Word).toNat = 2 ^ 1 - 1 := rfl
      rw [BitVec.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, Nat.pow_one]
    rw [hbit]
    by_cases h0 : e.toNat % 2 = 0
    · rw [if_pos h0]; exact h0
    · have h1 : e.toNat % 2 = 1 := by omega
      rw [if_neg h0]; exact h1
  rw [hand]
  by_cases h0 : e.toNat % 2 = 0
  · rw [if_pos h0, if_pos h0]
    rfl
  · rw [if_neg h0, if_neg h0]
    rfl

/-! ## Part 7 & Part 8: Shift combinations, mask distributivity, and constant motion -/

theorem shl_nested (s1 s2 x : Word) :
    Binary.shl.eval s1 (Binary.shl.eval s2 x) =
      if 256 - min s2.toNat 256 ≤ s1.toNat then 0#256
      else Binary.shl.eval (BitVec.ofNat 256 (s1.toNat + s2.toNat)) x := by
  simp only [Binary.eval, evmShl_eq_shiftLeft]
  by_cases hover : 256 - min s2.toNat 256 ≤ s1.toNat
  · simp only [hover, ↓reduceIte]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero]
    by_cases hi1 : i < s1.toNat
    · simp [hi1]
    · have hi2 : i - s1.toNat < s2.toNat := by omega
      simp [hi1, hi2]
  · simp only [hover, ↓reduceIte]
    have hsum : s1.toNat + s2.toNat < 256 := by omega
    have hnat : (BitVec.ofNat 256 (s1.toNat + s2.toNat)).toNat = s1.toNat + s2.toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
    rw [hnat]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_shiftLeft]
    by_cases hi1 : i < s1.toNat
    · have hi12 : i < s1.toNat + s2.toNat := by omega
      simp [hi1, hi12]
    · by_cases hi2 : i - s1.toNat < s2.toNat
      · have hi12 : i < s1.toNat + s2.toNat := by omega
        simp [hi1, hi2, hi12]
      · have hi12 : ¬(i < s1.toNat + s2.toNat) := by omega
        have hlt_sub : i - s1.toNat < 256 := by omega
        have hsub : i - s1.toNat - s2.toNat = i - (s1.toNat + s2.toNat) := by omega
        simp [hi, hi1, hi2, hi12, hlt_sub, hsub]

theorem shr_nested (s1 s2 x : Word) :
    Binary.shr.eval s1 (Binary.shr.eval s2 x) =
      if 256 - min s2.toNat 256 ≤ s1.toNat then 0#256
      else Binary.shr.eval (BitVec.ofNat 256 (s1.toNat + s2.toNat)) x := by
  simp only [Binary.eval, evmShr_eq_ushiftRight]
  by_cases hover : 256 - min s2.toNat 256 ≤ s1.toNat
  · simp only [hover, ↓reduceIte]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
    exact BitVec.getLsbD_of_ge x _ (by omega)
  · simp only [hover, ↓reduceIte]
    have hsum : s1.toNat + s2.toNat < 256 := by omega
    have hnat : (BitVec.ofNat 256 (s1.toNat + s2.toNat)).toNat = s1.toNat + s2.toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
    rw [hnat]
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    simp only [BitVec.getLsbD_ushiftRight]
    congr 1
    omega

theorem shr_of_shl_combine (outer inner x : Word)
    (ho : outer.toNat < 256) (hi : inner.toNat < 256) :
    Binary.shr.eval outer (Binary.shl.eval inner x) =
      Binary.and.eval
        (if outer.toNat < inner.toNat then
           Binary.shl.eval (BitVec.ofNat 256 (inner.toNat - outer.toNat)) x
         else if inner.toNat < outer.toNat then
           Binary.shr.eval (BitVec.ofNat 256 (outer.toNat - inner.toNat)) x
         else x)
        (((BitVec.allOnes 256) <<< inner.toNat) >>> outer.toNat) := by
  simp only [Binary.eval, evmShl_eq_shiftLeft, evmShr_eq_ushiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_allOnes]
  by_cases hcmp1 : outer.toNat < inner.toNat
  · have hnat : (BitVec.ofNat 256 (inner.toNat - outer.toNat)).toNat = inner.toNat - outer.toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
    simp only [hcmp1, ↓reduceIte, BitVec.getLsbD_shiftLeft, hnat]
    by_cases hko : outer.toNat + k < 256
    · by_cases hki : outer.toNat + k < inner.toNat
      · have hk1 : k < inner.toNat - outer.toNat := by omega
        simp [hko, hki, hk1]
      · have hk1 : ¬(k < inner.toNat - outer.toNat) := by omega
        have hsub : outer.toNat + k - inner.toNat = k - (inner.toNat - outer.toNat) := by omega
        have hlt2 : k - (inner.toNat - outer.toNat) < 256 := by omega
        simp [hk, hko, hki, hk1, hsub, hlt2]
    · simp [hko]
  · by_cases hcmp2 : inner.toNat < outer.toNat
    · have hnat : (BitVec.ofNat 256 (outer.toNat - inner.toNat)).toNat = outer.toNat - inner.toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
      simp only [hcmp1, hcmp2, ↓reduceIte, BitVec.getLsbD_ushiftRight, hnat]
      by_cases hko : outer.toNat + k < 256
      · have hki : ¬(outer.toNat + k < inner.toNat) := by omega
        have hsub : outer.toNat + k - inner.toNat = outer.toNat - inner.toNat + k := by omega
        have hlt2 : outer.toNat - inner.toNat + k < 256 := by omega
        simp [hko, hki, hsub, hlt2]
      · simp [hko]
    · have heq : outer.toNat = inner.toNat := by omega
      simp only [heq, Nat.lt_irrefl, ↓reduceIte]
      by_cases hko : inner.toNat + k < 256
      · have hki : ¬(inner.toNat + k < inner.toNat) := by omega
        have hsub : inner.toNat + k - inner.toNat = k := by omega
        simp [hk, hko, hki, hsub]
      · simp [hko]

theorem shl_of_shr_combine (outer inner x : Word)
    (ho : outer.toNat < 256) (hi : inner.toNat < 256) :
    Binary.shl.eval outer (Binary.shr.eval inner x) =
      Binary.and.eval
        (if outer.toNat < inner.toNat then
           Binary.shr.eval (BitVec.ofNat 256 (inner.toNat - outer.toNat)) x
         else if inner.toNat < outer.toNat then
           Binary.shl.eval (BitVec.ofNat 256 (outer.toNat - inner.toNat)) x
         else x)
        (((BitVec.allOnes 256) >>> inner.toNat) <<< outer.toNat) := by
  simp only [Binary.eval, evmShl_eq_shiftLeft, evmShr_eq_ushiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_allOnes]
  by_cases hcmp1 : outer.toNat < inner.toNat
  · have hnat : (BitVec.ofNat 256 (inner.toNat - outer.toNat)).toNat = inner.toNat - outer.toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
    simp only [hcmp1, ↓reduceIte, BitVec.getLsbD_ushiftRight, hnat]
    by_cases hko : k < outer.toNat
    · simp [hko]
    · by_cases hbound : inner.toNat + (k - outer.toNat) < 256
      · have hsub : inner.toNat - outer.toNat + k = inner.toNat + (k - outer.toNat) := by omega
        simp [hk, hko, hbound, hsub]
      · have hsub : inner.toNat - outer.toNat + k = inner.toNat + (k - outer.toNat) := by omega
        have hge : 256 ≤ inner.toNat + (k - outer.toNat) := by omega
        simp [hk, hko, hbound, hsub, BitVec.getLsbD_of_ge x _ hge]
  · by_cases hcmp2 : inner.toNat < outer.toNat
    · have hnat : (BitVec.ofNat 256 (outer.toNat - inner.toNat)).toNat = outer.toNat - inner.toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
      simp only [hcmp1, hcmp2, ↓reduceIte, BitVec.getLsbD_shiftLeft, hnat]
      by_cases hko : k < outer.toNat
      · simp [hko]
      · have hk1 : ¬(k < outer.toNat - inner.toNat) := by omega
        have hbound : inner.toNat + (k - outer.toNat) < 256 := by omega
        have hsub : k - (outer.toNat - inner.toNat) = inner.toNat + (k - outer.toNat) := by omega
        simp [hk, hko, hk1, hbound, hsub]
    · have heq : outer.toNat = inner.toNat := by omega
      simp only [heq, Nat.lt_irrefl, ↓reduceIte]
      by_cases hko : k < inner.toNat
      · simp [hko]
      · have hsub : inner.toNat + (k - inner.toNat) = k := by omega
        simp [hk, hko, hsub]

theorem distribute_alternating_mask (x y innerMask outerMask : Word) :
    Binary.and.eval (Binary.or.eval (Binary.and.eval x innerMask) y) outerMask =
      Binary.or.eval (Binary.and.eval x (innerMask &&& outerMask)) (Binary.and.eval y outerMask) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  simp only [Binary.eval, BitVec.getLsbD_and, BitVec.getLsbD_or]
  cases x.getLsbD k <;> cases y.getLsbD k <;> cases innerMask.getLsbD k <;> cases outerMask.getLsbD k <;> rfl

theorem remove_covered_shl_mask (mask s x : Word) (_hs : s.toNat ≤ 256)
    (hcov : mask &&& (if s.toNat = 256 then 0#256 else (BitVec.allOnes 256) <<< s.toNat) =
      (if s.toNat = 256 then 0#256 else (BitVec.allOnes 256) <<< s.toNat)) :
    Binary.and.eval mask (Binary.shl.eval s x) = Binary.shl.eval s x := by
  simp only [Binary.eval, evmShl_eq_shiftLeft]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
  by_cases h256 : s.toNat = 256
  · have hlt : k < s.toNat := by omega
    simp [hk, hlt]
  · simp only [h256, ↓reduceIte] at hcov
    by_cases hks : k < s.toNat
    · simp [hk, hks]
    · have hm : mask.getLsbD k = true := by
        have hb : (mask &&& ((BitVec.allOnes 256) <<< s.toNat)).getLsbD k =
            (((BitVec.allOnes 256) <<< s.toNat)).getLsbD k :=
          congrArg (fun w => BitVec.getLsbD w k) hcov
        have hsub_lt : k - s.toNat < 256 := by omega
        rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes] at hb
        simp only [hk, hks, hsub_lt, decide_true, decide_false,
          Bool.not_false, Bool.and_true] at hb
        exact hb
      simp [hk, hks, hm]

theorem remove_covered_shr_mask (mask s x : Word) (_hs : s.toNat ≤ 256)
    (hcov : mask &&& (if s.toNat = 256 then 0#256 else (BitVec.allOnes 256) >>> s.toNat) =
      (if s.toNat = 256 then 0#256 else (BitVec.allOnes 256) >>> s.toNat)) :
    Binary.and.eval mask (Binary.shr.eval s x) = Binary.shr.eval s x := by
  simp only [Binary.eval, evmShr_eq_ushiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  by_cases h256 : s.toNat = 256
  · have hge : 256 ≤ s.toNat + k := by omega
    simp [BitVec.getLsbD_of_ge x (s.toNat + k) hge]
  · simp only [h256, ↓reduceIte] at hcov
    by_cases hsk : s.toNat + k < 256
    · have hm : mask.getLsbD k = true := by
        have hb := congrArg (fun w => BitVec.getLsbD w k) hcov
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes,
          hsk, decide_true, Bool.and_true] at hb
        exact hb
      simp [hm]
    · have hge : 256 ≤ s.toNat + k := by omega
      simp [BitVec.getLsbD_of_ge x (s.toNat + k) hge]

theorem and_shl_distribute (s x y : Word) :
    Binary.and.eval (Binary.shl.eval s x) (Binary.shl.eval s y) =
      Binary.shl.eval s (Binary.and.eval x y) := by
  simp only [Binary.eval, evmShl_eq_shiftLeft]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and]
  by_cases hks : k < s.toNat <;> simp [hks]

theorem sub_const_eq_add_neg (x c : Word) :
    Binary.sub.eval x c = Binary.add.eval x (0#256 - c) := by
  change x - c = x + (0#256 - c)
  rw [BitVec.zero_sub, BitVec.sub_eq_add_neg]

theorem sub_nested_reassociate (x y c : Word) :
    Binary.sub.eval (Binary.add.eval x c) y = Binary.add.eval (Binary.sub.eval x y) c ∧
    Binary.sub.eval x (Binary.add.eval y c) = Binary.add.eval (Binary.sub.eval x y) (0#256 - c) ∧
    Binary.sub.eval (Binary.sub.eval x c) y = Binary.sub.eval (Binary.sub.eval x y) c ∧
    Binary.sub.eval (Binary.sub.eval c x) y = Binary.sub.eval c (Binary.add.eval x y) ∧
    Binary.sub.eval x (Binary.sub.eval y c) = Binary.add.eval (Binary.sub.eval x y) c ∧
    Binary.sub.eval x (Binary.sub.eval c y) = Binary.add.eval (Binary.add.eval x y) (0#256 - c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (x + c) - y = (x - y) + c
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm c (-y)]
  · change x - (y + c) = (x - y) + (0#256 - c)
    simp [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]
  · change (x - c) - y = (x - y) - c
    simp [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.add_comm (-c) (-y)]
  · change (c - x) - y = c - (x + y)
    simp [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]
  · change x - (y - c) = (x - y) + c
    simp [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  · change x - (c - y) = (x + y) + (0#256 - c)
    simp [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg,
      BitVec.add_assoc, BitVec.add_comm (-c) y]

theorem signextend_shr_eq_sar (b amount x : Word)
    (hdiv : amount.toNat % 8 = 0)
    (hamt : amount.toNat ≤ 256)
    (hb : b.toNat ≤ 256)
    (heq : (256 - amount.toNat) / 8 = b.toNat + 1) :
    Binary.signextend.eval b (Binary.shr.eval amount x) = Binary.sar.eval amount x := by
  simp only [Binary.eval, evmShr_eq_ushiftRight, evmSar]
  have hamt_lt : amount.toNat < 256 := by omega
  have hamt_ult : amount.ult 256#256 = true := by simp [BitVec.ult]; omega
  simp only [hamt_ult, ↓reduceIte]
  by_cases ha0 : amount.toNat = 0
  · have hs : evmSignextend b (x >>> amount.toNat) = x >>> amount.toNat :=
      signextend_ge_31 b (x >>> amount.toNat) (by omega)
    rw [hs]
    simp [ha0]
  · have hb_lt : b.toNat < 31 := by omega
    have hbit : b.toNat * 8 + 7 = 255 - amount.toNat := by omega
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [evmSignextend_getLsbD b (x >>> amount.toNat) hb_lt i hi]
    simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight]
    rw [hbit]
    by_cases hle : i ≤ 255 - amount.toNat
    · have hlt256 : amount.toNat + i < 256 := by omega
      simp [hi, hle, hlt256]
    · have hnlt256 : ¬(amount.toNat + i < 256) := by omega
      have htop : amount.toNat + (255 - amount.toNat) = 255 := by omega
      simp [hi, hle, hnlt256, htop, BitVec.msb_eq_getLsbD_last]

theorem byte_shl (i amount x : Word)
    (hmod : amount.toNat % 8 = 0)
    (hi : i.toNat ≤ 32)
    (hamt : amount.toNat ≤ 256) :
    Binary.byte.eval i (Binary.shl.eval amount x) =
      Binary.byte.eval (BitVec.ofNat 256 (i.toNat + amount.toNat / 8)) x := by
  simp only [Binary.eval, evmByte, evmShl_eq_shiftLeft]
  have hsum_nat : (BitVec.ofNat 256 (i.toNat + amount.toNat / 8)).toNat = i.toNat + amount.toNat / 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
  by_cases hbound : i.toNat + amount.toNat / 8 < 32
  · have hi_lt : i.toNat < 32 := by omega
    have hi_ult : i.ult 32#256 = true := by simp [BitVec.ult]; omega
    have hsum_ult : (BitVec.ofNat 256 (i.toNat + amount.toNat / 8)).ult 32#256 = true := by
      simp [BitVec.ult, hsum_nat, hbound]
    rw [if_pos hi_ult, if_pos hsum_ult, hsum_nat]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft]
    by_cases hk8 : k < 8
    · have hk0xff : (0xff#256 : Word).getLsbD k = true := by
        have hlt256 : (0xff#256 : Word).toNat = 2 ^ 8 - 1 := rfl
        rw [BitVec.getLsbD_eq_getElem hk, BitVec.getElem_eq_testBit_toNat, hlt256,
          Nat.testBit_two_pow_sub_one]
        simp [hk8]
      have hidx1 : 8 * (31 - i.toNat) + k < 256 := by omega
      have hnlt : ¬(8 * (31 - i.toNat) + k < amount.toNat) := by omega
      have hsub : 8 * (31 - i.toNat) + k - amount.toNat =
          8 * (31 - (i.toNat + amount.toNat / 8)) + k := by omega
      simp [hk0xff, hidx1, hnlt, hsub]
    · have hk0xff : (0xff#256 : Word).getLsbD k = false := by
        have hlt256 : (0xff#256 : Word).toNat = 2 ^ 8 - 1 := rfl
        rw [BitVec.getLsbD_eq_getElem hk, BitVec.getElem_eq_testBit_toNat, hlt256,
          Nat.testBit_two_pow_sub_one]
        simp [hk8]
      simp [hk0xff]
  · have hsum_nult : ¬((BitVec.ofNat 256 (i.toNat + amount.toNat / 8)).ult 32#256 = true) := by
      simp [BitVec.ult, hsum_nat]; omega
    rw [if_neg hsum_nult]
    by_cases hi_lt : i.toNat < 32
    · have hi_ult : i.ult 32#256 = true := by simp [BitVec.ult, hi_lt]
      rw [if_pos hi_ult]
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
        BitVec.getLsbD_zero]
      by_cases hk8 : k < 8
      · have hlt_amt : 8 * (31 - i.toNat) + k < amount.toNat := by omega
        have hidx1 : 8 * (31 - i.toNat) + k < 256 := by omega
        simp [hidx1, hlt_amt]
      · have hk0xff : (0xff#256 : Word).getLsbD k = false := by
          have hlt256 : (0xff#256 : Word).toNat = 2 ^ 8 - 1 := rfl
          rw [BitVec.getLsbD_eq_getElem hk, BitVec.getElem_eq_testBit_toNat, hlt256,
            Nat.testBit_two_pow_sub_one]
          simp [hk8]
        simp [hk0xff]
    · have hi_nult : ¬(i.ult 32#256 = true) := by simp [BitVec.ult]; omega
      rw [if_neg hi_nult]

theorem byte_shr_zero (i amount x : Word)
    (hlt : i.toNat < amount.toNat / 8) :
    Binary.byte.eval i (Binary.shr.eval amount x) = 0#256 := by
  simp only [Binary.eval, evmByte, evmShr_eq_ushiftRight]
  by_cases hi_lt : i.toNat < 32
  · have hi_ult : i.ult 32#256 = true := by simp [BitVec.ult, hi_lt]
    rw [if_pos hi_ult]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero]
    by_cases hk8 : k < 8
    · have hge : 256 ≤ amount.toNat + (8 * (31 - i.toNat) + k) := by omega
      simp [BitVec.getLsbD_of_ge x _ hge]
    · have hk0xff : (0xff#256 : Word).getLsbD k = false := by
        have hlt256 : (0xff#256 : Word).toNat = 2 ^ 8 - 1 := rfl
        rw [BitVec.getLsbD_eq_getElem hk, BitVec.getElem_eq_testBit_toNat, hlt256,
          Nat.testBit_two_pow_sub_one]
        simp [hk8]
      simp [hk0xff]
  · have hi_nult : ¬(i.ult 32#256 = true) := by simp [BitVec.ult]; omega
    rw [if_neg hi_nult]

theorem byte_shr (i amount x : Word)
    (hmod : amount.toNat % 8 = 0)
    (hi : i.toNat < 32)
    (hamt : amount.toNat ≤ 256)
    (hge : amount.toNat / 8 ≤ i.toNat) :
    Binary.byte.eval i (Binary.shr.eval amount x) =
      Binary.byte.eval (BitVec.ofNat 256 (i.toNat - amount.toNat / 8)) x := by
  simp only [Binary.eval, evmByte, evmShr_eq_ushiftRight]
  have hsub_nat : (BitVec.ofNat 256 (i.toNat - amount.toNat / 8)).toNat = i.toNat - amount.toNat / 8 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
  have hi_ult : i.ult 32#256 = true := by simp [BitVec.ult, hi]
  have hsub_ult : (BitVec.ofNat 256 (i.toNat - amount.toNat / 8)).ult 32#256 = true := by
    simp [BitVec.ult, hsub_nat]; omega
  rw [if_pos hi_ult, if_pos hsub_ult, hsub_nat]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight]
  by_cases hk8 : k < 8
  · have hadd : amount.toNat + (8 * (31 - i.toNat) + k) =
        8 * (31 - (i.toNat - amount.toNat / 8)) + k := by omega
    rw [hadd]
  · have hk0xff : (0xff#256 : Word).getLsbD k = false := by
      have hlt256 : (0xff#256 : Word).toNat = 2 ^ 8 - 1 := rfl
      rw [BitVec.getLsbD_eq_getElem hk, BitVec.getElem_eq_testBit_toNat, hlt256,
        Nat.testBit_two_pow_sub_one]
      simp [hk8]
    simp [hk0xff]

theorem shl_signextend (s b x : Word)
    (hmod : s.toNat % 8 = 0)
    (hs : s.toNat ≤ 256)
    (hb : b.toNat ≤ 32) :
    Binary.shl.eval s (Binary.signextend.eval b x) =
      Binary.signextend.eval (BitVec.ofNat 256 (s.toNat / 8 + b.toNat)) (Binary.shl.eval s x) := by
  have hsum_nat : (BitVec.ofNat 256 (s.toNat / 8 + b.toNat)).toNat = s.toNat / 8 + b.toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.lt_two_pow_self (n := 256); omega)]
  by_cases hover : 31 ≤ s.toNat / 8 + b.toNat
  · have hover_w : 31 ≤ (BitVec.ofNat 256 (s.toNat / 8 + b.toNat)).toNat := by
      rw [hsum_nat]; exact hover
    rw [signextend_ge_31 (BitVec.ofNat 256 (s.toNat / 8 + b.toNat)) (Binary.shl.eval s x) hover_w]
    by_cases hs256 : s.toNat = 256
    · rw [shl_ge_256 s _ (by omega), shl_ge_256 s _ (by omega)]
    · by_cases hb31 : 31 ≤ b.toNat
      · rw [signextend_ge_31 b x hb31]
      · have hb_lt : b.toNat < 31 := by omega
        simp only [Binary.eval, evmShl_eq_shiftLeft]
        apply BitVec.eq_of_getLsbD_eq
        intro k hk
        simp only [BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and]
        by_cases hks : k < s.toNat
        · simp [hks]
        · simp only [hks, decide_false, Bool.not_false, Bool.true_and]
          rw [evmSignextend_getLsbD b x hb_lt (k - s.toNat) (by omega)]
          have hle : k - s.toNat ≤ b.toNat * 8 + 7 := by omega
          simp [hle]
  · have hsum_lt : (BitVec.ofNat 256 (s.toNat / 8 + b.toNat)).toNat < 31 := by
      rw [hsum_nat]; omega
    have hb_lt : b.toNat < 31 := by omega
    simp only [Binary.eval, evmShl_eq_shiftLeft]
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [evmSignextend_getLsbD _ (x <<< s.toNat) hsum_lt k hk]
    rw [hsum_nat]
    simp only [BitVec.getLsbD_shiftLeft, hk, decide_true, Bool.true_and]
    by_cases hks : k < s.toNat
    · have hle : k ≤ (s.toNat / 8 + b.toNat) * 8 + 7 := by omega
      simp [hks, hle]
    · simp only [hks, decide_false, Bool.not_false, Bool.true_and]
      rw [evmSignextend_getLsbD b x hb_lt (k - s.toNat) (by omega)]
      by_cases hle : k ≤ (s.toNat / 8 + b.toNat) * 8 + 7
      · have hle2 : k - s.toNat ≤ b.toNat * 8 + 7 := by omega
        simp [hle, hle2]
      · have hnle2 : ¬(k - s.toNat ≤ b.toNat * 8 + 7) := by omega
        have hnlt_top : ¬((s.toNat / 8 + b.toNat) * 8 + 7 < s.toNat) := by omega
        have htop_lt : (s.toNat / 8 + b.toNat) * 8 + 7 < 256 := by omega
        have htop_sub : (s.toNat / 8 + b.toNat) * 8 + 7 - s.toNat = b.toNat * 8 + 7 := by omega
        simp [hle, hnle2, hnlt_top, htop_lt, htop_sub]

theorem shl_and_const (s x mask : Word) (_hs : s.toNat < 256) :
    Binary.shl.eval s (Binary.and.eval x mask) =
      Binary.and.eval (Binary.shl.eval s x) (mask <<< s.toNat) := by
  simp only [Binary.eval, evmShl_eq_shiftLeft]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, hk, decide_true, Bool.true_and]
  by_cases hks : k < s.toNat <;> simp [hks]

theorem shr_and_const (s x mask : Word) (_hs : s.toNat < 256) :
    Binary.shr.eval s (Binary.and.eval x mask) =
      Binary.and.eval (Binary.shr.eval s x) (mask >>> s.toNat) := by
  simp only [Binary.eval, evmShr_eq_ushiftRight]
  apply BitVec.eq_of_getLsbD_eq
  intro k _
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and]

theorem add_mod_pow2_eq_addmod (a b : Word) (k : Nat) (hk : k < 256) :
    Binary.mod.eval (Binary.add.eval a b) (1#256 <<< k) =
      Ternary.addmod.eval a b (1#256 <<< k) := by
  simp only [Binary.eval, Ternary.eval, evmMod, evmAddmod]
  have hpow : (1#256 <<< k).toNat = 2 ^ k := by
    rw [BitVec.toNat_shiftLeft]
    simp only [BitVec.toNat_ofNat]
    have h1 : 1 % 2 ^ 256 = 1 := rfl
    rw [h1, Nat.one_shiftLeft]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hk)
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hne0 : 1#256 <<< k ≠ 0#256 := by
    intro heq
    have := congrArg BitVec.toNat heq
    simp [hpow] at this
  rw [if_neg hne0, if_neg hne0]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_add, hpow, BitVec.toNat_ofNat]
  have hdvd : 2 ^ k ∣ 2 ^ 256 := Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.mod_mod_of_dvd _ hdvd]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hpos) (Nat.pow_lt_pow_right (by omega) hk))).symm

theorem mul_mod_pow2_eq_mulmod (a b : Word) (k : Nat) (hk : k < 256) :
    Binary.mod.eval (Binary.mul.eval a b) (1#256 <<< k) =
      Ternary.mulmod.eval a b (1#256 <<< k) := by
  simp only [Binary.eval, Ternary.eval, evmMod, evmMulmod]
  have hpow : (1#256 <<< k).toNat = 2 ^ k := by
    rw [BitVec.toNat_shiftLeft]
    simp only [BitVec.toNat_ofNat]
    have h1 : 1 % 2 ^ 256 = 1 := rfl
    rw [h1, Nat.one_shiftLeft]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) hk)
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have hne0 : 1#256 <<< k ≠ 0#256 := by
    intro heq
    have := congrArg BitVec.toNat heq
    simp [hpow] at this
  rw [if_neg hne0, if_neg hne0]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_mul, hpow, BitVec.toNat_ofNat]
  have hdvd : 2 ^ k ∣ 2 ^ 256 := Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.mod_mod_of_dvd _ hdvd]
  exact (Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ hpos) (Nat.pow_lt_pow_right (by omega) hk))).symm

theorem sub_add_self_cancel (a b : Word) :
    Binary.sub.eval a (Binary.add.eval a b) = Binary.sub.eval 0#256 b ∧
    Binary.sub.eval a (Binary.add.eval b a) = Binary.sub.eval 0#256 b := by
  simp only [Binary.eval]
  constructor <;> bv_omega

end Compiler.Algebraic.RuleList
