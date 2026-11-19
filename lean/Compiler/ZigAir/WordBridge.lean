/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.NumericProofs
import Contract.Yul.Expression

/-! Connect the actual generated conversions to the independent EVM word
representation used by the frontend, optimizer and validation proofs. This
bridge concerns values; it introduces no native backend or memory assumption. -/
namespace Compiler.ZigAir
open Scalar Contract.Yul

theorem u2s_word (word : Word) :
    Generated.u2s.run [.int false 256 word.toNat] = .ok (.int true 256 word.toInt) := by
  have bound := word.isLt
  rw [u2s_correct _ (by omega) (by omega)]
  have meaning := BitVec.toInt_eq_toNat_cond word
  simp only [Nat.reducePow] at meaning
  split <;> split at meaning <;> simp_all <;> omega

theorem s2u_word (word : Word) :
    Generated.s2u.run [.int true 256 word.toInt] = .ok (.int false 256 word.toNat) := by
  have lower := BitVec.le_toInt word
  have upper := BitVec.toInt_lt (x := word)
  have bound := word.isLt
  rw [s2u_correct _ (by simpa using lower) (by simpa using upper)]
  have meaning := BitVec.toInt_eq_toNat_cond word
  simp only [Nat.reducePow] at meaning
  split <;> split at meaning <;> simp_all <;> omega

private theorem sequence_success (first : Result) (next : Value → Result) (x y : Value)
    (left : first = .ok x) (right : next x = .ok y) : (first >>= next) = .ok y := by
  rw [left]
  exact right

theorem unsigned_roundtrip (word : Word) :
    (Generated.u2s.run [.int false 256 word.toNat] >>= fun value => Generated.s2u.run [value]) =
      .ok (.int false 256 word.toNat) := by
  exact sequence_success _ _ _ _ (u2s_word word) (s2u_word word)

theorem signed_roundtrip (word : Word) :
    (Generated.s2u.run [.int true 256 word.toInt] >>= fun value => Generated.u2s.run [value]) =
      .ok (.int true 256 word.toInt) := by
  exact sequence_success _ _ _ _ (s2u_word word) (u2s_word word)

end Compiler.ZigAir
