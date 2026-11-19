/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.AssociativeProofs

namespace Compiler.Extraction.SignExtendMask
open Contract.Yul

/-- Independent low-bit mask, with no native cast or arithmetic assumptions. -/
def lowBits (width : Nat) : Word := BitVec.ofNat 256 (2 ^ width - 1)

theorem masked_sign_extension (width : Nat) (mask value : Word)
    (contained : mask &&& lowBits width = mask) :
    mask &&& (value.setWidth width).signExtend 256 = mask &&& value := by
  apply BitVec.eq_of_getLsbD_eq
  intro index valid
  by_cases low : index < width
  · simp only [BitVec.getLsbD_and, BitVec.getLsbD_signExtend,
      BitVec.getLsbD_setWidth, valid, low, decide_true, ↓reduceIte, Bool.true_and]
  · have bit := congrArg (fun word : Word => word.getLsbD index) contained
    have zero : mask.getLsbD index = false := by
      simpa only [BitVec.getLsbD_and, lowBits, BitVec.getLsbD_ofNat,
        Nat.testBit_two_pow_sub_one, valid, low, decide_true, decide_false,
        Bool.and_false, Bool.true_and] using bit.symm
    simp only [BitVec.getLsbD_and, zero, Bool.false_and]

theorem masked_evm_signextend (index mask value : Word) (bound : index.toNat < 31)
    (contained : mask &&& lowBits ((index.toNat + 1) * 8) = mask) :
    mask &&& Folding.Op.signextend.value index value 0 = mask &&& value := by
  have width : 8 * (index.toNat + 1) = (index.toNat + 1) * 8 := by omega
  change mask &&& (if index.toNat < 31 then
    (value.setWidth (8 * (index.toNat + 1))).signExtend 256 else value) = mask &&& value
  rw [if_pos bound, width]
  exact masked_sign_extension ((index.toNat + 1) * 8) mask value contained

end Compiler.Extraction.SignExtendMask
