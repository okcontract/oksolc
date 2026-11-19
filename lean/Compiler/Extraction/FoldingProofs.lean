/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.FoldingProgram
import Compiler.Extraction.FoldingBits

namespace Compiler.Extraction.Folding
open Contract.Yul
set_option linter.unusedSimpArgs false
set_option exponentiation.threshold 1024
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

private theorem pure_ok (a : α) : (pure a : Except Fault α) = .ok a := rfl
private theorem bind_ok (a : α) (next : α → Except Fault β) : ((.ok a : Except Fault α) >>= next) = next a := rfl
private theorem map_ok (a : α) (f : α → β) : f <$> (.ok a : Except Fault α) = .ok (f a) := rfl
attribute [local simp] pure_ok bind_ok map_ok

theorem signedDivision_correct (a b : Word) : signedDivision a b = .ok (Op.sdiv.value a b 0) := by
  by_cases zero : b = 0#256
  · simp [signedDivision, Op.value, zero]
  · have zero0 : b ≠ (0 : Word) := zero
    by_cases overflow : a.toInt = -(2 ^ 255) ∧ b.toInt = -1
    · have left : a = BitVec.ofInt 256 (-(2 ^ 255)) := by
        simpa only [BitVec.ofInt_toInt] using congrArg (BitVec.ofInt 256) overflow.1
      simp only [signedDivision, zero0, if_false, overflow, if_true, Op.value]
      simp only [and_self, if_true]
      rw [left]
      congr 1
    · simp only [signedDivision, Zig.divTrunc, Op.value, zero0, overflow, ↓reduceIte]

theorem signedModulo_correct (a b : Word) : signedModulo a b = .ok (Op.smod.value a b 0) := by
  by_cases zero : b = 0#256
  · simp [signedModulo, Op.value, zero]
  · by_cases unit : b.toInt = 1 ∨ b.toInt = -1
    · rcases unit with positive | negative
      · simp [signedModulo, Op.value, zero, positive]
      · simp [signedModulo, Op.value, zero, negative]
    · have notNegative : b.toInt ≠ -1 := fun h => unit (Or.inr h)
      have notPositive : b.toInt ≠ 1 := fun h => unit (Or.inl h)
      simp [signedModulo, Zig.rem, Op.value, zero, unit, notNegative, notPositive]

theorem byteValue_correct (index value : Word) : byteValue index value = .ok (Op.byte.value index value 0) := by
  by_cases large : index.toNat ≥ 32
  · simp [byteValue, Op.value, large, Nat.not_lt.mpr large]
  · have bound : index.toNat < 32 := Nat.lt_of_not_ge large
    have sub : index.toNat ≤ 31 := by omega
    have product : 8 * (31 - index.toNat) < 2 ^ 256 := by omega
    have cast : 8 * (31 - index.toNat) < 2 ^ 8 := by omega
    simp [byteValue, Op.value, large, bound, Zig.checkedSub, sub, Zig.checkedMul, product, Zig.narrow, cast]

theorem shiftLeft_correct (amount value : Word) : shiftLeft amount value = .ok (Op.shl.value amount value 0) := by
  by_cases large : amount.toNat ≥ 256
  · simp [shiftLeft, Op.value, Binary.eval, large, Nat.not_lt.mpr large]
  · have bound : amount.toNat < 256 := Nat.lt_of_not_ge large
    simp [shiftLeft, Op.value, Binary.eval, large, bound, Zig.narrow]

theorem shiftRight_correct (amount value : Word) : shiftRight amount value = .ok (Op.shr.value amount value 0) := by
  by_cases large : amount.toNat ≥ 256
  · simp [shiftRight, Op.value, Binary.eval, large, Nat.not_lt.mpr large]
  · have bound : amount.toNat < 256 := Nat.lt_of_not_ge large
    simp [shiftRight, Op.value, Binary.eval, large, bound, Zig.narrow]

private theorem nonzero_toNat (value : Word) (nonzero : value ≠ 0) : 0 < value.toNat := by
  have : value.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
  omega

theorem addMod_correct (a b m : Word) : addMod a b m = .ok (Op.addmod.value a b m) := by
  by_cases zero : m = 0#256
  · simp [addMod, Op.value, zero]
  · have aBound := a.isLt
    have bBound := b.isLt
    have sum : a.toNat + b.toNat < 2 ^ 257 := by omega
    have remainder : (a.toNat + b.toNat) % m.toNat < 2 ^ 256 :=
      Nat.lt_trans (Nat.mod_lt _ (nonzero_toNat m zero)) m.isLt
    simp [addMod, Op.value, zero, BitVec.toNat_setWidth_of_le (by decide : 256 ≤ 257),
      Zig.checkedAdd, sum, Zig.narrow, remainder]

theorem mulMod_correct (a b m : Word) : mulMod a b m = .ok (Op.mulmod.value a b m) := by
  by_cases zero : m = 0#256
  · simp [mulMod, Op.value, zero]
  · have product : a.toNat * b.toNat < 2 ^ 512 := by
      have h := Nat.mul_lt_mul_of_lt_of_lt a.isLt b.isLt
      simpa using h
    have remainder : (a.toNat * b.toNat) % m.toNat < 2 ^ 256 :=
      Nat.lt_trans (Nat.mod_lt _ (nonzero_toNat m zero)) m.isLt
    simp [mulMod, Op.value, zero, BitVec.toNat_setWidth_of_le (by decide : 256 ≤ 512),
      Zig.checkedMul, product, Zig.narrow, remainder]

theorem powerLoop_correct (fuel : Nat) (base exponent result : Word)
    (bound : exponent.toNat < 2 ^ fuel) :
    powerLoop fuel base exponent result =
      .ok (result * Contract.Interaction.WordPower.pow base exponent.toNat) := by
  induction fuel generalizing base exponent result with
  | zero =>
    have zero : exponent = 0 := by
      apply BitVec.eq_of_toNat_eq
      change exponent.toNat = 0
      simpa using bound
    simp [powerLoop, zero, Contract.Interaction.WordPower.pow_zero]
  | succ fuel ih =>
    by_cases zero : exponent = 0#256
    · simp [powerLoop, zero, Contract.Interaction.WordPower.pow_zero]
    · have zero0 : exponent ≠ (0 : Word) := zero
      have positive := nonzero_toNat exponent zero
      have half : (exponent >>> 1).toNat = exponent.toNat / 2 := by
        simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
      have halfBound : (exponent >>> 1).toNat < 2 ^ fuel := by
        rw [half]
        rw [Nat.pow_succ] at bound
        omega
      have recurrence : Contract.Interaction.WordPower.pow base exponent.toNat =
          if exponent.toNat % 2 = 0 then Contract.Interaction.WordPower.pow (base * base) (exponent.toNat / 2)
          else base * Contract.Interaction.WordPower.pow (base * base) (exponent.toNat / 2) := by
        rw [Contract.Interaction.WordPower.pow]
        simp [Nat.ne_of_gt positive]
      simp only [powerLoop, zero0, if_false, ih _ _ _ halfBound, half, recurrence]
      have parity : (exponent &&& (1 : Word)) = 0 ↔ exponent.toNat % 2 = 0 := by
        rw [← BitVec.toNat_inj]
        simp [BitVec.toNat_and]
      by_cases even : exponent.toNat % 2 = 0
      · simp only [even, parity.mpr even, ne_eq, not_true_eq_false, ↓reduceIte]
      · have odd : (exponent &&& (1 : Word)) ≠ 0 := fun h => even (parity.mp h)
        simp only [even, ↓reduceIte]
        split
        · simp only [BitVec.mul_assoc]
        · rename_i impossible
          exact False.elim (impossible odd)

theorem wrappingPower_correct (base exponent : Word) :
    wrappingPower base exponent = .ok (Op.exp.value base exponent 0) := by
  simpa [wrappingPower, Op.value] using powerLoop_correct 256 base exponent 1 exponent.isLt

theorem signExtend_correct (index value : Word) :
    signExtend index value = .ok (Op.signextend.value index value 0) := by
  by_cases large : index.toNat ≥ 31
  · simp [signExtend, Op.value, large, Nat.not_lt.mpr large]
  · have bound : index.toNat < 31 := by omega
    have product : index.toNat * 8 < 2 ^ 256 := by omega
    have sum : index.toNat * 8 + 7 < 2 ^ 256 := by omega
    have cast : index.toNat * 8 + 7 < 2 ^ 8 := by omega
    have bitBound : index.toNat * 8 + 7 < 256 := by omega
    have high := highBit_toNat (index.toNat * 8 + 7) bitBound
    have sub : 1 ≤ 2 ^ (index.toNat * 8 + 7) := Nat.two_pow_pos _
    simp only [signExtend, Op.value, large, bound, Zig.checkedMul, product, Zig.checkedAdd, sum,
      Zig.narrow, cast, ↓reduceIte, bind_ok, pure_ok, high, Zig.checkedSub, sub]
    apply congrArg Except.ok
    have same := signMask_correct value (index.toNat * 8 + 7) bitBound
    have width : index.toNat * 8 + 7 + 1 = 8 * (index.toNat + 1) := by omega
    rw [width] at same
    exact same

/-- Every admitted opcode computes the specified EVM word, for every input.
Wrong arity returns null before any indexing; arithmetic faults are impossible. -/
theorem folding_correct (op : Op) (args : List Word) :
    run helpers clauses op.opcode args = .ok (op.eval args) := by
  cases args with
  | nil => cases op <;> rfl
  | cons a rest =>
    cases rest with
    | nil => cases op <;> simp [run, clauses, Op.opcode, Op.eval, Op.arity,
        Body.run, argument, primitive, List.mapM, List.mapM.loop, Except.map, Op.value]
    | cons b rest =>
      cases rest with
      | nil =>
        cases op <;> simp [run, clauses, Op.opcode, Op.eval, Op.arity,
          Body.run, argument, primitive, List.mapM, List.mapM.loop, Except.map, helpers,
          signedDivision_correct, signedModulo_correct, wrappingPower_correct,
          byteValue_correct, signExtend_correct, shiftLeft_correct, shiftRight_correct]
        all_goals by_cases zero : b = 0#256 <;> simp [zero, Op.value, Binary.eval, Except.map]
      | cons c rest =>
        cases rest with
        | nil => cases op <;> simp [run, clauses, Op.opcode, Op.eval, Op.arity,
            Body.run, argument, primitive, List.mapM, List.mapM.loop, Except.map, helpers, addMod_correct, mulMod_correct]
        | cons d rest => cases op <;> simp [run, clauses, Op.opcode, Op.eval, Op.arity]

private theorem run_unknown (entries : List Clause) (opcode : BitVec 8) (args : List Word)
    (unknown : ∀ clause ∈ entries, opcode ≠ clause.opcode) :
    run helpers entries opcode args = .ok none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [run, unknown entry (by simp), ↓reduceIte]
    exact ih (fun clause member => unknown clause (by simp [member]))

/-- Unsupported opcodes remain null; they are never silently assigned a value. -/
theorem folding_unknown (opcode : BitVec 8) (args : List Word)
    (unknown : ∀ op : Op, opcode ≠ op.opcode) :
    run helpers clauses opcode args = .ok none := by
  apply run_unknown
  intro clause member
  simp only [clauses, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst clause
  · exact unknown .add
  · exact unknown .mul
  · exact unknown .sub
  · exact unknown .div
  · exact unknown .sdiv
  · exact unknown .mod
  · exact unknown .smod
  · exact unknown .exp
  · exact unknown .not
  · exact unknown .lt
  · exact unknown .gt
  · exact unknown .slt
  · exact unknown .sgt
  · exact unknown .eq
  · exact unknown .iszero
  · exact unknown .and
  · exact unknown .or
  · exact unknown .xor
  · exact unknown .byte
  · exact unknown .addmod
  · exact unknown .mulmod
  · exact unknown .signextend
  · exact unknown .shl
  · exact unknown .shr

theorem folding_wrong_arity (op : Op) (args : List Word) (wrong : args.length ≠ op.arity) :
    run helpers clauses op.opcode args = .ok none := by
  rw [folding_correct]
  simp [Op.eval, wrong]

end Compiler.Extraction.Folding
