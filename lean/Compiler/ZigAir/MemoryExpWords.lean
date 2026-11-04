/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.BitwiseProofs
import Compiler.ZigAir.MemoryAirLaws
import Contract.Interaction.WordPower

/-! Connect the captured unsigned scalar operations to the existing EVM word
specification. These are interpretation laws, not native-code refinement. -/
namespace Compiler.ZigAir.MemoryExp
open Memory MemoryAir

abbrev Word := BitVec 256
abbrev wordType : Ty := .scalar (.int false 256)
def number (w : Word) : Value := .scalar (.int false 256 w.toNat)
def slot (address : Address) : Value := .pointer (.pointer true false wordType) address
def unitRef : Ref := .constant (.scalar .unit)

theorem number_valid (w : Word) : (number w).valid = true :=
  Scalar.unsigned_nat_valid _ _ w.isLt

theorem number_typed (w : Word) : (number w).hasType wordType = true := by
  simpa [Value.hasType, number, Value.type, Scalar.Value.type] using number_valid w

theorem local_ref (env : Env) (id : Nat) (value : Value)
    (found : env id = some value) (valid : value.valid = true) :
    (Ref.local id).eval env = .ok value := by
  simp [Ref.eval_local, found, valid]

theorem scalar_word (env : Env) (id : Nat) (w : Word)
    (found : env id = some (number w)) :
    (Scalar.Ref.local id).eval (scalarEnv env) = .ok (.int false 256 w.toNat) := by
  have valid := number_valid w
  change (Scalar.Value.int false 256 w.toNat).valid = true at valid
  simp [Scalar.Ref.eval, scalarEnv, found, number, valid]

theorem load_word (args : List Value) (env : Env) (state : State) (id : Nat)
    (address : Address) (w : Word) (found : env id = some (slot address))
    (read : load state (slot address) = .ok (number w)) :
    (Prim.load (.local id)).eval args env state = (.ok (number w), state) := by
  rw [Prim.eval_load, local_ref env id _ found rfl]
  simpa only [bind, Except.bind] using congrArg (fun x => (x, state)) read

theorem multiply_eval (left right : Scalar.Ref) (args : List Value) (env : Env) (state : State)
    (a b : Word) (ha : left.eval (scalarEnv env) = .ok (.int false 256 a.toNat))
    (hb : right.eval (scalarEnv env) = .ok (.int false 256 b.toNat)) :
    (Prim.scalar (.arithmetic .mul .wrapping left right)).eval args env state =
      (.ok (number (a * b)), state) := by
  rw [Prim.eval_scalar]
  simp [Scalar.Prim.eval, ha, hb, bind, Except.bind, Scalar.integer, Scalar.normalize,
    Scalar.Arithmetic.eval, number, BitVec.toNat_mul, Int.natCast_mul]

theorem parity_eval (ref : Scalar.Ref) (args : List Value) (env : Env) (state : State)
    (w : Word) (read : ref.eval (scalarEnv env) = .ok (.int false 256 w.toNat)) :
    (Prim.scalar (.bitAnd ref (.constant (.int false 256 1)))).eval args env state =
      (.ok (number (w &&& 1)), state) := by
  rw [Prim.eval_scalar, Scalar.bitAnd_eval ref (.constant (.int false 256 1)) [] (scalarEnv env)
    w.toNat 1 256 read rfl]
  simp [number, BitVec.toNat_and]

theorem halve_eval (ref : Scalar.Ref) (args : List Value) (env : Env) (state : State)
    (w : Word) (read : ref.eval (scalarEnv env) = .ok (.int false 256 w.toNat)) :
    (Prim.scalar (.shiftRight ref (.constant (.int false 8 1)))).eval args env state =
      (.ok (number (w >>> 1)), state) := by
  rw [Prim.eval_scalar, Scalar.shiftRight_eval ref (.constant (.int false 8 1)) [] (scalarEnv env)
    w.toNat 1 256 read rfl (by decide)]
  simp [number, BitVec.toNat_ushiftRight]

theorem nonzero_eval (ref : Scalar.Ref) (args : List Value) (env : Env) (state : State)
    (w : Word) (read : ref.eval (scalarEnv env) = .ok (.int false 256 w.toNat)) :
    (Prim.scalar (.comparison .ne ref (.constant (.int false 256 0)))).eval args env state =
      (.ok (.scalar (.bool (decide (w ≠ 0)))), state) := by
  have zero : w.toNat = 0 ↔ w = 0 := by
    constructor <;> intro h
    · exact BitVec.eq_of_toNat_eq h
    · simp [h]
  rw [Prim.eval_scalar]
  simp only [Scalar.Prim.eval, read, bind, Except.bind]
  simp [Scalar.Ref.eval, Scalar.Value.valid,
    Scalar.Ty.contains, Scalar.Ty.lower, Scalar.Ty.upper, Scalar.Comparison.eval, zero]

def nextResult (base exponent result : Word) : Word :=
  if exponent &&& 1 ≠ 0 then result * base else result

theorem halve_decreases (w : Word) (nonzero : w ≠ 0) : (w >>> 1).toNat < w.toNat := by
  have positive : 0 < w.toNat := by
    have : w.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
    omega
  simpa [BitVec.toNat_ushiftRight] using Scalar.shiftRight_one_decreases w.toNat positive

theorem power_step (base exponent result : Word) (nonzero : exponent ≠ 0) :
    nextResult base exponent result * Contract.Interaction.WordPower.pow (base * base) (exponent >>> 1).toNat =
      result * Contract.Interaction.WordPower.pow base exponent.toNat := by
  have positive : exponent.toNat ≠ 0 := fun h => nonzero (BitVec.eq_of_toNat_eq h)
  have parity : exponent &&& 1 = 0 ↔ exponent.toNat % 2 = 0 := by
    rw [← BitVec.toNat_inj]
    simp [BitVec.toNat_and]
  conv => rhs; rw [Contract.Interaction.WordPower.pow, dif_neg positive]
  simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.reducePow, nextResult]
  by_cases even : exponent.toNat % 2 = 0
  · have zero := parity.mpr even
    simp only [zero, ne_eq, not_true_eq_false, ↓reduceIte, if_pos even]
  · have odd : exponent &&& 1 ≠ 0 := fun h => even (parity.mp h)
    simp only [if_pos odd, if_neg even, BitVec.mul_assoc]

end Compiler.ZigAir.MemoryExp
