/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.Generated

/-! These theorems execute the generated production AIR over every valid input.
They do not assume that unchecked casts or arithmetic succeed: the semantics
checks those obligations on the selected control path. Source validity and
native backend preservation remain separate obligations. -/
namespace Compiler.ZigAir
open Scalar

theorem u2s_correct (x : Int) (lo : 0 ≤ x) (hi : x < 2 ^ 256) :
    Generated.u2s.run [.int false 256 x] =
      .ok (.int true 256 (if x < 2 ^ 255 then x else x - 2 ^ 256)) := by
  by_cases sign : x < 2 ^ 255
  · have signedLower : -(2 ^ 255 : Int) ≤ x := by omega
    simp only [Int.reducePow] at lo hi sign signedLower ⊢
    simp [Generated.u2s, Program.run, Code.eval, Control.Code.eval, controlSemantics, Outcome.ofControl, Prim.eval,
      Ref.eval, Control.Env.set, Value.hasType, Value.type, Value.valid, Ty.contains,
      Ty.lower, Ty.upper, integer, Comparison.eval, bind, Except.bind,
      lo, hi, sign, signedLower]
  · have signLower : (2 ^ 255 : Int) ≤ x := by omega
    have remainderUpper : x - 2 ^ 255 < (2 ^ 255 : Int) := by omega
    have remainderLower : -(2 ^ 255 : Int) ≤ x - 2 ^ 255 := by omega
    have unsignedUpper : x - 2 ^ 255 < (2 ^ 256 : Int) := by omega
    have resultLower : -(2 ^ 255 : Int) ≤ -(2 ^ 255) + (x - 2 ^ 255) := by omega
    have resultUpper : -(2 ^ 255) + (x - 2 ^ 255) < (2 ^ 255 : Int) := by omega
    simp only [Int.reducePow] at lo hi sign signLower remainderUpper remainderLower unsignedUpper resultLower resultUpper ⊢
    simp [Generated.u2s, Program.run, Code.eval, Control.Code.eval, controlSemantics, Outcome.ofControl, Prim.eval,
      Ref.eval, Control.Env.set, Value.hasType, Value.type, Value.valid, Ty.contains,
      Ty.lower, Ty.upper, integer, Arithmetic.eval, Comparison.eval, bind, Except.bind,
      lo, hi, sign, signLower, remainderUpper, remainderLower, unsignedUpper, resultLower, resultUpper]
    omega

theorem s2u_correct (x : Int) (lo : -(2 ^ 255) ≤ x) (hi : x < 2 ^ 255) :
    Generated.s2u.run [.int true 256 x] =
      .ok (.int false 256 (if x < 0 then x + 2 ^ 256 else x)) := by
  by_cases sign : x < 0
  · have negative : ¬ 0 ≤ x := by omega
    have offsetLower : 0 ≤ x - -(2 ^ 255 : Int) := by omega
    have offsetSignedUpper : x - -(2 ^ 255 : Int) < 2 ^ 255 := by omega
    have offsetSignedLower : -(2 ^ 255 : Int) ≤ x - -(2 ^ 255 : Int) := by omega
    have offsetUnsignedUpper : x - -(2 ^ 255 : Int) < 2 ^ 256 := by omega
    have resultLower : 0 ≤ (2 ^ 255 : Int) + (x - -(2 ^ 255)) := by omega
    have resultUpper : (2 ^ 255 : Int) + (x - -(2 ^ 255)) < 2 ^ 256 := by omega
    simp only [Int.reducePow, Int.sub_neg] at lo hi offsetLower offsetSignedUpper offsetSignedLower offsetUnsignedUpper resultLower resultUpper ⊢
    simp [Generated.s2u, Program.run, Code.eval, Control.Code.eval, controlSemantics, Outcome.ofControl, Prim.eval,
      Ref.eval, Control.Env.set, Value.hasType, Value.type, Value.valid, Ty.contains,
      Ty.lower, Ty.upper, integer, Arithmetic.eval, Comparison.eval, bind, Except.bind,
      lo, hi, sign, negative, offsetLower, offsetSignedUpper, offsetSignedLower, offsetUnsignedUpper, resultLower, resultUpper]
    omega
  · have nonnegative : 0 ≤ x := by omega
    have unsignedUpper : x < (2 ^ 256 : Int) := by omega
    simp only [Int.reducePow] at lo hi unsignedUpper ⊢
    simp [Generated.s2u, Program.run, Code.eval, Control.Code.eval, controlSemantics, Outcome.ofControl, Prim.eval,
      Ref.eval, Control.Env.set, Value.hasType, Value.type, Value.valid, Ty.contains,
      Ty.lower, Ty.upper, integer, Comparison.eval, bind, Except.bind,
      lo, hi, sign, nonnegative, unsignedUpper]

end Compiler.ZigAir
