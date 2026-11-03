/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypeDefinitions

namespace Compiler.ZigAir.Memory

-- Lean 4.29 cannot derive nested inductive DecidableEq. These total structural
-- decisions retain constructor, permission, nominal identity, layout and every field.
mutual
private def Ty.decEq (a b : Ty) : Decidable (a = b) :=
  match a, b with
  | .scalar a0, .scalar b0 =>
    decidable_of_iff (a0 = b0) (by simp)
  | .optionalScalar a0, .optionalScalar b0 =>
    decidable_of_iff (a0 = b0) (by simp)
  | .optionalObject a0 a1, .optionalObject b0 b1 =>
    letI : Decidable (a0 = b0) := Ty.decEq a0 b0
    decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  | .pointer a0 a1 a2, .pointer b0 b1 b2 =>
    letI : Decidable (a2 = b2) := Ty.decEq a2 b2
    decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  | .slice a0 a1, .slice b0 b1 =>
    letI : Decidable (a1 = b1) := Ty.decEq a1 b1
    decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  | .array a0 a1, .array b0 b1 =>
    letI : Decidable (a1 = b1) := Ty.decEq a1 b1
    decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  | .record a0 a1, .record b0 b1 =>
    decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  | .aggregate a0 a1 a2, .aggregate b0 b1 b2 =>
    letI : Decidable (a2 = b2) := fieldsDecEq a2 b2
    decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  | .scalar _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .scalar _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .scalar _, .array _ _ => isFalse (by intro impossible; cases impossible)
  | .scalar _, .record _ _ => isFalse (by intro impossible; cases impossible)
  | .scalar _, .aggregate _ _ _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .array _ _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .record _ _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .aggregate _ _ _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .array _ _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .record _ _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .aggregate _ _ _ => isFalse (by intro impossible; cases impossible)
  | .array _ _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .array _ _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .array _ _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .array _ _, .record _ _ => isFalse (by intro impossible; cases impossible)
  | .array _ _, .aggregate _ _ _ => isFalse (by intro impossible; cases impossible)
  | .record _ _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .record _ _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .record _ _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .record _ _, .array _ _ => isFalse (by intro impossible; cases impossible)
  | .record _ _, .aggregate _ _ _ => isFalse (by intro impossible; cases impossible)
  | .aggregate _ _ _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .aggregate _ _ _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .aggregate _ _ _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .aggregate _ _ _, .array _ _ => isFalse (by intro impossible; cases impossible)
  | .aggregate _ _ _, .record _ _ => isFalse (by intro impossible; cases impossible)
  | .scalar _, .optionalScalar _ => isFalse (by intro impossible; cases impossible)
  | .optionalScalar _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .optionalScalar _ => isFalse (by intro impossible; cases impossible)
  | .optionalScalar _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .optionalScalar _ => isFalse (by intro impossible; cases impossible)
  | .optionalScalar _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .array _ _, .optionalScalar _ => isFalse (by intro impossible; cases impossible)
  | .optionalScalar _, .array _ _ => isFalse (by intro impossible; cases impossible)
  | .record _ _, .optionalScalar _ => isFalse (by intro impossible; cases impossible)
  | .optionalScalar _, .record _ _ => isFalse (by intro impossible; cases impossible)
  | .aggregate _ _ _, .optionalScalar _ => isFalse (by intro impossible; cases impossible)
  | .optionalScalar _, .aggregate _ _ _ => isFalse (by intro impossible; cases impossible)
  | .scalar _, .optionalObject _ _ => isFalse (by intro impossible; cases impossible)
  | .optionalObject _ _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .optionalScalar _, .optionalObject _ _ => isFalse (by intro impossible; cases impossible)
  | .optionalObject _ _, .optionalScalar _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .optionalObject _ _ => isFalse (by intro impossible; cases impossible)
  | .optionalObject _ _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .optionalObject _ _ => isFalse (by intro impossible; cases impossible)
  | .optionalObject _ _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .array _ _, .optionalObject _ _ => isFalse (by intro impossible; cases impossible)
  | .optionalObject _ _, .array _ _ => isFalse (by intro impossible; cases impossible)
  | .record _ _, .optionalObject _ _ => isFalse (by intro impossible; cases impossible)
  | .optionalObject _ _, .record _ _ => isFalse (by intro impossible; cases impossible)
  | .aggregate _ _ _, .optionalObject _ _ => isFalse (by intro impossible; cases impossible)
  | .optionalObject _ _, .aggregate _ _ _ => isFalse (by intro impossible; cases impossible)
termination_by structural a

private def Field.decEq (a b : Field) : Decidable (a = b) :=
  match a, b with
  | .scalar a0, .scalar b0 =>
    decidable_of_iff (a0 = b0) (by simp)
  | .pointer a0 a1 a2, .pointer b0 b1 b2 =>
    decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  | .slice a0 a1, .slice b0 b1 =>
    decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  | .recordSlice a0 a1 a2, .recordSlice b0 b1 b2 =>
    decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  | .object a0, .object b0 =>
    letI : Decidable (a0 = b0) := Ty.decEq a0 b0
    decidable_of_iff (a0 = b0) (by simp)
  | .scalar _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .scalar _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .scalar _, .recordSlice _ _ _ => isFalse (by intro impossible; cases impossible)
  | .scalar _, .object _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .recordSlice _ _ _ => isFalse (by intro impossible; cases impossible)
  | .pointer _ _ _, .object _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .recordSlice _ _ _ => isFalse (by intro impossible; cases impossible)
  | .slice _ _, .object _ => isFalse (by intro impossible; cases impossible)
  | .recordSlice _ _ _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .recordSlice _ _ _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .recordSlice _ _ _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .recordSlice _ _ _, .object _ => isFalse (by intro impossible; cases impossible)
  | .object _, .scalar _ => isFalse (by intro impossible; cases impossible)
  | .object _, .pointer _ _ _ => isFalse (by intro impossible; cases impossible)
  | .object _, .slice _ _ => isFalse (by intro impossible; cases impossible)
  | .object _, .recordSlice _ _ _ => isFalse (by intro impossible; cases impossible)
termination_by structural a

private def fieldsDecEq (a b : List (Nat × Field)) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by intro impossible; cases impossible)
  | ha :: ta, hb :: tb =>
    letI : Decidable (ha.2 = hb.2) := Field.decEq ha.2 hb.2
    letI : Decidable (ta = tb) := fieldsDecEq ta tb
    decidable_of_iff (ha.1 = hb.1 ∧ ha.2 = hb.2 ∧ ta = tb) (by simp [Prod.ext_iff, and_assoc])
termination_by structural a
end

instance : DecidableEq Ty := Ty.decEq
instance : DecidableEq Field := Field.decEq

end Compiler.ZigAir.Memory
