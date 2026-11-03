/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryTypeEquality

namespace Compiler.ZigAir.Memory

structure Address where
  allocation : Nat
  offset : Nat := 0
  deriving DecidableEq, Repr

mutual
inductive Value where
  | scalar (value : Scalar.Value)
  | optionalScalar (child : Scalar.Ty) (payload : Option Scalar.Value)
  | pointer (type : Ty) (address : Address)
  | slice (type : Ty) (address : Address) (length : Nat)
  | optionalObject (child : Ty) (layout : Layout) (payload : Option ObjectValue)
  deriving Repr

/-- An evaluated optional payload, not another heap or allocation. Primitive
fields reuse the existing values and their pointer lifetime identities. Record
fields must match the complete ordered declaration; missing fields are invalid.
This register value supplies no byte view into an optional's representation. -/
inductive ObjectValue where
  | leaf (value : Value)
  | fields (values : List (Nat × ObjectValue))
  deriving Repr
end

-- Total structural equality for the nested value vocabulary.
mutual
private def Value.decEq (a b : Value) : Decidable (a = b) :=
  match a, b with
  | .scalar a, .scalar b => decidable_of_iff (a = b) (by simp)
  | .optionalScalar a0 a1, .optionalScalar b0 b1 => decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  | .pointer a0 a1, .pointer b0 b1 => decidable_of_iff (a0 = b0 ∧ a1 = b1) (by simp)
  | .slice a0 a1 a2, .slice b0 b1 b2 => decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  | .optionalObject a0 a1 a2, .optionalObject b0 b1 b2 =>
    letI : Decidable (a2 = b2) := optionalDecEq a2 b2
    decidable_of_iff (a0 = b0 ∧ a1 = b1 ∧ a2 = b2) (by simp)
  | .scalar _, .optionalScalar _ _ | .scalar _, .pointer _ _ | .scalar _, .slice _ _ _ | .scalar _, .optionalObject _ _ _
  | .optionalScalar _ _, .scalar _ | .optionalScalar _ _, .pointer _ _ | .optionalScalar _ _, .slice _ _ _
  | .optionalScalar _ _, .optionalObject _ _ _
  | .pointer _ _, .scalar _ | .pointer _ _, .optionalScalar _ _ | .pointer _ _, .slice _ _ _ | .pointer _ _, .optionalObject _ _ _
  | .slice _ _ _, .scalar _ | .slice _ _ _, .optionalScalar _ _ | .slice _ _ _, .pointer _ _ | .slice _ _ _, .optionalObject _ _ _
  | .optionalObject _ _ _, .scalar _ | .optionalObject _ _ _, .optionalScalar _ _
  | .optionalObject _ _ _, .pointer _ _ | .optionalObject _ _ _, .slice _ _ _ => isFalse (by intro h; cases h)
termination_by structural a

private def ObjectValue.decEq (a b : ObjectValue) : Decidable (a = b) :=
  match a, b with
  | .leaf a, .leaf b =>
    letI : Decidable (a = b) := Value.decEq a b
    decidable_of_iff (a = b) (by simp)
  | .fields a, .fields b =>
    letI : Decidable (a = b) := fieldsDecEq a b
    decidable_of_iff (a = b) (by simp)
  | .leaf _, .fields _ | .fields _, .leaf _ => isFalse (by intro h; cases h)
termination_by structural a

private def optionalDecEq (a b : Option ObjectValue) : Decidable (a = b) :=
  match a, b with
  | none, none => isTrue rfl
  | none, some _ | some _, none => isFalse (by intro h; cases h)
  | some a, some b =>
    letI : Decidable (a = b) := ObjectValue.decEq a b
    decidable_of_iff (a = b) (by simp)
termination_by structural a

private def fieldsDecEq (a b : List (Nat × ObjectValue)) : Decidable (a = b) :=
  match a, b with
  | [], [] => isTrue rfl
  | [], _ :: _ | _ :: _, [] => isFalse (by intro h; cases h)
  | ha :: ta, hb :: tb =>
    letI : Decidable (ha.2 = hb.2) := ObjectValue.decEq ha.2 hb.2
    letI : Decidable (ta = tb) := fieldsDecEq ta tb
    decidable_of_iff (ha.1 = hb.1 ∧ ha.2 = hb.2 ∧ ta = tb) (by simp [Prod.ext_iff, and_assoc])
termination_by structural a
end

instance : DecidableEq Value := Value.decEq
instance : DecidableEq ObjectValue := ObjectValue.decEq

end Compiler.ZigAir.Memory
