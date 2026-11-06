/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Yul.Expression

/-! Guard, selection, and replacement model for `src/libevmasm/algebraic_rules.zig`.
Word operations are defined once in `Contract.Yul.Expression`; this layer models
fact-driven algebraic selection over evaluated 256-bit operands. -/
namespace Compiler.Algebraic
open Contract
open Contract.Yul

inductive Guard where
  | left_zero | right_zero | left_one | right_one | left_max | right_max | equal
  deriving DecidableEq, Repr

inductive Replacement where
  | left | right | zero | one | max | not_right | neg_left | neg_right
  | iszero_left | iszero_right | bool_left | bool_right
  deriving DecidableEq, Repr

inductive Stage where
  | constants | equal
  deriving DecidableEq, Repr

structure Rule where
  op : Binary
  guard : Guard
  replacement : Replacement
  deriving DecidableEq, Repr

structure Facts where
  left : Option Word := none
  right : Option Word := none
  equal : Bool := false
  deriving DecidableEq, Repr

structure Facts.Reliable (facts : Facts) (a b : Word) : Prop where
  left : ∀ v, facts.left = some v → a = v
  right : ∀ v, facts.right = some v → b = v
  equal : facts.equal = true → a = b

def Guard.Holds : Guard → Word → Word → Prop
  | .left_zero, a, _ => a = 0
  | .right_zero, _, b => b = 0
  | .left_one, a, _ => a = 1
  | .right_one, _, b => b = 1
  | .left_max, a, _ => a = BitVec.allOnes 256
  | .right_max, _, b => b = BitVec.allOnes 256
  | .equal, a, b => a = b

def Guard.matches (guard : Guard) (facts : Facts) : Bool :=
  match guard with
  | .left_zero => decide (facts.left = some 0)
  | .right_zero => decide (facts.right = some 0)
  | .left_one => decide (facts.left = some 1)
  | .right_one => decide (facts.right = some 1)
  | .left_max => decide (facts.left = some (BitVec.allOnes 256))
  | .right_max => decide (facts.right = some (BitVec.allOnes 256))
  | .equal => facts.equal

def Guard.stage : Guard → Stage
  | .equal => .equal
  | _ => .constants

def Replacement.eval (replacement : Replacement) (a b : Word) : Word :=
  match replacement with
  | .left => a | .right => b | .zero => 0 | .one => 1 | .max => BitVec.allOnes 256
  | .not_right => Unary.bitnot.eval b
  | .neg_left => Binary.sub.eval 0 a | .neg_right => Binary.sub.eval 0 b
  | .iszero_left => Unary.iszero.eval a | .iszero_right => Unary.iszero.eval b
  | .bool_left => Unary.iszero.eval (Unary.iszero.eval a)
  | .bool_right => Unary.iszero.eval (Unary.iszero.eval b)

def Replacement.expression (replacement : Replacement) (a b : Expression) : Expression :=
  match replacement with
  | .left => a | .right => b | .zero => .literal 0 | .one => .literal 1
  | .max => .literal (2^256 - 1)
  | .not_right => .unary .bitnot b
  | .neg_left => .binary .sub (.literal 0) a
  | .neg_right => .binary .sub (.literal 0) b
  | .iszero_left => .unary .iszero a | .iszero_right => .unary .iszero b
  | .bool_left => .unary .iszero (.unary .iszero a)
  | .bool_right => .unary .iszero (.unary .iszero b)

theorem replacement_eval (replacement : Replacement) (a b : Expression)
    (storage : Word → Word) (ctx : Contract.Context) (locals : String → Word) :
    (replacement.expression a b).eval storage ctx locals =
      replacement.eval (a.eval storage ctx locals) (b.eval storage ctx locals) := by
  cases replacement <;> rfl

def Rule.Sound (rule : Rule) : Prop :=
  ∀ a b, rule.guard.Holds a b → rule.op.eval a b = rule.replacement.eval a b

def select (rules : List Rule) (op : Binary) (stage : Stage) (facts : Facts) : Option Replacement :=
  match rules with
  | [] => none
  | rule :: rest =>
    if rule.op = op ∧ rule.guard.stage = stage ∧ rule.guard.matches facts = true then
      some rule.replacement
    else select rest op stage facts

theorem matches_sound (guard : Guard) (facts : Facts) (a b : Word)
    (reliable : facts.Reliable a b) (matched : guard.matches facts = true) :
    guard.Holds a b := by
  cases guard <;> simp only [Guard.matches, decide_eq_true_eq, Guard.Holds] at *
  · exact reliable.left _ matched
  · exact reliable.right _ matched
  · exact reliable.left _ matched
  · exact reliable.right _ matched
  · exact reliable.left _ matched
  · exact reliable.right _ matched
  · exact reliable.equal matched

theorem select_sound (rules : List Rule) (sound : ∀ rule ∈ rules, rule.Sound)
    (op : Binary) (stage : Stage) (facts : Facts) (a b : Word)
    (reliable : facts.Reliable a b) (replacement : Replacement)
    (selected : select rules op stage facts = some replacement) :
    op.eval a b = replacement.eval a b := by
  induction rules with
  | nil => simp [select] at selected
  | cons rule rest ih =>
    simp only [select] at selected
    split at selected
    next matched =>
      obtain ⟨rfl, _, guardMatch⟩ := matched
      cases selected
      exact sound rule (by simp) a b (matches_sound _ _ _ _ reliable guardMatch)
    next =>
      exact ih (fun r hr => sound r (by simp [hr])) selected

end Compiler.Algebraic
