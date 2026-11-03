/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Algebraic.Proofs

/-! A sound, incomplete normalizer for translation validation. It derives facts
from expressions; no fact or transformation claim supplied by Zig is trusted.
Fuel bounds checking work. Exhausting it returns an equivalent expression and
can lose acceptance, never establish an invalid equality. -/
namespace Compiler.Validation
open Contract.Yul Compiler.Algebraic

deriving instance DecidableEq for Expression

def constant : Expression → Option Word
  | .literal value => some (BitVec.ofNat 256 value)
  | _ => none

def facts (a b : Expression) : Facts := {
  left := constant a, right := constant b, equal := decide (a = b)
}

theorem constant_sound (e : Expression) (value : Word) (known : constant e = some value)
    (storage : Word → Word) (ctx : Contract.Context) (locals : String → Word) :
    e.eval storage ctx locals = value := by
  cases e <;> simp only [constant, Option.some.injEq, reduceCtorEq] at known
  subst value
  rfl

theorem facts_reliable (a b : Expression) (storage : Word → Word)
    (ctx : Contract.Context) (locals : String → Word) :
    (facts a b).Reliable (a.eval storage ctx locals) (b.eval storage ctx locals) := by
  constructor
  · exact fun value known => constant_sound a value known storage ctx locals
  · exact fun value known => constant_sound b value known storage ctx locals
  · intro equal
    simp only [facts, decide_eq_true_eq] at equal
    subst b
    rfl

def rewrite (op : Binary) (a b : Expression) : Expression :=
  match constant a, constant b with
  | some x, some y => .literal (op.eval x y).toNat
  | _, _ =>
    match select productionRules op .constants (facts a b) with
    | some replacement => replacement.expression a b
    | none =>
      match select productionRules op .equal (facts a b) with
      | some replacement => replacement.expression a b
      | none => .binary op a b

theorem rewrite_sound (op : Binary) (a b : Expression) (storage : Word → Word)
    (ctx : Contract.Context) (locals : String → Word) :
    (rewrite op a b).eval storage ctx locals = (Expression.binary op a b).eval storage ctx locals := by
  unfold rewrite
  split
  next x y hx hy =>
    simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [constant_sound a x hx storage ctx locals, constant_sound b y hy storage ctx locals]
  all_goals
    split
    next replacement selected =>
      exact (production_expression_sound op .constants (facts a b) a b storage ctx locals
        (facts_reliable a b storage ctx locals) replacement selected).symm
    next =>
      split
      next replacement selected =>
        exact (production_expression_sound op .equal (facts a b) a b storage ctx locals
          (facts_reliable a b storage ctx locals) replacement selected).symm
      next => rfl

/-- The ordering heuristic need not be injective or complete for soundness.
It merely chooses an orientation for operations proved commutative. -/
def commute : Binary → Bool
  | .add | .mul | .and | .or | .xor | .eq => true
  | _ => false

theorem commute_sound (op : Binary) (admitted : commute op = true) (a b : Word) :
    op.eval a b = op.eval b a := by
  cases op <;> simp only [commute, reduceCtorEq] at admitted
  · exact BitVec.add_comm a b
  · exact BitVec.mul_comm a b
  · exact BitVec.and_comm a b
  · exact BitVec.or_comm a b
  · exact BitVec.xor_comm a b
  · exact congrArg boolWord Bool.beq_comm

def ordered (op : Binary) (a b : Expression) : Expression :=
  if commute op && (compare a.render b.render == .gt) then rewrite op b a else rewrite op a b

theorem ordered_sound (op : Binary) (a b : Expression) (storage : Word → Word)
    (ctx : Contract.Context) (locals : String → Word) :
    (ordered op a b).eval storage ctx locals = (Expression.binary op a b).eval storage ctx locals := by
  unfold ordered
  split
  next swapped =>
    rw [rewrite_sound]
    simp only [Bool.and_eq_true] at swapped
    exact commute_sound op swapped.1 _ _
  next => exact rewrite_sound op a b storage ctx locals

/-- This extension discharges the actual `RuleList.reassociate` artifact
obligation. It groups constants for its five pure word operations; neither
production rewrite choices nor native graph facts are trusted by the checker. -/
def regroupable : Binary → Bool
  | .add | .mul | .and | .or | .xor => true
  | _ => false

theorem regroupable_commutes (op : Binary) (admitted : regroupable op = true) : commute op = true := by
  cases op <;> simp_all [regroupable, commute]

theorem regroupable_assoc (op : Binary) (admitted : regroupable op = true) (a b c : Word) :
    op.eval (op.eval a b) c = op.eval a (op.eval b c) := by
  cases op <;> simp only [regroupable, Bool.false_eq_true] at admitted
  · exact BitVec.add_assoc a b c
  · exact BitVec.mul_assoc a b c
  · exact BitVec.and_assoc a b c
  · exact BitVec.or_assoc a b c
  · exact BitVec.xor_assoc a b c

def constantParts (op : Binary) : Expression → Option (Word × Expression)
  | .binary nested a b =>
    if op = nested then
      match constant a, constant b with
      | some value, _ => some (value, b)
      | _, some value => some (value, a)
      | _, _ => none
    else none
  | _ => none

theorem constantParts_sound (op : Binary) (admitted : regroupable op = true)
    (e rest : Expression) (value : Word) (found : constantParts op e = some (value, rest))
    (storage : Word → Word) (ctx : Contract.Context) (locals : String → Word) :
    e.eval storage ctx locals = op.eval value (rest.eval storage ctx locals) := by
  cases e <;> simp only [constantParts, reduceCtorEq] at found
  rename_i nested a b
  split at found
  next same =>
    subst nested
    split at found
    next x hx =>
      cases found
      exact congrArg (fun y => op.eval y (rest.eval storage ctx locals)) (constant_sound a value hx storage ctx locals)
    next x hx _ =>
      cases found
      rw [Expression.eval, constant_sound b value hx storage ctx locals]
      exact commute_sound op (regroupable_commutes op admitted) _ _
    next => contradiction
  next => contradiction

def mergeConstant (op : Binary) (value : Word) (rest other : Expression) : Expression :=
  match constant other with
  | some outer => ordered op (.literal (op.eval value outer).toNat) rest
  | none => ordered op (.literal value.toNat) (ordered op rest other)

theorem mergeConstant_sound (op : Binary) (admitted : regroupable op = true)
    (value : Word) (rest other : Expression)
    (storage : Word → Word) (ctx : Contract.Context) (locals : String → Word) :
    (mergeConstant op value rest other).eval storage ctx locals =
      op.eval (op.eval value (rest.eval storage ctx locals)) (other.eval storage ctx locals) := by
  unfold mergeConstant
  split
  next outer known =>
    simp only [ordered_sound, Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [constant_sound other outer known storage ctx locals, regroupable_assoc op admitted,
      commute_sound op (regroupable_commutes op admitted) outer (rest.eval storage ctx locals),
      ← regroupable_assoc op admitted]
  next =>
    simp only [ordered_sound, Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact (regroupable_assoc op admitted _ _ _).symm

def regroup (op : Binary) (a b : Expression) : Expression :=
  if regroupable op then
    match constantParts op a with
    | some (value, rest) => mergeConstant op value rest b
    | none =>
      match constantParts op b with
      | some (value, rest) => mergeConstant op value rest a
      | none => ordered op a b
  else ordered op a b

theorem regroup_sound (op : Binary) (a b : Expression) (storage : Word → Word)
    (ctx : Contract.Context) (locals : String → Word) :
    (regroup op a b).eval storage ctx locals = (Expression.binary op a b).eval storage ctx locals := by
  unfold regroup
  split
  next admitted =>
    split
    next value rest found =>
      rw [mergeConstant_sound op admitted, Expression.eval,
        constantParts_sound op admitted a rest value found storage ctx locals]
    next =>
      split
      next value rest found =>
        rw [mergeConstant_sound op admitted, Expression.eval,
          constantParts_sound op admitted b rest value found storage ctx locals]
        exact commute_sound op (regroupable_commutes op admitted) _ _
      next => exact ordered_sound op a b storage ctx locals
  next => exact ordered_sound op a b storage ctx locals

def reduce : Expression → Expression
  | .literal value => .literal (BitVec.ofNat 256 value).toNat
  | .unary op (.literal value) => .literal (op.eval (BitVec.ofNat 256 value)).toNat
  | .unary .bitnot (.unary .bitnot arg) => arg
  | .binary .shl (.literal count) b =>
    if 256 ≤ (BitVec.ofNat 256 count).toNat then .literal 0 else ordered .shl (.literal count) b
  | .binary .shr (.literal count) b =>
    if 256 ≤ (BitVec.ofNat 256 count).toNat then .literal 0 else ordered .shr (.literal count) b
  | .binary op a b => regroup op a b
  | e => e

theorem reduce_sound (e : Expression) (storage : Word → Word)
    (ctx : Contract.Context) (locals : String → Word) :
    (reduce e).eval storage ctx locals = e.eval storage ctx locals := by
  unfold reduce
  split
  · simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · simp only [Expression.eval, Unary.eval, BitVec.not_not]
  · split
    next wide =>
      have below : ¬ (BitVec.ofNat 256 _).toNat < 256 := Nat.not_lt.mpr wide
      simp only [Expression.eval, Binary.eval, below, ↓reduceIte]
      rfl
    next => exact ordered_sound _ _ _ storage ctx locals
  · split
    next wide =>
      have below : ¬ (BitVec.ofNat 256 _).toNat < 256 := Nat.not_lt.mpr wide
      simp only [Expression.eval, Binary.eval, below, ↓reduceIte]
      rfl
    next => exact ordered_sound _ _ _ storage ctx locals
  · exact regroup_sound _ _ _ storage ctx locals
  · rfl

def normalize : Nat → Expression → Expression
  | 0, e => e
  | fuel + 1, e =>
    let children := match e with
      | .unary op a => .unary op (normalize fuel a)
      | .binary op a b => .binary op (normalize fuel a) (normalize fuel b)
      | _ => e
    let changed := reduce children
    if changed = children then children else normalize fuel changed

theorem normalize_sound (fuel : Nat) (e : Expression) (storage : Word → Word)
    (ctx : Contract.Context) (locals : String → Word) :
    (normalize fuel e).eval storage ctx locals = e.eval storage ctx locals := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
    cases e <;> simp only [normalize] <;> split <;>
      simp only [ih, reduce_sound, Expression.eval]

def equivalent (fuel : Nat) (a b : Expression) : Bool := decide (normalize fuel a = normalize fuel b)

theorem equivalent_sound (fuel : Nat) (a b : Expression) (accepted : equivalent fuel a b = true)
    (storage : Word → Word) (ctx : Contract.Context) (locals : String → Word) :
    a.eval storage ctx locals = b.eval storage ctx locals := by
  simp only [equivalent, decide_eq_true_eq] at accepted
  rw [← normalize_sound fuel a, ← normalize_sound fuel b, accepted]

end Compiler.Validation
