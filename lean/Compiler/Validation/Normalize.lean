/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Algebraic.Proofs
import Compiler.Algebraic.RuleListProofs

/-! Sound normalizer for translation validation of `ExpressionClasses` + `RuleList`.

All facts are computed directly from Lean expressions; no transformation claim,
constant query, or equivalence assertion from Zig is trusted. Exhausting fuel
returns a semantically equivalent expression and can only lose acceptance, never
certify an invalid rewrite. -/
namespace Compiler.Validation
open Contract Contract.Yul Compiler.Algebraic

deriving instance DecidableEq for Expression

def maxWord : Word := BitVec.allOnes 256
def addressMask : Word := (1#256 <<< 160) - 1#256

def constant : Expression → Option Word
  | .literal value => some (BitVec.ofNat 256 value)
  | _ => none

theorem constant_sound (e : Expression) (value : Word) (known : constant e = some value)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    e.eval storage ctx locals = value := by
  cases e <;> simp only [constant, Option.some.injEq, reduceCtorEq] at known
  subst value
  rfl

def facts (a b : Expression) : Facts := {
  left := constant a, right := constant b, equal := decide (a = b)
}

theorem facts_reliable (a b : Expression) (storage : Word → Word)
    (ctx : Context) (locals : String → Word) :
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
    (ctx : Context) (locals : String → Word) :
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

/-- Commutative orientation heuristic for canonical form. -/
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
    (ctx : Context) (locals : String → Word) :
    (ordered op a b).eval storage ctx locals = (Expression.binary op a b).eval storage ctx locals := by
  unfold ordered
  split
  next swapped =>
    rw [rewrite_sound]
    simp only [Bool.and_eq_true] at swapped
    exact commute_sound op swapped.1 _ _
  next => exact rewrite_sound op a b storage ctx locals

/-- Associative + commutative word operations normalized by constant regrouping. -/
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
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
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
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
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
    (ctx : Context) (locals : String → Word) :
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

/-- Find `k < 256` such that `w = 1 <<< k` when `w` is an exact power of two. -/
private def log2Loop : Nat → Word → Option Nat
  | 0, _ => none
  | n + 1, w =>
    if 255 - n < 256 then
      if w = (1#256 <<< (255 - n)) then some (255 - n) else log2Loop n w
    else none

def exactLog2 (w : Word) : Option Nat := log2Loop 256 w

private theorem log2Loop_sound (n : Nat) (w : Word) (k : Nat)
    (found : log2Loop n w = some k) : k < 256 ∧ w = (1#256 <<< k) := by
  induction n with
  | zero => simp [log2Loop] at found
  | succ n ih =>
    unfold log2Loop at found
    split at found
    next hlt =>
      split at found
      next heq =>
        cases found
        exact ⟨hlt, heq⟩
      next => exact ih found
    next => simp at found

theorem exactLog2_sound (w : Word) (k : Nat) (found : exactLog2 w = some k) :
    k < 256 ∧ w = (1#256 <<< k) :=
  log2Loop_sound 256 w k found

/-- Check whether `e` is a 160-bit address-producing nullary operation. -/
def isAddressExpr : Expression → Bool
  | .nullary _ => true
  | _ => false

theorem isAddressExpr_mask (e : Expression) (h : isAddressExpr e = true)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    Binary.and.eval addressMask (e.eval storage ctx locals) = e.eval storage ctx locals := by
  cases e with
  | nullary op =>
    simp only [Expression.eval, addressMask]
    exact (RuleList.address_mask_idempotent ctx op).2
  | _ => simp [isAddressExpr] at h

/-- Normalize unary procedural rules (`NOT`, `ISZERO` chains and comparisons). -/
def reduceUnary : Unary → Expression → Expression
  | op, .literal value => .literal (op.eval (BitVec.ofNat 256 value)).toNat
  | .bitnot, .unary .bitnot x => x
  | .iszero, .unary .iszero (.unary .iszero x) => .unary .iszero x
  | .iszero, .unary .iszero (.binary .eq a b) => .binary .eq a b
  | .iszero, .unary .iszero (.binary .lt a b) => .binary .lt a b
  | .iszero, .unary .iszero (.binary .slt a b) => .binary .slt a b
  | .iszero, .unary .iszero (.binary .gt a b) => .binary .gt a b
  | .iszero, .unary .iszero (.binary .sgt a b) => .binary .sgt a b
  | .iszero, .binary .xor a b => .binary .eq a b
  | .iszero, .binary .sub a b => .binary .eq a b
  | op, arg => .unary op arg

theorem reduceUnary_sound (op : Unary) (arg : Expression)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    (reduceUnary op arg).eval storage ctx locals = (Expression.unary op arg).eval storage ctx locals := by
  unfold reduceUnary
  split
  · simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact (RuleList.bitnot_bitnot _).symm
  · exact (RuleList.iszero_triple _).symm
  · exact (RuleList.iszero_iszero_eq _ _).symm
  · exact (RuleList.iszero_iszero_lt _ _).symm
  · exact (RuleList.iszero_iszero_slt _ _).symm
  · exact (RuleList.iszero_iszero_gt _ _).symm
  · exact (RuleList.iszero_iszero_sgt _ _).symm
  · exact (RuleList.iszero_xor_eq _ _).symm
  · exact (RuleList.iszero_sub_eq _ _).symm
  · rfl

/-- Normalize ternary constant folding and power-of-two `ADDMOD`/`MULMOD` equivalence. -/
def reduceTernary (op : Ternary) (a b c : Expression) : Expression :=
  match constant a, constant b, constant c with
  | some av, some bv, some cv => .literal (op.eval av bv cv).toNat
  | _, _, _ =>
    match op, constant c with
    | .addmod, some mv =>
      match exactLog2 mv with
      | some k => .binary .and (.binary .add a b) (.literal (((1#256 <<< k) - 1#256).toNat))
      | none => .ternary op a b c
    | .mulmod, some mv =>
      match exactLog2 mv with
      | some k => .binary .and (.binary .mul a b) (.literal (((1#256 <<< k) - 1#256).toNat))
      | none => .ternary op a b c
    | _, _ => .ternary op a b c

theorem reduceTernary_sound (op : Ternary) (a b c : Expression)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    (reduceTernary op a b c).eval storage ctx locals =
      (Expression.ternary op a b c).eval storage ctx locals := by
  unfold reduceTernary
  cases hca : constant a with
  | some av =>
    cases hcb : constant b with
    | some bv =>
      cases hcc : constant c with
      | some cv =>
        simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          constant_sound a av hca storage ctx locals,
          constant_sound b bv hcb storage ctx locals,
          constant_sound c cv hcc storage ctx locals]
      | none =>
        cases op <;> simp
    | none =>
      cases op <;> cases hcc : constant c <;> simp only []
      · rename_i mv
        cases hk : exactLog2 mv with
        | none => rfl
        | some k =>
          obtain ⟨hlt, heq⟩ := exactLog2_sound mv k hk
          simp only [Expression.eval, constant_sound c mv hcc storage ctx locals, heq,
            BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [← RuleList.mod_pow2_eq_and _ k hlt]
          exact RuleList.add_mod_pow2_eq_addmod _ _ k hlt
      · rename_i mv
        cases hk : exactLog2 mv with
        | none => rfl
        | some k =>
          obtain ⟨hlt, heq⟩ := exactLog2_sound mv k hk
          simp only [Expression.eval, constant_sound c mv hcc storage ctx locals, heq,
            BitVec.ofNat_toNat, BitVec.setWidth_eq]
          rw [← RuleList.mod_pow2_eq_and _ k hlt]
          exact RuleList.mul_mod_pow2_eq_mulmod _ _ k hlt
  | none =>
    cases op <;> cases hcc : constant c <;> simp only []
    · rename_i mv
      cases hk : exactLog2 mv with
      | none => rfl
      | some k =>
        obtain ⟨hlt, heq⟩ := exactLog2_sound mv k hk
        simp only [Expression.eval, constant_sound c mv hcc storage ctx locals, heq,
          BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rw [← RuleList.mod_pow2_eq_and _ k hlt]
        exact RuleList.add_mod_pow2_eq_addmod _ _ k hlt
    · rename_i mv
      cases hk : exactLog2 mv with
      | none => rfl
      | some k =>
        obtain ⟨hlt, heq⟩ := exactLog2_sound mv k hk
        simp only [Expression.eval, constant_sound c mv hcc storage ctx locals, heq,
          BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rw [← RuleList.mod_pow2_eq_and _ k hlt]
        exact RuleList.mul_mod_pow2_eq_mulmod _ _ k hlt

/-- Per-opcode helpers for `RuleList` binary procedural rewrites. -/
def reduceByte (a x : Expression) : Option Expression :=
  match constant a with
  | none => none
  | some nw =>
    if nw = 31#256 then some (.binary .and x (.literal 0xff))
    else if 32 ≤ nw.toNat then some (.literal 0)
    else match x with
      | .binary .shl s inner =>
        match constant s with
        | some sw =>
          if sw.toNat % 8 = 0 ∧ nw.toNat ≤ 32 ∧ sw.toNat ≤ 256 then
            some (.binary .byte (.literal (nw.toNat + sw.toNat / 8)) inner)
          else none
        | none => none
      | .binary .shr s inner =>
        match constant s with
        | some sw =>
          if nw.toNat < sw.toNat / 8 then some (.literal 0)
          else if sw.toNat % 8 = 0 ∧ nw.toNat < 32 ∧ sw.toNat ≤ 256 then
            some (.binary .byte (.literal (nw.toNat - sw.toNat / 8)) inner)
          else none
        | none => none
      | _ => none

theorem reduceByte_sound (a x out : Expression) (h : reduceByte a x = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary .byte a x).eval storage ctx locals := by
  unfold reduceByte at h
  cases hca : constant a with
  | none => simp [hca] at h
  | some nw =>
    simp only [hca] at h
    have haw := constant_sound a nw hca storage ctx locals
    split at h
    · next h31 =>
      cases h
      simp only [Expression.eval, haw, h31]
      exact (RuleList.byte_31_eq_and _).symm
    · split at h
      · next hge32 =>
        cases h
        simp only [Expression.eval, haw]
        exact (RuleList.byte_ge_32 nw _ hge32).symm
      · cases x with
        | binary xop s inner =>
          cases xop with
          | shl =>
            cases hcs : constant s with
            | none => simp [hcs] at h
            | some sw =>
              simp only [hcs] at h
              split at h <;> simp at h
              next cond =>
                rcases cond with ⟨hmod, hnle, hsle⟩
                subst out
                simp only [Expression.eval, haw, constant_sound s sw hcs storage ctx locals]
                exact (RuleList.byte_shl nw sw _ hmod hnle hsle).symm
          | shr =>
            cases hcs : constant s with
            | none => simp [hcs] at h
            | some sw =>
              simp only [hcs] at h
              split at h
              · next hlt =>
                cases h
                simp only [Expression.eval, haw, constant_sound s sw hcs storage ctx locals]
                exact (RuleList.byte_shr_zero nw sw _ hlt).symm
              · next hnlt =>
                split at h <;> simp at h
                next cond =>
                  rcases cond with ⟨hmod, hnlt32, hsle⟩
                  subst out
                  simp only [Expression.eval, haw, constant_sound s sw hcs storage ctx locals]
                  exact (RuleList.byte_shr nw sw _ hmod hnlt32 hsle (Nat.le_of_not_lt hnlt)).symm
          | _ => simp at h
        | _ => simp at h

def reduceShl (a x : Expression) : Option Expression :=
  match constant a with
  | none => none
  | some nw =>
    if 256 ≤ nw.toNat then some (.literal 0)
    else match x with
      | .binary .shl b inner =>
        match constant b with
        | some bw =>
          if 256 - min bw.toNat 256 ≤ nw.toNat then some (.literal 0)
          else some (.binary .shl (.literal (nw.toNat + bw.toNat)) inner)
        | none => none
      | .binary .shr b inner =>
        match constant b with
        | some bw =>
          if 256 ≤ bw.toNat then some (.literal 0)
          else
            let mask := ((maxWord >>> bw.toNat) <<< nw.toNat).toNat
            let shifted :=
              if nw.toNat < bw.toNat then Expression.binary .shr (.literal (bw.toNat - nw.toNat)) inner
              else if bw.toNat < nw.toNat then Expression.binary .shl (.literal (nw.toNat - bw.toNat)) inner
              else inner
            some (.binary .and shifted (.literal mask))
        | none => none
      | .binary .signextend d inner =>
        match constant d with
        | some dw =>
          if nw.toNat % 8 = 0 ∧ dw.toNat ≤ 32 then
            some (.binary .signextend (.literal (nw.toNat / 8 + dw.toNat))
              (.binary .shl (.literal nw.toNat) inner))
          else none
        | none => none
      | .binary .and ia ib =>
        match constant ia, constant ib with
        | some mask, _ =>
          some (.binary .and (.binary .shl (.literal nw.toNat) ib) (.literal (mask <<< nw.toNat).toNat))
        | _, some mask =>
          some (.binary .and (.binary .shl (.literal nw.toNat) ia) (.literal (mask <<< nw.toNat).toNat))
        | _, _ => none
      | _ => none

theorem reduceShl_sound (a x out : Expression) (h : reduceShl a x = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary .shl a x).eval storage ctx locals := by
  unfold reduceShl at h
  cases hca : constant a with
  | none => simp [hca] at h
  | some nw =>
    simp only [hca] at h
    have haw := constant_sound a nw hca storage ctx locals
    split at h
    · next hge256 =>
      cases h
      simp only [Expression.eval, haw]
      exact (RuleList.shl_ge_256 nw _ hge256).symm
    · next hn256 =>
      have hnlt : nw.toNat < 256 := Nat.lt_of_not_ge hn256
      cases x with
      | binary xop b inner =>
        cases xop with
        | shl =>
          cases hcb : constant b with
          | none => simp [hcb] at h
          | some bw =>
            simp only [hcb] at h
            have hbw := constant_sound b bw hcb storage ctx locals
            have hshl := RuleList.shl_nested nw bw (inner.eval storage ctx locals)
            split at h
            · next hover =>
              cases h
              simp only [Expression.eval, haw, hbw]
              rw [hshl, if_pos hover]
            · next hnover =>
              cases h
              simp only [Expression.eval, haw, hbw]
              rw [hshl, if_neg hnover]
        | shr =>
          cases hcb : constant b with
          | none => simp [hcb] at h
          | some bw =>
            simp only [hcb] at h
            have hbw := constant_sound b bw hcb storage ctx locals
            split at h
            · next hbge =>
              cases h
              simp only [Expression.eval, haw, hbw]
              rw [RuleList.shr_ge_256 bw _ hbge]
              simp [Binary.eval, evmShl_eq_shiftLeft]
            · next hbnge =>
              cases h
              have hblt : bw.toNat < 256 := Nat.lt_of_not_ge hbnge
              have hcomb := RuleList.shl_of_shr_combine nw bw (inner.eval storage ctx locals) hnlt hblt
              simp only [Expression.eval, haw, hbw, maxWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
              split
              · next hlt => simpa [hlt] using hcomb.symm
              · next hge =>
                split
                · next hgt => simpa [hge, hgt] using hcomb.symm
                · next hng => simpa [hge, hng] using hcomb.symm
        | signextend =>
          cases hcd : constant b with
          | none => simp [hcd] at h
          | some dw =>
            simp only [hcd] at h
            split at h <;> simp at h
            next cond =>
              rcases cond with ⟨hmod, hdle⟩
              subst out
              simp only [Expression.eval, haw, constant_sound b dw hcd storage ctx locals,
                BitVec.ofNat_toNat, BitVec.setWidth_eq]
              exact (RuleList.shl_signextend nw dw _ hmod (Nat.le_of_lt hnlt) hdle).symm
        | «and» =>
          simp only [] at h
          cases hcb : constant b with
          | some mask =>
            simp only [hcb, Option.some.injEq] at h; subst out
            simp only [Expression.eval, haw, BitVec.ofNat_toNat, BitVec.setWidth_eq,
              constant_sound b mask hcb storage ctx locals]
            have hc : Binary.and.eval mask (inner.eval storage ctx locals) =
                Binary.and.eval (inner.eval storage ctx locals) mask := BitVec.and_comm _ _
            rw [hc]
            exact (RuleList.shl_and_const nw _ mask hnlt).symm
          | none =>
            cases hci : constant inner with
            | some mask =>
              simp only [hcb, hci, Option.some.injEq] at h; subst out
              simp only [Expression.eval, haw, BitVec.ofNat_toNat, BitVec.setWidth_eq,
                constant_sound inner mask hci storage ctx locals]
              exact (RuleList.shl_and_const nw _ mask hnlt).symm
            | none => simp [hcb, hci] at h
        | _ => simp at h
      | _ => simp at h

def reduceShr (a x : Expression) : Option Expression :=
  match constant a with
  | none => none
  | some nw =>
    if 256 ≤ nw.toNat then some (.literal 0)
    else match x with
      | .binary .shr b inner =>
        match constant b with
        | some bw =>
          if 256 - min bw.toNat 256 ≤ nw.toNat then some (.literal 0)
          else some (.binary .shr (.literal (nw.toNat + bw.toNat)) inner)
        | none => none
      | .binary .shl b inner =>
        match constant b with
        | some bw =>
          if 256 ≤ bw.toNat then some (.literal 0)
          else
            let mask := ((maxWord <<< bw.toNat) >>> nw.toNat).toNat
            let shifted :=
              if nw.toNat < bw.toNat then Expression.binary .shl (.literal (bw.toNat - nw.toNat)) inner
              else if bw.toNat < nw.toNat then Expression.binary .shr (.literal (nw.toNat - bw.toNat)) inner
              else inner
            some (.binary .and shifted (.literal mask))
        | none => none
      | .binary .and ia ib =>
        match constant ia, constant ib with
        | some mask, _ =>
          some (.binary .and (.binary .shr (.literal nw.toNat) ib) (.literal (mask >>> nw.toNat).toNat))
        | _, some mask =>
          some (.binary .and (.binary .shr (.literal nw.toNat) ia) (.literal (mask >>> nw.toNat).toNat))
        | _, _ => none
      | _ => none

theorem reduceShr_sound (a x out : Expression) (h : reduceShr a x = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary .shr a x).eval storage ctx locals := by
  unfold reduceShr at h
  cases hca : constant a with
  | none => simp [hca] at h
  | some nw =>
    simp only [hca] at h
    have haw := constant_sound a nw hca storage ctx locals
    split at h
    · next hge256 =>
      cases h
      simp only [Expression.eval, haw]
      exact (RuleList.shr_ge_256 nw _ hge256).symm
    · next hn256 =>
      have hnlt : nw.toNat < 256 := Nat.lt_of_not_ge hn256
      cases x with
      | binary xop b inner =>
        cases xop with
        | shr =>
          cases hcb : constant b with
          | none => simp [hcb] at h
          | some bw =>
            simp only [hcb] at h
            have hbw := constant_sound b bw hcb storage ctx locals
            have hshr := RuleList.shr_nested nw bw (inner.eval storage ctx locals)
            split at h
            · next hover =>
              cases h
              simp only [Expression.eval, haw, hbw]
              rw [hshr, if_pos hover]
            · next hnover =>
              cases h
              simp only [Expression.eval, haw, hbw]
              rw [hshr, if_neg hnover]
        | shl =>
          cases hcb : constant b with
          | none => simp [hcb] at h
          | some bw =>
            simp only [hcb] at h
            have hbw := constant_sound b bw hcb storage ctx locals
            split at h
            · next hbge =>
              cases h
              simp only [Expression.eval, haw, hbw]
              rw [RuleList.shl_ge_256 bw _ hbge]
              simp [Binary.eval, evmShr_eq_ushiftRight]
            · next hbnge =>
              cases h
              have hblt : bw.toNat < 256 := Nat.lt_of_not_ge hbnge
              have hcomb := RuleList.shr_of_shl_combine nw bw (inner.eval storage ctx locals) hnlt hblt
              simp only [Expression.eval, haw, hbw, maxWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
              split
              · next hlt => simpa [hlt] using hcomb.symm
              · next hge =>
                split
                · next hgt => simpa [hge, hgt] using hcomb.symm
                · next hng => simpa [hge, hng] using hcomb.symm
        | «and» =>
          simp only [] at h
          cases hcb : constant b with
          | some mask =>
            simp only [hcb, Option.some.injEq] at h; subst out
            simp only [Expression.eval, haw, BitVec.ofNat_toNat, BitVec.setWidth_eq,
              constant_sound b mask hcb storage ctx locals]
            have hc : Binary.and.eval mask (inner.eval storage ctx locals) =
                Binary.and.eval (inner.eval storage ctx locals) mask := BitVec.and_comm _ _
            rw [hc]
            exact (RuleList.shr_and_const nw _ mask hnlt).symm
          | none =>
            cases hci : constant inner with
            | some mask =>
              simp only [hcb, hci, Option.some.injEq] at h; subst out
              simp only [Expression.eval, haw, BitVec.ofNat_toNat, BitVec.setWidth_eq,
                constant_sound inner mask hci storage ctx locals]
              exact (RuleList.shr_and_const nw _ mask hnlt).symm
            | none => simp [hcb, hci] at h
        | _ => simp at h
      | _ => simp at h

def reduceSignextend (b x : Expression) : Option Expression :=
  match constant b with
  | some bw =>
    if 31 ≤ bw.toNat then some x
    else match x with
      | .binary .shr s inner =>
        match constant s with
        | some sw =>
          if sw.toNat % 8 = 0 ∧ sw.toNat ≤ 256 ∧ (256 - sw.toNat) / 8 = bw.toNat + 1 then
            some (.binary .sar (.literal sw.toNat) inner)
          else none
        | none => none
      | .binary .signextend a inner =>
        match constant a with
        | some aw =>
          some (.binary .signextend (.literal (if bw.toNat ≤ aw.toNat then bw.toNat else aw.toNat)) inner)
        | none => none
      | _ => none
  | none =>
    match x with
    | .binary .signextend b2 inner =>
      if b = b2 then some (.binary .signextend b inner) else none
    | _ => none

theorem reduceSignextend_sound (b x out : Expression) (h : reduceSignextend b x = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary .signextend b x).eval storage ctx locals := by
  unfold reduceSignextend at h
  cases hcb : constant b with
  | some bw =>
    simp only [hcb] at h
    have hbw := constant_sound b bw hcb storage ctx locals
    split at h
    · next hge31 =>
      cases h
      simp only [Expression.eval, hbw]
      exact (RuleList.signextend_ge_31 bw _ hge31).symm
    · next hnge31 =>
      have hblt31 : bw.toNat < 31 := Nat.lt_of_not_ge hnge31
      cases x with
      | binary xop s inner =>
        cases xop with
        | shr =>
          cases hcs : constant s with
          | none => simp [hcs] at h
          | some sw =>
            simp only [hcs] at h
            split at h <;> simp at h
            next cond =>
              rcases cond with ⟨hmod, hsle, hrel⟩
              subst out
              simp only [Expression.eval, hbw, constant_sound s sw hcs storage ctx locals,
                BitVec.ofNat_toNat, BitVec.setWidth_eq]
              exact (RuleList.signextend_shr_eq_sar bw sw _ hmod hsle (by omega) hrel).symm
        | signextend =>
          cases hca : constant s with
          | none => simp [hca] at h
          | some aw =>
            simp only [hca, Option.some.injEq] at h
            subst out
            have haw := constant_sound s aw hca storage ctx locals
            have hmin := RuleList.signextend_nested_min bw aw (inner.eval storage ctx locals)
            simp only [Expression.eval, hbw, haw]
            split
            · next hle =>
              simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              simpa [hle] using hmin.symm
            · next hgt =>
              simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
              simpa [hgt] using hmin.symm
        | _ => simp at h
      | _ => simp at h
  | none =>
    simp only [hcb] at h
    cases x with
    | binary xop b2 inner =>
      cases xop <;> simp at h
      rcases h with ⟨rfl, rfl⟩
      exact (RuleList.signextend_idempotent _ _).symm
    | _ => simp at h

def reduceExp (a x : Expression) : Option Expression :=
  match constant a with
  | none => none
  | some bw =>
    if bw = 0#256 then some (.unary .iszero x)
    else if bw = 1#256 then some (.literal 1)
    else if bw = 2#256 then some (.binary .shl x (.literal 1))
    else if bw = maxWord then
      some (.binary .sub (.unary .iszero (.binary .and x (.literal 1))) (.binary .and x (.literal 1)))
    else none

theorem reduceExp_sound (a x out : Expression) (h : reduceExp a x = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary .exp a x).eval storage ctx locals := by
  unfold reduceExp at h
  cases hca : constant a with
  | none => simp [hca] at h
  | some bw =>
    simp only [hca] at h
    have haw := constant_sound a bw hca storage ctx locals
    split at h
    · next h0 =>
      cases h; simp only [Expression.eval, haw, h0]
      exact (RuleList.exp_zero_base _).symm
    · split at h
      · next h1 =>
        cases h; simp only [Expression.eval, haw, h1]
        exact (RuleList.exp_one_base _).symm
      · split at h
        · next h2 =>
          cases h; simp only [Expression.eval, haw, h2]
          exact (RuleList.exp_two_base _).symm
        · split at h <;> simp at h
          next hmax =>
            subst out; simp only [Expression.eval, haw, hmax, maxWord]
            exact (RuleList.exp_max_base _).symm

private def isShlOne : Expression → Option Expression
  | .binary .shl y oneExpr => if constant oneExpr = some 1#256 then some y else none
  | _ => none

private theorem isShlOne_sound (e y : Expression) (h : isShlOne e = some y)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    e.eval storage ctx locals = Binary.shl.eval (y.eval storage ctx locals) 1#256 := by
  unfold isShlOne at h
  cases e with
  | binary bop sh oneExpr =>
    cases bop with
    | shl =>
      simp only [] at h
      by_cases hone : constant oneExpr = some 1#256
      · simp only [hone, ↓reduceIte, Option.some.injEq] at h
        subst y
        simp only [Expression.eval, constant_sound oneExpr _ hone storage ctx locals]
      · simp [hone] at h
    | _ => simp at h
  | _ => simp at h

def reduceMulDivMod (op : Binary) (a b : Expression) : Option Expression :=
  match op with
  | .mul =>
    match constant a with
    | some cv =>
      match exactLog2 cv with
      | some k => some (.binary .shl (.literal k) b)
      | none => none
    | none =>
      match constant b with
      | some cv =>
        match exactLog2 cv with
        | some k => some (.binary .shl (.literal k) a)
        | none => none
      | none =>
        match isShlOne b with
        | some y => some (.binary .shl y a)
        | none =>
          match isShlOne a with
          | some y2 => some (.binary .shl y2 b)
          | none => none
  | .div =>
    match constant b with
    | some cv =>
      match exactLog2 cv with
      | some k => some (.binary .shr (.literal k) a)
      | none => none
    | none =>
      match isShlOne b with
      | some y => some (.binary .shr y a)
      | none => none
  | .mod =>
    match constant b with
    | some cv =>
      match exactLog2 cv with
      | some k => some (.binary .and a (.literal (((1#256 <<< k) - 1#256).toNat)))
      | none => none
    | none => none
  | _ => none

theorem reduceMulDivMod_sound (op : Binary) (a b out : Expression)
    (h : reduceMulDivMod op a b = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary op a b).eval storage ctx locals := by
  cases op <;> simp only [reduceMulDivMod] at h
  case mul =>
    cases hca : constant a with
    | some cv =>
      simp only [hca] at h
      cases hk : exactLog2 cv <;> simp [hk] at h
      rename_i k; subst out
      obtain ⟨hlt, heq⟩ := exactLog2_sound cv k hk
      simp only [Expression.eval, constant_sound a cv hca storage ctx locals, heq]
      exact ((RuleList.mul_pow2_eq_shl _ k hlt).2).symm
    | none =>
      simp only [hca] at h
      cases hcb : constant b with
      | some cv =>
        simp only [hcb] at h
        cases hk : exactLog2 cv <;> simp [hk] at h
        rename_i k; subst out
        obtain ⟨hlt, heq⟩ := exactLog2_sound cv k hk
        simp only [Expression.eval, constant_sound b cv hcb storage ctx locals, heq]
        exact ((RuleList.mul_pow2_eq_shl _ k hlt).1).symm
      | none =>
        simp only [hcb] at h
        cases hsb : isShlOne b with
        | some y =>
          simp only [hsb, Option.some.injEq] at h; subst out
          simp only [Expression.eval, isShlOne_sound b y hsb storage ctx locals]
          exact ((RuleList.mul_shl_one_eq_shl _ _).1).symm
        | none =>
          simp only [hsb] at h
          cases hsa : isShlOne a with
          | some y2 =>
            simp only [hsa, Option.some.injEq] at h; subst out
            simp only [Expression.eval, isShlOne_sound a y2 hsa storage ctx locals]
            exact ((RuleList.mul_shl_one_eq_shl _ _).2).symm
          | none => simp [hsa] at h
  case div =>
    cases hcb : constant b with
    | some cv =>
      simp only [hcb] at h
      cases hk : exactLog2 cv <;> simp [hk] at h
      rename_i k; subst out
      obtain ⟨hlt, heq⟩ := exactLog2_sound cv k hk
      simp only [Expression.eval, constant_sound b cv hcb storage ctx locals, heq]
      exact (RuleList.div_pow2_eq_shr _ k hlt).symm
    | none =>
      simp only [hcb] at h
      cases hsb : isShlOne b with
      | some y =>
        simp only [hsb, Option.some.injEq] at h; subst out
        simp only [Expression.eval, isShlOne_sound b y hsb storage ctx locals]
        exact (RuleList.div_shl_one_eq_shr _ _).symm
      | none => simp [hsb] at h
  case mod =>
    cases hcb : constant b with
    | some cv =>
      simp only [hcb] at h
      cases hk : exactLog2 cv with
      | none => simp [hk] at h
      | some k =>
        simp only [hk, Option.some.injEq] at h; subst out
        obtain ⟨hlt, heq⟩ := exactLog2_sound cv k hk
        simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          constant_sound b cv hcb storage ctx locals, heq]
        exact (RuleList.mod_pow2_eq_and _ k hlt).symm
    | none => simp [hcb] at h
  all_goals simp at h

private theorem literal_neg_eval (w : Word) (storage : Word → Word)
    (ctx : Context) (locals : String → Word) :
    (Expression.literal ((0#256 - w).toNat)).eval storage ctx locals = 0#256 - w := by
  simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq]

private def reduceSubRhs (lhs rhs : Expression) : Option Expression :=
  match rhs with
  | .binary .add ra rb =>
    if lhs = ra then some (.binary .sub (.literal 0) rb)
    else if lhs = rb then some (.binary .sub (.literal 0) ra)
    else match constant ra, constant rb with
      | some rav, _ => some (.binary .add (.binary .sub lhs rb) (.literal (0#256 - rav).toNat))
      | _, some rbv => some (.binary .add (.binary .sub lhs ra) (.literal (0#256 - rbv).toNat))
      | _, _ => none
  | .binary .sub ra rb =>
    if lhs = ra then some rb
    else match constant ra, constant rb with
      | _, some rbv => some (.binary .add (.binary .sub lhs ra) (.literal rbv.toNat))
      | some rav, _ => some (.binary .add (.binary .add lhs rb) (.literal (0#256 - rav).toNat))
      | _, _ => none
  | _ => none

private theorem reduceSubRhs_sound (lhs rhs out : Expression)
    (h : reduceSubRhs lhs rhs = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary .sub lhs rhs).eval storage ctx locals := by
  unfold reduceSubRhs at h
  cases rhs with
  | binary rop ra rb =>
    cases rop with
    | add =>
      simp only [] at h
      by_cases heq1 : lhs = ra
      · simp only [heq1, ↓reduceIte, Option.some.injEq] at h
        subst out ra
        exact ((RuleList.sub_add_self_cancel _ _).1).symm
      · simp only [heq1, ↓reduceIte] at h
        by_cases heq2 : lhs = rb
        · simp only [heq2, ↓reduceIte, Option.some.injEq] at h
          subst out rb
          exact ((RuleList.sub_add_self_cancel _ _).2).symm
        · simp only [heq2, ↓reduceIte] at h
          cases hcra : constant ra with
          | some rav =>
            simp only [hcra, Option.some.injEq] at h; subst out
            change Binary.add.eval (Binary.sub.eval (lhs.eval storage ctx locals) (rb.eval storage ctx locals))
              ((Expression.literal ((0#256 - rav).toNat)).eval storage ctx locals) =
              Binary.sub.eval (lhs.eval storage ctx locals)
                (Binary.add.eval (ra.eval storage ctx locals) (rb.eval storage ctx locals))
            rw [literal_neg_eval, constant_sound ra rav hcra storage ctx locals]
            have hc : Binary.add.eval rav (rb.eval storage ctx locals) =
                Binary.add.eval (rb.eval storage ctx locals) rav := BitVec.add_comm _ _
            rw [hc]
            exact ((RuleList.sub_nested_reassociate _ _ rav).2.1).symm
          | none =>
            cases hcrb : constant rb with
            | some rbv =>
              simp only [hcra, hcrb, Option.some.injEq] at h; subst out
              change Binary.add.eval (Binary.sub.eval (lhs.eval storage ctx locals) (ra.eval storage ctx locals))
                ((Expression.literal ((0#256 - rbv).toNat)).eval storage ctx locals) =
                Binary.sub.eval (lhs.eval storage ctx locals)
                  (Binary.add.eval (ra.eval storage ctx locals) (rb.eval storage ctx locals))
              rw [literal_neg_eval, constant_sound rb rbv hcrb storage ctx locals]
              exact ((RuleList.sub_nested_reassociate _ _ rbv).2.1).symm
            | none => simp [hcra, hcrb] at h
    | sub =>
      simp only [] at h
      by_cases heq1 : lhs = ra
      · simp only [heq1, ↓reduceIte, Option.some.injEq] at h
        subst out ra
        exact (RuleList.sub_sub_cancel _ _).symm
      · simp only [heq1, ↓reduceIte] at h
        cases hcrb : constant rb with
        | some rbv =>
          cases hcra : constant ra <;> simp only [hcra, hcrb, Option.some.injEq] at h <;> subst out
          all_goals
            simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
              constant_sound rb rbv hcrb storage ctx locals]
            exact ((RuleList.sub_nested_reassociate _ _ rbv).2.2.2.2.1).symm
        | none =>
          cases hcra : constant ra with
          | some rav =>
            simp only [hcra, hcrb, Option.some.injEq] at h; subst out
            change Binary.add.eval (Binary.add.eval (lhs.eval storage ctx locals) (rb.eval storage ctx locals))
              ((Expression.literal ((0#256 - rav).toNat)).eval storage ctx locals) =
              Binary.sub.eval (lhs.eval storage ctx locals)
                (Binary.sub.eval (ra.eval storage ctx locals) (rb.eval storage ctx locals))
            rw [literal_neg_eval, constant_sound ra rav hcra storage ctx locals]
            exact ((RuleList.sub_nested_reassociate _ _ rav).2.2.2.2.2).symm
          | none => simp [hcra, hcrb] at h
    | _ => simp at h
  | _ => simp at h

def reduceSubClean (lhs rhs : Expression) : Option Expression :=
  match constant rhs with
  | some cv => some (.binary .add lhs (.literal (0#256 - cv).toNat))
  | none =>
    match lhs with
    | .binary .add a b =>
      if a = rhs then some b
      else if b = rhs then some a
      else match constant a, constant b with
        | some av, _ => some (.binary .add (.binary .sub b rhs) (.literal av.toNat))
        | _, some bv => some (.binary .add (.binary .sub a rhs) (.literal bv.toNat))
        | _, _ => reduceSubRhs (.binary .add a b) rhs
    | .binary .sub a b =>
      match constant a, constant b with
      | _, some bv => some (.binary .sub (.binary .sub a rhs) (.literal bv.toNat))
      | some av, _ => some (.binary .sub (.literal av.toNat) (.binary .add b rhs))
      | _, _ => reduceSubRhs (.binary .sub a b) rhs
    | _ => reduceSubRhs lhs rhs

theorem reduceSubClean_sound (lhs rhs out : Expression)
    (h : reduceSubClean lhs rhs = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary .sub lhs rhs).eval storage ctx locals := by
  unfold reduceSubClean at h
  cases hcr : constant rhs with
  | some cv =>
    simp only [hcr, Option.some.injEq] at h; subst out
    change Binary.add.eval (lhs.eval storage ctx locals)
      ((Expression.literal ((0#256 - cv).toNat)).eval storage ctx locals) =
      Binary.sub.eval (lhs.eval storage ctx locals) (rhs.eval storage ctx locals)
    rw [literal_neg_eval, constant_sound rhs cv hcr storage ctx locals]
    exact (RuleList.sub_const_eq_add_neg _ cv).symm
  | none =>
    simp only [hcr] at h
    cases lhs with
    | binary lop a b =>
      cases lop with
      | add =>
        simp only [] at h
        by_cases heq1 : a = rhs
        · simp only [heq1, ↓reduceIte, Option.some.injEq] at h
          subst out a
          exact (RuleList.add_sub_cancel_left _ _).symm
        · simp only [heq1, ↓reduceIte] at h
          by_cases heq2 : b = rhs
          · simp only [heq2, ↓reduceIte, Option.some.injEq] at h
            subst out b
            exact (RuleList.add_sub_cancel_right _ _).symm
          · simp only [heq2, ↓reduceIte] at h
            cases hca : constant a with
            | some av =>
              simp only [hca, Option.some.injEq] at h; subst out
              simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
                constant_sound a av hca storage ctx locals]
              have hc : Binary.add.eval av (b.eval storage ctx locals) =
                  Binary.add.eval (b.eval storage ctx locals) av := BitVec.add_comm _ _
              rw [hc]
              exact ((RuleList.sub_nested_reassociate _ _ av).1).symm
            | none =>
              cases hcb : constant b with
              | some bv =>
                simp only [hca, hcb, Option.some.injEq] at h; subst out
                simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
                  constant_sound b bv hcb storage ctx locals]
                exact ((RuleList.sub_nested_reassociate _ _ bv).1).symm
              | none =>
                simp only [hca, hcb] at h
                exact reduceSubRhs_sound (.binary .add a b) rhs out h storage ctx locals
      | sub =>
        simp only [] at h
        cases hcb : constant b with
        | some bv =>
          cases hca : constant a <;> simp only [hca, hcb, Option.some.injEq] at h <;> subst out
          all_goals
            simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
              constant_sound b bv hcb storage ctx locals]
            exact ((RuleList.sub_nested_reassociate _ _ bv).2.2.1).symm
        | none =>
          cases hca : constant a with
          | some av =>
            simp only [hca, hcb, Option.some.injEq] at h; subst out
            simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
              constant_sound a av hca storage ctx locals]
            exact ((RuleList.sub_nested_reassociate _ _ av).2.2.2.1).symm
          | none =>
            simp only [hca, hcb] at h
            exact reduceSubRhs_sound (.binary .sub a b) rhs out h storage ctx locals
      | _ => exact reduceSubRhs_sound _ rhs out h storage ctx locals
    | _ => exact reduceSubRhs_sound _ rhs out h storage ctx locals

def reduceRuleListBinary (op : Binary) (a b : Expression) : Option Expression :=
  match op with
  | .byte => reduceByte a b
  | .shl => reduceShl a b
  | .shr => reduceShr a b
  | .signextend => reduceSignextend a b
  | .exp => reduceExp a b
  | .mul | .div | .mod => reduceMulDivMod op a b
  | .sub => reduceSubClean a b
  | _ => none

theorem reduceRuleListBinary_sound (op : Binary) (a b out : Expression)
    (h : reduceRuleListBinary op a b = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary op a b).eval storage ctx locals := by
  cases op <;> simp only [reduceRuleListBinary] at h
  case byte => exact reduceByte_sound a b out h storage ctx locals
  case shl => exact reduceShl_sound a b out h storage ctx locals
  case shr => exact reduceShr_sound a b out h storage ctx locals
  case signextend => exact reduceSignextend_sound a b out h storage ctx locals
  case exp => exact reduceExp_sound a b out h storage ctx locals
  case mul => exact reduceMulDivMod_sound .mul a b out h storage ctx locals
  case div => exact reduceMulDivMod_sound .div a b out h storage ctx locals
  case mod => exact reduceMulDivMod_sound .mod a b out h storage ctx locals
  case sub => exact reduceSubClean_sound a b out h storage ctx locals
  all_goals simp at h

/-- Alternating mask distribution `(inner & innerMask | alt) & outerMask` for `AND`. -/
def reduceAlternatingBranch (cand alt : Expression) (outerMask : Word) : Option Expression :=
  match cand with
  | .binary .and ia ib =>
    match constant ia, constant ib with
    | some innerMask, _ =>
      some (.binary .or
        (.binary .and ib (.literal (innerMask &&& outerMask).toNat))
        (.binary .and alt (.literal outerMask.toNat)))
    | _, some innerMask =>
      some (.binary .or
        (.binary .and ia (.literal (innerMask &&& outerMask).toNat))
        (.binary .and alt (.literal outerMask.toNat)))
    | _, _ => none
  | _ => none

theorem reduceAlternatingBranch_sound (cand alt out : Expression) (outerMask : Word)
    (h : reduceAlternatingBranch cand alt outerMask = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals =
      Binary.and.eval outerMask (Binary.or.eval (cand.eval storage ctx locals) (alt.eval storage ctx locals)) := by
  unfold reduceAlternatingBranch at h
  cases cand with
  | binary cop ia ib =>
    cases cop with
    | «and» =>
      simp only [] at h
      cases hcia : constant ia with
      | some innerMask =>
        simp only [hcia, Option.some.injEq] at h; subst out
        simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
          constant_sound ia innerMask hcia storage ctx locals]
        have hc1 : Binary.and.eval innerMask (ib.eval storage ctx locals) =
            Binary.and.eval (ib.eval storage ctx locals) innerMask := BitVec.and_comm _ _
        have hc2 : Binary.and.eval outerMask
              (Binary.or.eval (Binary.and.eval (ib.eval storage ctx locals) innerMask) (alt.eval storage ctx locals)) =
            Binary.and.eval
              (Binary.or.eval (Binary.and.eval (ib.eval storage ctx locals) innerMask) (alt.eval storage ctx locals))
              outerMask := BitVec.and_comm _ _
        rw [hc1, hc2]
        exact (RuleList.distribute_alternating_mask _ _ innerMask outerMask).symm
      | none =>
        cases hcib : constant ib with
        | some innerMask =>
          simp only [hcia, hcib, Option.some.injEq] at h; subst out
          simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
            constant_sound ib innerMask hcib storage ctx locals]
          have hc2 : Binary.and.eval outerMask
                (Binary.or.eval (Binary.and.eval (ia.eval storage ctx locals) innerMask) (alt.eval storage ctx locals)) =
              Binary.and.eval
                (Binary.or.eval (Binary.and.eval (ia.eval storage ctx locals) innerMask) (alt.eval storage ctx locals))
                outerMask := BitVec.and_comm _ _
          rw [hc2]
          exact (RuleList.distribute_alternating_mask _ _ innerMask outerMask).symm
        | none => simp [hcia, hcib] at h
    | _ => simp at h
  | _ => simp at h

def reduceAndPair (x y : Expression) : Option Expression :=
  if constant x = some 0xff#256 then
    match y with
    | .binary .byte bi bv =>
      if constant bi = some 31#256 then none else some (.binary .byte bi bv)
    | _ => none
  else if constant x = some addressMask ∧ isAddressExpr y = true then some y
  else
    match y with
    | .unary .bitnot nx =>
      if nx = x then some (.literal 0)
      else match x with
        | .unary .bitnot mx => some (.unary .bitnot (.binary .or mx nx))
        | _ => none
    | .binary .or a b =>
      if x = a ∨ x = b then some x
      else
        match constant x with
        | some outerMask =>
          match reduceAlternatingBranch a b outerMask with
          | some out => some out
          | none => reduceAlternatingBranch b a outerMask
        | none => none
    | .binary .and a b =>
      if x = a ∨ x = b then some (.binary .and a b) else none
    | .binary .shr amtExpr val =>
      match constant x, constant amtExpr with
      | some mask, some aw =>
        if aw.toNat ≤ 256 then
          let coverage := if aw.toNat = 256 then 0#256 else maxWord >>> aw.toNat
          if (mask &&& coverage) = coverage then some (.binary .shr (.literal aw.toNat) val)
          else none
        else none
      | _, _ => none
    | .binary .shl s1 v1 =>
      match constant x with
      | some mask =>
        match constant s1 with
        | some aw =>
          if aw.toNat ≤ 256 then
            let coverage := if aw.toNat = 256 then 0#256 else maxWord <<< aw.toNat
            if (mask &&& coverage) = coverage then some (.binary .shl (.literal aw.toNat) v1)
            else none
          else none
        | none => none
      | none =>
        match x with
        | .binary .shl s2 v2 =>
          if s1 = s2 then some (.binary .shl s1 (.binary .and v2 v1)) else none
        | _ => none
    | .binary .signextend bExpr val =>
      match constant x, constant bExpr with
      | some mask, some bw =>
        if bw.toNat < 31 then
          let lowMask := (1#256 <<< ((bw.toNat + 1) * 8)) - 1#256
          if (mask &&& lowMask) = mask then some (.binary .and (.literal mask.toNat) val)
          else none
        else none
      | _, _ => none
    | _ => none

theorem reduceAndPair_sound (x y out : Expression) (h : reduceAndPair x y = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary .and x y).eval storage ctx locals := by
  unfold reduceAndPair at h
  by_cases h0xff : constant x = some 0xff#256
  · simp only [h0xff, ↓reduceIte] at h
    cases y with
    | binary bop bi bv =>
      cases bop <;> simp at h
      rcases h with ⟨_, rfl⟩
      simp only [Expression.eval, constant_sound x _ h0xff storage ctx locals]
      have hc : Binary.and.eval 0xff#256 (Binary.byte.eval (bi.eval storage ctx locals) (bv.eval storage ctx locals)) =
          Binary.and.eval (Binary.byte.eval (bi.eval storage ctx locals) (bv.eval storage ctx locals)) 0xff#256 :=
        BitVec.and_comm _ _
      rw [hc]
      exact (RuleList.and_byte_mask _ _).symm
    | _ => simp at h
  · simp only [h0xff, ↓reduceIte] at h
    by_cases haddr : constant x = some addressMask ∧ isAddressExpr y = true
    · simp only [haddr, and_self, ↓reduceIte, Option.some.injEq] at h
      subst out
      simp only [Expression.eval, constant_sound x _ haddr.1 storage ctx locals]
      exact (isAddressExpr_mask y haddr.2 storage ctx locals).symm
    · simp only [haddr, ↓reduceIte] at h
      cases y with
      | unary uop nx =>
        cases uop <;> try simp at h
        by_cases hnx : nx = x
        · simp only [hnx, ↓reduceIte, Option.some.injEq] at h
          subst out nx
          exact (RuleList.and_complement _).symm
        · simp only [hnx, ↓reduceIte] at h
          cases x with
          | unary xuop mx =>
            cases xuop <;> simp at h
            subst out
            exact (RuleList.demorgan_not_or _ _).symm
          | _ => simp at h
      | binary bop a b =>
        cases bop with
        | «or» =>
          simp only [] at h
          by_cases hab : x = a ∨ x = b
          · simp only [hab, ↓reduceIte, Option.some.injEq] at h
            subst out
            rcases hab with rfl | rfl
            · exact (RuleList.and_absorb_or_left _ _).symm
            · exact (RuleList.and_absorb_or_right _ _).symm
          · simp only [hab, ↓reduceIte] at h
            cases hcx : constant x with
            | none => simp [hcx] at h
            | some outerMask =>
              simp only [hcx] at h
              have hx := constant_sound x outerMask hcx storage ctx locals
              cases ha : reduceAlternatingBranch a b outerMask with
              | some res =>
                simp only [ha, Option.some.injEq] at h; subst out
                simp only [Expression.eval, hx]
                exact reduceAlternatingBranch_sound a b res outerMask ha storage ctx locals
              | none =>
                simp only [ha] at h
                simp only [Expression.eval, hx]
                rw [reduceAlternatingBranch_sound b a out outerMask h storage ctx locals]
                exact congrArg (Binary.and.eval outerMask) (BitVec.or_comm _ _)
        | «and» =>
          simp only [] at h
          by_cases hab : x = a ∨ x = b
          · simp only [hab, ↓reduceIte, Option.some.injEq] at h
            subst out
            simp only [Expression.eval]
            rcases hab with rfl | rfl
            · have hc : Binary.and.eval (x.eval storage ctx locals)
                  (Binary.and.eval (x.eval storage ctx locals) (b.eval storage ctx locals)) =
                Binary.and.eval (Binary.and.eval (x.eval storage ctx locals) (b.eval storage ctx locals))
                  (x.eval storage ctx locals) := BitVec.and_comm _ _
              rw [hc]
              exact (RuleList.and_drop_repeated_left _ _).symm
            · have hc : Binary.and.eval (x.eval storage ctx locals)
                  (Binary.and.eval (a.eval storage ctx locals) (x.eval storage ctx locals)) =
                Binary.and.eval (Binary.and.eval (a.eval storage ctx locals) (x.eval storage ctx locals))
                  (x.eval storage ctx locals) := BitVec.and_comm _ _
              rw [hc]
              exact (RuleList.and_drop_repeated_right _ _).symm
          · simp [hab] at h
        | shr =>
          simp only [] at h
          cases hcx : constant x with
          | none => simp [hcx] at h
          | some mask =>
            cases hca : constant a with
            | none => simp [hcx, hca] at h
            | some aw =>
              simp only [hcx, hca] at h
              split at h <;> simp at h
              next hawle =>
                rcases h with ⟨hcov, rfl⟩
                simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
                  constant_sound x mask hcx storage ctx locals,
                  constant_sound a aw hca storage ctx locals]
                exact (RuleList.remove_covered_shr_mask mask aw _ hawle hcov).symm
        | shl =>
          simp only [] at h
          cases hcx : constant x with
          | some mask =>
            simp only [hcx] at h
            cases hca : constant a with
            | none => simp [hca] at h
            | some aw =>
              simp only [hca] at h
              split at h <;> simp at h
              next hawle =>
                rcases h with ⟨hcov, rfl⟩
                simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
                  constant_sound x mask hcx storage ctx locals,
                  constant_sound a aw hca storage ctx locals]
                exact (RuleList.remove_covered_shl_mask mask aw _ hawle hcov).symm
          | none =>
            simp only [hcx] at h
            cases x with
            | binary xbop s2 v2 =>
              cases xbop <;> simp at h
              rcases h with ⟨rfl, rfl⟩
              exact (RuleList.and_shl_distribute _ _ _).symm
            | _ => simp at h
        | signextend =>
          simp only [] at h
          cases hcx : constant x with
          | none => simp [hcx] at h
          | some mask =>
            cases hca : constant a with
            | none => simp [hcx, hca] at h
            | some bw =>
              simp only [hcx, hca] at h
              split at h <;> simp at h
              next hblt =>
                rcases h with ⟨hmask, rfl⟩
                simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq,
                  constant_sound x mask hcx storage ctx locals,
                  constant_sound a bw hca storage ctx locals]
                exact (RuleList.strip_signextend_low_mask mask bw _ hblt hmask).symm
        | _ => simp at h
      | _ => simp at h

def reduceOrPair (x y : Expression) : Option Expression :=
  match y with
  | .unary .bitnot nx =>
    if nx = x then some (.literal maxWord.toNat)
    else match x with
      | .unary .bitnot mx => some (.unary .bitnot (.binary .and mx nx))
      | _ => none
  | .binary .and a b =>
    if x = a ∨ x = b then some x else none
  | .binary .or a b =>
    if x = a ∨ x = b then some (.binary .or a b) else none
  | _ => none

theorem reduceOrPair_sound (x y out : Expression) (h : reduceOrPair x y = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary .or x y).eval storage ctx locals := by
  unfold reduceOrPair at h
  cases y with
  | unary uop nx =>
    cases uop <;> try simp at h
    by_cases hnx : nx = x
    · simp only [hnx, ↓reduceIte, Option.some.injEq] at h
      subst out nx
      simp only [Expression.eval, maxWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact (RuleList.or_complement _).symm
    · simp only [hnx, ↓reduceIte] at h
      cases x with
      | unary xuop mx =>
        cases xuop <;> simp at h
        subst out
        exact (RuleList.demorgan_not_and _ _).symm
      | _ => simp at h
  | binary bop a b =>
    cases bop with
    | «and» =>
      simp only [] at h
      by_cases hab : x = a ∨ x = b
      · simp only [hab, ↓reduceIte, Option.some.injEq] at h
        subst out
        rcases hab with rfl | rfl
        · exact (RuleList.or_absorb_and_left _ _).symm
        · exact (RuleList.or_absorb_and_right _ _).symm
      · simp [hab] at h
    | «or» =>
      simp only [] at h
      by_cases hab : x = a ∨ x = b
      · simp only [hab, ↓reduceIte, Option.some.injEq] at h
        subst out
        simp only [Expression.eval]
        rcases hab with rfl | rfl
        · have hc : Binary.or.eval (x.eval storage ctx locals)
              (Binary.or.eval (x.eval storage ctx locals) (b.eval storage ctx locals)) =
            Binary.or.eval (Binary.or.eval (x.eval storage ctx locals) (b.eval storage ctx locals))
              (x.eval storage ctx locals) := BitVec.or_comm _ _
          rw [hc]
          exact (RuleList.or_drop_repeated_left _ _).symm
        · have hc : Binary.or.eval (x.eval storage ctx locals)
              (Binary.or.eval (a.eval storage ctx locals) (x.eval storage ctx locals)) =
            Binary.or.eval (Binary.or.eval (a.eval storage ctx locals) (x.eval storage ctx locals))
              (x.eval storage ctx locals) := BitVec.or_comm _ _
          rw [hc]
          exact (RuleList.or_drop_repeated_right _ _).symm
      · simp [hab] at h
    | _ => simp at h
  | _ => simp at h

def reduceSymmetricPair (op : Binary) (x y : Expression) : Option Expression :=
  match op with
  | .xor =>
    match y with
    | .binary .xor a b =>
      if x = a then some b else if x = b then some a else none
    | _ => none
  | .add =>
    if constant x = some 1#256 then
      match y with
      | .unary .bitnot a => some (.binary .sub (.literal 0) a)
      | .binary .sub a b => if x = b then some a else none
      | _ => none
    else
      match y with
      | .binary .sub a b => if x = b then some a else none
      | _ => none
  | .and => reduceAndPair x y
  | .or => reduceOrPair x y
  | _ => none

theorem reduceSymmetricPair_commutes (op : Binary) (x y out : Expression)
    (h : reduceSymmetricPair op x y = some out) : commute op = true := by
  cases op <;> simp [reduceSymmetricPair] at h <;> rfl

theorem reduceSymmetricPair_sound (op : Binary) (x y out : Expression)
    (h : reduceSymmetricPair op x y = some out)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    out.eval storage ctx locals = (Expression.binary op x y).eval storage ctx locals := by
  cases op <;> simp only [reduceSymmetricPair] at h
  case add =>
    by_cases hx1 : constant x = some 1#256
    · simp only [hx1, ↓reduceIte] at h
      cases y with
      | unary uop a =>
        cases uop <;> simp at h
        subst out
        simp only [Expression.eval, constant_sound x _ hx1 storage ctx locals]
        exact ((RuleList.not_add_one_eq_neg _).2).symm
      | binary bop a b =>
        cases bop <;> simp at h
        rcases h with ⟨rfl, rfl⟩
        exact (RuleList.sub_add_cancel_right _ _).symm
      | _ => simp at h
    · simp only [hx1, ↓reduceIte] at h
      cases y with
      | binary bop a b =>
        cases bop <;> simp at h
        rcases h with ⟨rfl, rfl⟩
        exact (RuleList.sub_add_cancel_right _ _).symm
      | _ => simp at h
  case «and» => exact reduceAndPair_sound x y out h storage ctx locals
  case «or» => exact reduceOrPair_sound x y out h storage ctx locals
  case xor =>
    cases y with
    | binary bop a b =>
      cases bop <;> try simp at h
      by_cases hxa : x = a
      · simp only [hxa, ↓reduceIte, Option.some.injEq] at h
        subst out a
        exact (RuleList.xor_cancel_left _ _).symm
      · simp only [hxa, ↓reduceIte] at h
        by_cases hxb : x = b
        · simp only [hxb, ↓reduceIte, Option.some.injEq] at h
          subst out b
          exact (RuleList.xor_cancel_right _ _).symm
        · simp [hxb] at h
    | _ => simp at h
  all_goals simp at h

def reduceBinary (op : Binary) (a b : Expression) : Expression :=
  match constant a, constant b with
  | some x, some y => .literal (op.eval x y).toNat
  | _, _ =>
    match reduceRuleListBinary op a b with
    | some out => out
    | none =>
      match reduceSymmetricPair op a b with
      | some out => out
      | none =>
        match reduceSymmetricPair op b a with
        | some out => out
        | none => regroup op a b

theorem reduceBinary_sound (op : Binary) (a b : Expression)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    (reduceBinary op a b).eval storage ctx locals =
      (Expression.binary op a b).eval storage ctx locals := by
  unfold reduceBinary
  split
  next x y hx hy =>
    simp only [Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [constant_sound a x hx storage ctx locals, constant_sound b y hy storage ctx locals]
  all_goals
    split
    next out hout => exact reduceRuleListBinary_sound op a b out hout storage ctx locals
    next =>
      split
      next out hout => exact reduceSymmetricPair_sound op a b out hout storage ctx locals
      next =>
        split
        next out hout =>
          rw [reduceSymmetricPair_sound op b a out hout storage ctx locals]
          exact commute_sound op (reduceSymmetricPair_commutes op b a out hout) _ _
        next => exact regroup_sound op a b storage ctx locals

def reduce : Expression → Expression
  | .literal value => .literal (BitVec.ofNat 256 value).toNat
  | .unary op arg => reduceUnary op arg
  | .binary op a b => reduceBinary op a b
  | .ternary op a b c => reduceTernary op a b c
  | e => e

theorem reduce_sound (e : Expression) (storage : Word → Word)
    (ctx : Context) (locals : String → Word) :
    (reduce e).eval storage ctx locals = e.eval storage ctx locals := by
  cases e with
  | literal value => simp only [reduce, Expression.eval, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  | unary op arg => exact reduceUnary_sound op arg storage ctx locals
  | binary op a b => exact reduceBinary_sound op a b storage ctx locals
  | ternary op a b c => exact reduceTernary_sound op a b c storage ctx locals
  | _ => rfl

def normalize : Nat → Expression → Expression
  | 0, e => e
  | fuel + 1, e =>
    let children := match e with
      | .unary op a => .unary op (normalize fuel a)
      | .binary op a b => .binary op (normalize fuel a) (normalize fuel b)
      | .ternary op a b c => .ternary op (normalize fuel a) (normalize fuel b) (normalize fuel c)
      | _ => e
    let changed := reduce children
    if changed = children then children else normalize fuel changed

theorem normalize_sound (fuel : Nat) (e : Expression) (storage : Word → Word)
    (ctx : Context) (locals : String → Word) :
    (normalize fuel e).eval storage ctx locals = e.eval storage ctx locals := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
    cases e <;> simp only [normalize] <;> split <;>
      simp only [ih, reduce_sound, Expression.eval]

def equivalent (fuel : Nat) (a b : Expression) : Bool := decide (normalize fuel a = normalize fuel b)

theorem equivalent_sound (fuel : Nat) (a b : Expression) (accepted : equivalent fuel a b = true)
    (storage : Word → Word) (ctx : Context) (locals : String → Word) :
    a.eval storage ctx locals = b.eval storage ctx locals := by
  simp only [equivalent, decide_eq_true_eq] at accepted
  rw [← normalize_sound fuel a, ← normalize_sound fuel b, accepted]

#audit_contract_proof Compiler.Validation.normalize_sound
#audit_contract_proof Compiler.Validation.equivalent_sound

end Compiler.Validation
