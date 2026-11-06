/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Validation.Graph
import Contract.Evm.Machine

/-! Cancun straight-line word-block bytecode validator bridged directly to the
unified `Contract.Evm` raw-byte machine (`Contract.Evm.step`, `run`, `runMetered`).

Numeric byte decoding is independent of the Zig instruction enum. Unsupported
instructions, truncated `PUSH` immediates, stack overflows (`> 1024`), stack
underflows, and exhausted checking fuel all reject (`false`).

Acceptance guarantees both:
1. Symbolic/word block execution produces `source.eval storage ctx locals :: parameters.map locals`
   preserving the caller's stack frame for every `Context` and local assignment.
2. Appending `0x00` (`STOP`) and running the real `Contract.Evm.Machine` from `pc = 0`
   halts cleanly with `.returned []` and final machine stack
   `source.eval storage ctx locals :: parameters.map locals` (and exact gas cost
   under `runMetered` for all gas budgets). -/
namespace Compiler.Validation.WordBlock
open Contract Contract.Yul Contract.Evm

inductive Op where
  | push (width : Nat) (value : Word)
  | dup (index : Nat)
  | nullary (op : Nullary)
  | unary (op : Unary)
  | binary (op : Binary)
  | ternary (op : Ternary)
  deriving DecidableEq, Repr

/-- Decode one straight-line instruction at `pc` in `code`, returning `(op, byteWidth)`.
Truncated `PUSH1..PUSH32` immediates are rejected (`pc + 1 + width ≤ code.length`). -/
def decodeAt (code : List UInt8) (pc : Nat) : Option (Op × Nat) :=
  match code[pc]? with
  | none => none
  | some byte =>
    let n := byte.toNat
    if n = 0x5f then
      some (.push 0 0#256, 1)
    else if 0x60 ≤ n ∧ n ≤ 0x7f then
      let w := pushWidth byte
      if pc + 1 + w ≤ code.length then
        some (.push w (bytesWord (padded code (pc + 1) w)), 1 + w)
      else none
    else if 0x80 ≤ n ∧ n ≤ 0x8f then
      some (.dup (n - 0x80), 1)
    else match n with
      | 0x01 => some (.binary .add, 1)
      | 0x02 => some (.binary .mul, 1)
      | 0x03 => some (.binary .sub, 1)
      | 0x04 => some (.binary .div, 1)
      | 0x05 => some (.binary .sdiv, 1)
      | 0x06 => some (.binary .mod, 1)
      | 0x07 => some (.binary .smod, 1)
      | 0x08 => some (.ternary .addmod, 1)
      | 0x09 => some (.ternary .mulmod, 1)
      | 0x0a => some (.binary .exp, 1)
      | 0x0b => some (.binary .signextend, 1)
      | 0x10 => some (.binary .lt, 1)
      | 0x11 => some (.binary .gt, 1)
      | 0x12 => some (.binary .slt, 1)
      | 0x13 => some (.binary .sgt, 1)
      | 0x14 => some (.binary .eq, 1)
      | 0x15 => some (.unary .iszero, 1)
      | 0x16 => some (.binary .and, 1)
      | 0x17 => some (.binary .or, 1)
      | 0x18 => some (.binary .xor, 1)
      | 0x19 => some (.unary .bitnot, 1)
      | 0x1a => some (.binary .byte, 1)
      | 0x1b => some (.binary .shl, 1)
      | 0x1c => some (.binary .shr, 1)
      | 0x1d => some (.binary .sar, 1)
      | 0x30 => some (.nullary .address, 1)
      | 0x32 => some (.nullary .origin, 1)
      | 0x33 => some (.nullary .caller, 1)
      | 0x41 => some (.nullary .coinbase, 1)
      | _ => none

def Op.step (algebra : Algebra α) (stack : List α) : Op → Option (List α)
  | .push _ v =>
    if stack.length < 1024 then some (algebra.literal v.toNat :: stack) else none
  | .dup i =>
    if stack.length < 1024 then do return (← stack[i]?) :: stack else none
  | .nullary op =>
    if stack.length < 1024 then some (algebra.nullary op :: stack) else none
  | .unary op => match stack with
    | a :: rest => some (algebra.unary op a :: rest)
    | _ => none
  | .binary op => match stack with
    | a :: b :: rest => some (algebra.binary op a b :: rest)
    | _ => none
  | .ternary op => match stack with
    | a :: b :: c :: rest => some (algebra.ternary op a b c :: rest)
    | _ => none

/-- Symbolic/abstract straight-line block runner over `code` starting at `pc`.
Requires `stack.length ≤ 1024` at every point and reaches `pc = code.length`
cleanly without jumping past `code.length`. -/
def runBlock (algebra : Algebra α) (code : List UInt8) : Nat → Nat → List α → Option (List α)
  | 0, pc, stack =>
    if stack.length > 1024 then none
    else if pc = code.length then some stack
    else none
  | fuel + 1, pc, stack =>
    if stack.length > 1024 then none
    else if pc = code.length then some stack
    else do
      let (op, width) ← decodeAt code pc
      let next ← op.step algebra stack
      runBlock algebra code fuel (pc + width) next

def evalExpr (ctx : Context) (locals : String → Word) (e : Expression) : Word :=
  e.eval (fun _ => 0#256) ctx locals

theorem Op.step_map (op : Op) (stack : List Expression) (ctx : Context) (locals : String → Word) :
    op.step (words ctx locals) (stack.map (evalExpr ctx locals)) =
      (op.step expressions stack).map (List.map (evalExpr ctx locals)) := by
  cases op with
  | push _ v =>
    simp only [Op.step, List.length_map]
    split
    · simp [expressions, words, evalExpr, Expression.eval]
    · rfl
  | dup i =>
    simp only [Op.step, List.length_map]
    split
    · cases h : stack[i]? <;> simp [h, List.getElem?_map]
    · rfl
  | nullary op =>
    simp only [Op.step, List.length_map]
    split
    · simp [expressions, words, evalExpr, Expression.eval]
    · rfl
  | unary op =>
    cases stack <;> simp [Op.step, expressions, words, evalExpr, Expression.eval]
  | binary op =>
    cases stack with
    | nil => rfl
    | cons a rest =>
      cases rest <;> simp [Op.step, expressions, words, evalExpr, Expression.eval]
  | ternary op =>
    cases stack with
    | nil => rfl
    | cons a r1 =>
      cases r1 with
      | nil => rfl
      | cons b r2 =>
        cases r2 <;> simp [Op.step, expressions, words, evalExpr, Expression.eval]

theorem runBlock_map (code : List UInt8) (fuel pc : Nat) (stack : List Expression)
    (ctx : Context) (locals : String → Word) :
    runBlock (words ctx locals) code fuel pc (stack.map (evalExpr ctx locals)) =
      (runBlock expressions code fuel pc stack).map (List.map (evalExpr ctx locals)) := by
  induction fuel generalizing pc stack with
  | zero =>
    unfold runBlock
    simp only [List.length_map]
    split
    · rfl
    · split <;> rfl
  | succ fuel ih =>
    unfold runBlock
    simp only [List.length_map]
    split
    · rfl
    · split
      · rfl
      · cases hd : decodeAt code pc with
        | none => simp
        | some decoded =>
          rcases decoded with ⟨op, width⟩
          simp only [bind, Option.bind, Op.step_map]
          cases hs : op.step expressions stack with
          | none => simp
          | some next =>
            simp only [Option.map_some]
            exact ih (pc + width) next

/-- Source lowering for `compiler-word-export`: Solidity shifts use `(value, shift)`
argument order while Yul/EVM `Node` uses `(shift, value)`. All other admitted
unchecked word operations (`input`, `literal`, `bitnot`, `add`, `sub`, `mul`,
`and`, `or`, `xor`) keep their operand order. -/
def lowerSourceNode : Node → Option Node
  | .literal n => some (.literal n)
  | .input name => some (.input name)
  | .unary .bitnot a => some (.unary .bitnot a)
  | .binary op l r =>
    match op with
    | .add | .sub | .mul | .and | .or | .xor => some (.binary op l r)
    | .shl | .shr => some (.binary op r l)
    | _ => none
  | _ => none

def lowerSourceNodes (parameters : List String) (nodes : List Node) : Option (List Node) :=
  nodes.mapM fun n => do
    match n with
    | .input name => if name ∈ parameters then lowerSourceNode n else none
    | _ => lowerSourceNode n

def validate (fuel : Nat) (code : List UInt8) (parameters : List String)
    (source : Expression) : Bool :=
  parameters.length ≤ 16 &&
  parameters.Nodup &&
  !code.isEmpty &&
  code.length ≤ 4096 &&
  match runBlock expressions code code.length 0 (parameters.map Expression.variable) with
  | some (result :: frame) =>
    equivalent fuel source result && decide (frame = parameters.map Expression.variable)
  | _ => false

def execute (code : List UInt8) (ctx : Context) (stack : List Word) : Option (List Word) :=
  runBlock (words ctx (fun _ => 0#256)) code code.length 0 stack

theorem runBlock_words_irrel_locals (code : List UInt8) (fuel pc : Nat) (stack : List Word)
    (ctx : Context) (l1 l2 : String → Word) :
    runBlock (words ctx l1) code fuel pc stack = runBlock (words ctx l2) code fuel pc stack := by
  induction fuel generalizing pc stack with
  | zero => rfl
  | succ fuel ih =>
    unfold runBlock
    split
    · rfl
    · split
      · rfl
      · cases hd : decodeAt code pc with
        | none => rfl
        | some decoded =>
          rcases decoded with ⟨op, width⟩
          have hstep : op.step (words ctx l1) stack = op.step (words ctx l2) stack := by
            cases op <;> rfl
          simp only [bind, Option.bind, hstep]
          cases op.step (words ctx l2) stack with
          | none => rfl
          | some next => exact ih (pc + width) next

private theorem padded_append_left (code tail : List UInt8) (offset w : Nat)
    (h : offset + w ≤ code.length) :
    padded (code ++ tail) offset w = padded code offset w := by
  simp only [padded, readBytesPadded]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have hlt : offset + i < code.length := by omega
  rw [List.getElem?_append_left hlt]

private theorem decodeAt_step_evm (code tail : List UInt8) (pc : Nat) (op : Op) (width : Nat)
    (input : Input) (env : Environment) (s : State) (wStack : List Word)
    (hsp : s.machine.pc = pc)
    (hd : decodeAt code pc = some (op, width))
    (hop : op.step (words env.ctx (fun _ => 0#256)) s.machine.stack = some wStack) :
    ∃ cost, Contract.Evm.step (code ++ tail) input env s =
      .next cost 0 { s with machine := { s.machine with pc := pc + width, stack := wStack } } := by
  unfold decodeAt at hd
  cases hbyte : code[pc]? with
  | none => simp [hbyte] at hd
  | some byte =>
    have hlt : pc < code.length := by
      cases Nat.lt_or_ge pc code.length with
      | inl h => exact h
      | inr hge =>
        rw [List.getElem?_eq_none hge] at hbyte
        cases hbyte
    have hcode_byte : ((code ++ tail)[pc]?).getD 0 = byte := by
      rw [List.getElem?_append_left hlt, hbyte]; rfl
    simp only [hbyte] at hd
    by_cases h5f : byte.toNat = 0x5f
    · simp only [h5f, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hd
      rcases hd with ⟨rfl, rfl⟩
      simp only [Op.step, words, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hop
      split at hop
      · rename_i hlen
        simp only [Option.some.injEq] at hop
        subst hop
        refine ⟨2, ?_⟩
        unfold Contract.Evm.step
        simp only [hsp, hcode_byte, h5f, Contract.Evm.push, hlen, ↓reduceIte]
      · cases hop
    · simp only [h5f, ↓reduceIte] at hd
      by_cases hpush : 0x60 ≤ byte.toNat ∧ byte.toNat ≤ 0x7f
      · simp only [hpush, and_self, ↓reduceIte] at hd
        split at hd
        · rename_i hfit
          simp only [Option.some.injEq, Prod.mk.injEq] at hd
          rcases hd with ⟨rfl, rfl⟩
          simp only [Op.step, words, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hop
          split at hop
          · rename_i hlen
            simp only [Option.some.injEq] at hop
            subst hop
            refine ⟨3, ?_⟩
            unfold Contract.Evm.step
            simp only [hsp, hcode_byte]
            have hnot_fixed :
                byte.toNat ≠ 0x00 ∧ byte.toNat ≠ 0x01 ∧ byte.toNat ≠ 0x02 ∧ byte.toNat ≠ 0x03 ∧
                byte.toNat ≠ 0x04 ∧ byte.toNat ≠ 0x05 ∧ byte.toNat ≠ 0x06 ∧ byte.toNat ≠ 0x07 ∧
                byte.toNat ≠ 0x08 ∧ byte.toNat ≠ 0x09 ∧ byte.toNat ≠ 0x0a ∧ byte.toNat ≠ 0x0b ∧
                byte.toNat ≠ 0x10 ∧ byte.toNat ≠ 0x11 ∧ byte.toNat ≠ 0x12 ∧ byte.toNat ≠ 0x13 ∧
                byte.toNat ≠ 0x14 ∧ byte.toNat ≠ 0x15 ∧ byte.toNat ≠ 0x16 ∧ byte.toNat ≠ 0x17 ∧
                byte.toNat ≠ 0x18 ∧ byte.toNat ≠ 0x19 ∧ byte.toNat ≠ 0x1a ∧ byte.toNat ≠ 0x1b ∧
                byte.toNat ≠ 0x1c ∧ byte.toNat ≠ 0x1d ∧ byte.toNat ≠ 0x30 ∧ byte.toNat ≠ 0x32 ∧
                byte.toNat ≠ 0x33 ∧ byte.toNat ≠ 0x34 ∧ byte.toNat ≠ 0x35 ∧ byte.toNat ≠ 0x36 ∧
                byte.toNat ≠ 0x37 ∧ byte.toNat ≠ 0x38 ∧ byte.toNat ≠ 0x39 ∧ byte.toNat ≠ 0x41 ∧
                byte.toNat ≠ 0x50 ∧ byte.toNat ≠ 0x51 ∧ byte.toNat ≠ 0x52 ∧ byte.toNat ≠ 0x53 ∧
                byte.toNat ≠ 0x54 ∧ byte.toNat ≠ 0x55 ∧ byte.toNat ≠ 0x56 ∧ byte.toNat ≠ 0x57 ∧
                byte.toNat ≠ 0x58 ∧ byte.toNat ≠ 0x59 ∧ byte.toNat ≠ 0x5b ∧ byte.toNat ≠ 0x5f ∧
                byte.toNat ≠ 0x80 ∧ byte.toNat ≠ 0xf3 ∧ byte.toNat ≠ 0xfd ∧ byte.toNat ≠ 0xfe := by
              omega
            rcases hpush with ⟨hlo, hhi⟩
            have hpad := padded_append_left code tail (pc + 1) (pushWidth byte) hfit
            split <;> try omega
            simp only [hlo, hhi, and_self, ↓reduceIte, Contract.Evm.push, hlen, hsp, hpad]
          · cases hop
        · cases hd
      · simp only [hpush, ↓reduceIte] at hd
        by_cases hdup : 0x80 ≤ byte.toNat ∧ byte.toNat ≤ 0x8f
        · simp only [hdup, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hd
          rcases hd with ⟨rfl, rfl⟩
          simp only [Op.step] at hop
          split at hop
          · rename_i hlen
            cases hidx : s.machine.stack[byte.toNat - 0x80]? with
            | none => simp [hidx] at hop
            | some val =>
              simp only [hidx, bind, pure, Option.bind_some, Option.some.injEq] at hop
              subst hop
              refine ⟨3, ?_⟩
              unfold Contract.Evm.step
              simp only [hsp, hcode_byte]
              by_cases h80 : byte.toNat = 0x80
              · simp only [h80] at hidx ⊢
                cases hst : s.machine.stack with
                | nil => simp [hst] at hidx
                | cons top rest =>
                  simp only [hst, Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hidx
                  subst hidx
                  simp [Contract.Evm.push, hst] at hlen ⊢
                  simp [hlen, hsp]
              · rcases hdup with ⟨hlo, hhi⟩
                have h81 : 0x81 ≤ byte.toNat := by omega
                split <;> try omega
                simp only [hpush, ↓reduceIte, h81, hhi, and_self, hidx, Contract.Evm.push, hlen, hsp]
          · cases hop
        · simp only [hdup, ↓reduceIte] at hd
          split at hd
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨5, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨5, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨5, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨5, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨5, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b r2 => cases r2 with
                | nil => simp [Op.step, hst] at hop
                | cons c rest =>
                  simp only [Op.step, hst, words, Ternary.eval, Option.some.injEq] at hop; subst hop
                  exact ⟨8, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.ternary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b r2 => cases r2 with
                | nil => simp [Op.step, hst] at hop
                | cons c rest =>
                  simp only [Op.step, hst, words, Ternary.eval, Option.some.injEq] at hop; subst hop
                  exact ⟨8, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.ternary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨10 + 50 * expByteLen b, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨5, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a rest =>
              simp only [Op.step, hst, words, Unary.eval, Option.some.injEq] at hop; subst hop
              exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.unary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a rest =>
              simp only [Op.step, hst, words, Unary.eval, Option.some.injEq] at hop; subst hop
              exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.unary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            cases hst : s.machine.stack with
            | nil => simp [Op.step, hst] at hop
            | cons a r1 => cases r1 with
              | nil => simp [Op.step, hst] at hop
              | cons b rest =>
                simp only [Op.step, hst, words, Binary.eval, Option.some.injEq] at hop; subst hop
                exact ⟨3, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.binary, hst]⟩
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            simp only [Op.step, words, Nullary.eval] at hop
            split at hop
            · rename_i hlen; simp only [Option.some.injEq] at hop; subst hop
              exact ⟨2, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.push, hlen]⟩
            · cases hop
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            simp only [Op.step, words, Nullary.eval] at hop
            split at hop
            · rename_i hlen; simp only [Option.some.injEq] at hop; subst hop
              exact ⟨2, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.push, hlen]⟩
            · cases hop
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            simp only [Op.step, words, Nullary.eval] at hop
            split at hop
            · rename_i hlen; simp only [Option.some.injEq] at hop; subst hop
              exact ⟨2, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.push, hlen]⟩
            · cases hop
          · rename_i hn
            simp only [Option.some.injEq, Prod.mk.injEq] at hd; rcases hd with ⟨rfl, rfl⟩
            simp only [Op.step, words, Nullary.eval] at hop
            split at hop
            · rename_i hlen; simp only [Option.some.injEq] at hop; subst hop
              exact ⟨2, by unfold Contract.Evm.step; simp [hsp, hcode_byte, hn, Contract.Evm.push, hlen]⟩
            · cases hop
          · cases hd

/-- Any accepted `runBlock` execution steps faithfully in `Contract.Evm.run`
when followed by `0x00` (`STOP`), halting cleanly with `.returned []`, identical
cost = sentry (`needed = used`, since no `SSTORE` executes), and final stack `out`. -/
theorem runBlock_evm (code : List UInt8) (fuel pc : Nat) (input : Input)
    (env : Environment) (s : State) (out : List Word)
    (hsp : s.machine.pc = pc)
    (hrun : runBlock (words env.ctx (fun _ => 0#256)) code fuel pc s.machine.stack = some out) :
    ∃ cost, Contract.Evm.run (code ++ [0x00]) input env (fuel + 1) s =
      .finished cost cost ⟨.returned [], { s with machine := { s.machine with pc := code.length, stack := out } }⟩ := by
  induction fuel generalizing pc s with
  | zero =>
    unfold runBlock at hrun
    split at hrun
    · cases hrun
    · split at hrun
      · rename_i hpc
        simp only [Option.some.injEq] at hrun
        subst hrun
        refine ⟨0, ?_⟩
        unfold Contract.Evm.run Guarded.run Contract.Evm.step
        have hstop : ((code ++ [0x00])[s.machine.pc]?).getD 0 = 0 := by
          rw [hsp, hpc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        simp only [hstop, UInt8.toNat_zero]
        have hs : { s with machine := { s.machine with pc := code.length, stack := s.machine.stack } } = s := by
          cases s with | mk m st wm rf =>
          cases m; simp at hsp hpc; subst hsp; subst hpc; rfl
        rw [hs]
      · cases hrun
  | succ fuel ih =>
    unfold runBlock at hrun
    split at hrun
    · cases hrun
    · split at hrun
      · rename_i hpc
        simp only [Option.some.injEq] at hrun
        subst hrun
        refine ⟨0, ?_⟩
        unfold Contract.Evm.run Guarded.run Contract.Evm.step
        have hstop : ((code ++ [0x00])[s.machine.pc]?).getD 0 = 0 := by
          rw [hsp, hpc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
          rfl
        simp only [hstop, UInt8.toNat_zero]
        have hs : { s with machine := { s.machine with pc := code.length, stack := s.machine.stack } } = s := by
          cases s with | mk m st wm rf =>
          cases m; simp at hsp hpc; subst hsp; subst hpc; rfl
        rw [hs]
      · cases hd : decodeAt code pc with
        | none => simp [hd] at hrun
        | some decoded =>
          rcases decoded with ⟨op, width⟩
          simp only [hd, bind, Option.bind] at hrun
          cases hop : op.step (words env.ctx (fun _ => 0#256)) s.machine.stack with
          | none => simp [hop] at hrun
          | some nextStack =>
            simp only [hop] at hrun
            obtain ⟨c1, hstep⟩ := decodeAt_step_evm code [0x00] pc op width input env s nextStack hsp hd hop
            let s' : State := { s with machine := { s.machine with pc := pc + width, stack := nextStack } }
            obtain ⟨c2, hrest⟩ := ih (pc + width) s' rfl hrun
            refine ⟨c1 + c2, ?_⟩
            rw [Contract.Evm.run, Guarded.run, hstep]
            change (Contract.Evm.run (code ++ [0x00]) input env (fuel + 1) s').charge c1 0 = _
            rw [hrest]
            simp only [Guarded.Trace.charge, Nat.zero_max]
            rfl

/-- Master soundness theorem for straight-line word blocks:
if `validate fuel code parameters source = true`, then for every execution
environment `env`, input `input`, initial state `s` starting at `pc = 0` with
`s.machine.stack = parameters.map locals`, and local assignment `locals`:
1. Abstract word execution returns `evalExpr env.ctx locals source :: parameters.map locals`.
2. Real `Contract.Evm` execution on `code ++ [0x00]` finishes cleanly with exact
   cost `cost`, returning `evalExpr env.ctx locals source :: parameters.map locals`.
3. `Contract.Evm.runMetered` matches for every gas budget `gas`. -/
theorem validate_sound (fuel : Nat) (code : List UInt8) (parameters : List String)
    (source : Expression) (accepted : validate fuel code parameters source = true)
    (input : Input) (env : Environment) (locals : String → Word) (s : State)
    (hpc : s.machine.pc = 0) (hstack : s.machine.stack = parameters.map locals) :
    let expectedStack := evalExpr env.ctx locals source :: parameters.map locals
    execute code env.ctx (parameters.map locals) = some expectedStack ∧
    ∃ cost,
      Contract.Evm.run (code ++ [0x00]) input env (code.length + 1) s =
        .finished cost cost ⟨.returned [], { s with machine := { s.machine with pc := code.length, stack := expectedStack } }⟩ ∧
      ∀ gas, Contract.Evm.runMetered (code ++ [0x00]) input env (code.length + 1) gas s =
        if cost ≤ gas then
          .finished (gas - cost) ⟨.returned [], { s with machine := { s.machine with pc := code.length, stack := expectedStack } }⟩
        else .exceptional := by
  unfold validate at accepted
  simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
  rcases accepted with ⟨⟨⟨_, _⟩, _⟩, hblk⟩
  cases h : runBlock expressions code code.length 0 (parameters.map Expression.variable) with
  | none => simp [h] at hblk
  | some resStack =>
    cases resStack with
    | nil => simp [h] at hblk
    | cons result frame =>
      simp only [h, Bool.and_eq_true, decide_eq_true_eq] at hblk
      rcases hblk with ⟨heq, hframe⟩
      have same := equivalent_sound fuel source result heq (fun _ => 0#256) env.ctx locals
      have mapped := runBlock_map code code.length 0 (parameters.map Expression.variable) env.ctx locals
      rw [h] at mapped
      simp only [Option.map_some, List.map_cons, hframe, List.map_map] at mapped
      have hmap_in : List.map (evalExpr env.ctx locals ∘ Expression.variable) parameters = parameters.map locals := by
        apply List.map_congr_left; intro _ _; rfl
      rw [hmap_in] at mapped
      have hirrel := runBlock_words_irrel_locals code code.length 0 (parameters.map locals) env.ctx locals (fun _ => 0#256)
      have hexec : execute code env.ctx (parameters.map locals) =
          some (evalExpr env.ctx locals source :: parameters.map locals) := by
        unfold execute
        rw [← hirrel, mapped]
        simp only [evalExpr, same]
      refine ⟨hexec, ?_⟩
      have hsrun : runBlock (words env.ctx (fun _ => 0#256)) code code.length 0 s.machine.stack =
          some (evalExpr env.ctx locals source :: parameters.map locals) := by
        rw [hstack]; exact hexec
      obtain ⟨cost, hevm⟩ := runBlock_evm code code.length 0 input env s
        (evalExpr env.ctx locals source :: parameters.map locals) hpc hsrun
      refine ⟨cost, hevm, ?_⟩
      intro gas
      exact Guarded.metered_of_run (Contract.Evm.step (code ++ [0x00]) input env)
        (code.length + 1) s cost cost _ gas hevm

#audit_contract_proof Compiler.Validation.WordBlock.validate_sound

end Compiler.Validation.WordBlock
