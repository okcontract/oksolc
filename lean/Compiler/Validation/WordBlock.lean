/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Validation.Graph

/-! Cancun straight-line word blocks. Numeric byte decoding is independent of
the Zig instruction enum. Unsupported instructions, truncated immediates,
stack faults and exhausted checking fuel reject. No storage, memory, control
flow or transaction observations are admitted. The end of this byte slice is
a block boundary, not an EVM STOP instruction. -/
namespace Compiler.Validation.WordBlock
open Contract.Yul

inductive Op where
  | push (value : Nat)
  | dup (index : Nat)
  | unary (op : Unary)
  | binary (op : Binary)
  deriving DecidableEq, Repr

def decode : List UInt8 → Option (Op × Nat × List UInt8)
  | [] => none
  | byte :: rest =>
    let n := byte.toNat
    if 0x5f ≤ n ∧ n ≤ 0x7f then
      let width := n - 0x5f
      if width ≤ rest.length then
        some (.push ((rest.take width).foldl (fun acc b => acc * 256 + b.toNat) 0),
          if width = 0 then 2 else 3, rest.drop width)
      else none
    else if 0x80 ≤ n ∧ n ≤ 0x8f then some (.dup (n - 0x80), 3, rest)
    else match n with
      | 0x01 => some (.binary .add, 3, rest)
      | 0x02 => some (.binary .mul, 5, rest)
      | 0x03 => some (.binary .sub, 3, rest)
      | 0x04 => some (.binary .div, 5, rest)
      | 0x06 => some (.binary .mod, 5, rest)
      | 0x10 => some (.binary .lt, 3, rest)
      | 0x11 => some (.binary .gt, 3, rest)
      | 0x14 => some (.binary .eq, 3, rest)
      | 0x15 => some (.unary .iszero, 3, rest)
      | 0x16 => some (.binary .and, 3, rest)
      | 0x17 => some (.binary .or, 3, rest)
      | 0x18 => some (.binary .xor, 3, rest)
      | 0x19 => some (.unary .bitnot, 3, rest)
      | 0x1b => some (.binary .shl, 3, rest)
      | 0x1c => some (.binary .shr, 3, rest)
      | _ => none

def Op.step (algebra : Algebra α) (stack : List α) : Op → Option (List α)
  | .push n => some (algebra.literal n :: stack)
  | .dup i => do return (← stack[i]?) :: stack
  | .unary op => match stack with
    | a :: rest => some (algebra.unary op a :: rest)
    | _ => none
  | .binary op => match stack with
    | a :: b :: rest => some (algebra.binary op a b :: rest)
    | _ => none

/-- Every visited stack, including entry and exit, must fit the EVM bound.
Gas costs are accumulated exactly; the metered observation below requires
sufficient entry gas. Fuel bounds checking work, not the word domain. -/
def run (algebra : Algebra α) : Nat → List UInt8 → List α → Option (Nat × List α)
  | fuel, code, stack =>
    if stack.length > 1024 then none else
    match code with
    | [] => some (0, stack)
    | _ :: _ => match fuel with
      | 0 => none
      | fuel + 1 => do
        let (op, cost, rest) ← decode code
        let next ← op.step algebra stack
        let (remaining, result) ← run algebra fuel rest next
        return (cost + remaining, result)

def eval (locals : String → Word) : Expression → Word :=
  Expression.eval (fun _ => 0) ⟨0, 0⟩ locals

def wordAlgebra : Algebra Word := words (fun _ => 0)

theorem Op.step_map (op : Op) (stack : List Expression) (locals : String → Word) :
    op.step wordAlgebra (stack.map (eval locals)) =
      (op.step expressions stack).map (List.map (eval locals)) := by
  cases op with
  | push => rfl
  | dup i => cases h : stack[i]? <;> simp [Op.step, List.getElem?_map, h]
  | unary op => cases stack <;> rfl
  | binary op => cases stack with
    | nil => rfl
    | cons a rest => cases rest <;> rfl

theorem run_map (fuel : Nat) (code : List UInt8) (stack : List Expression)
    (locals : String → Word) :
    run wordAlgebra fuel code (stack.map (eval locals)) =
      (run expressions fuel code stack).map (fun (cost, result) => (cost, result.map (eval locals))) := by
  induction fuel generalizing code stack with
  | zero => cases code <;> simp only [run.eq_def, List.length_map] <;> split <;> rfl
  | succ fuel ih =>
    rw [run.eq_def wordAlgebra (fuel + 1) code (stack.map (eval locals)),
      run.eq_def expressions (fuel + 1) code stack]
    simp only [List.length_map]
    split
    · rfl
    · cases code with
      | nil => rfl
      | cons byte rest =>
        cases hd : decode (byte :: rest) with
        | none => simp
        | some decoded =>
          rcases decoded with ⟨op, cost, tail⟩
          simp only [Op.step_map]
          cases hs : op.step expressions stack with
          | none => simp [hs]
          | some next =>
            simp [hs]
            rw [ih tail next]
            cases run expressions fuel tail next <;> rfl

def validate (fuel : Nat) (code : List UInt8) (parameters : List String)
    (source : Expression) : Bool :=
  match run expressions code.length code (parameters.map Expression.variable) with
  | some (_, result :: frame) =>
    equivalent fuel source result && decide (frame = parameters.map Expression.variable)
  | _ => false

def execute (code : List UInt8) (stack : List Word) : Option (Nat × List Word) :=
  run wordAlgebra code.length code stack

theorem validate_sound (fuel : Nat) (code : List UInt8) (parameters : List String)
    (source : Expression) (accepted : validate fuel code parameters source = true)
    (locals : String → Word) :
    ∃ cost, execute code (parameters.map locals) =
      some (cost, eval locals source :: parameters.map locals) := by
  unfold validate at accepted
  cases h : run expressions code.length code (parameters.map Expression.variable) with
  | none => simp [h] at accepted
  | some output =>
    rcases output with ⟨cost, stack⟩
    cases stack with
    | nil => simp [h] at accepted
    | cons result frame =>
      simp only [h, Bool.and_eq_true, decide_eq_true_eq] at accepted
      have same := equivalent_sound fuel source result accepted.1 (fun _ => 0) ⟨0, 0⟩ locals
      have mapped := run_map code.length code (parameters.map Expression.variable) locals
      rw [h] at mapped
      simp only [Option.map_some, List.map_cons, accepted.2, List.map_map] at mapped
      simpa only [execute, eval, Expression.eval, same] using Exists.intro cost mapped

def metered (code : List UInt8) (stack : List Word) (gas : Nat) : Option (Nat × List Word) := do
  let (cost, result) ← execute code stack
  if cost ≤ gas then some (gas - cost, result) else none

theorem metered_of_execute (code : List UInt8) (stack result : List Word) (cost gas : Nat)
    (done : execute code stack = some (cost, result)) (enough : cost ≤ gas) :
    metered code stack gas = some (gas - cost, result) := by
  simp [metered, done, enough]

end Compiler.Validation.WordBlock
