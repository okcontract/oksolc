/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Validation.Normalize

/-! Dense, topologically ordered graph representation for translation validation
of the production `ExpressionClasses` pass over the full pure/environmental
EVM opcode set (`Nullary`, `Unary`, `Binary`, `Ternary`).

Every node reference must point strictly to an earlier node index, ruling out
forward references, cycles, and out-of-range IDs even in unreachable nodes. -/
namespace Compiler.Validation
open Contract Contract.Yul

inductive Node where
  | literal (value : Nat)
  | input (name : String)
  | nullary (op : Nullary)
  | unary (op : Unary) (arg : Nat)
  | binary (op : Binary) (left right : Nat)
  | ternary (op : Ternary) (first second third : Nat)
  deriving DecidableEq, Repr

structure Algebra (α : Type) where
  literal : Nat → α
  input : String → α
  nullary : Nullary → α
  unary : Unary → α → α
  binary : Binary → α → α → α
  ternary : Ternary → α → α → α → α

def Node.run (algebra : Algebra α) (values : List α) : Node → Option α
  | .literal n => some (algebra.literal n)
  | .input name => some (algebra.input name)
  | .nullary op => some (algebra.nullary op)
  | .unary op arg => do return algebra.unary op (← values[arg]?)
  | .binary op left right => do return algebra.binary op (← values[left]?) (← values[right]?)
  | .ternary op first second third => do
    return algebra.ternary op (← values[first]?) (← values[second]?) (← values[third]?)

def expressions : Algebra Expression :=
  ⟨.literal, .variable, .nullary, .unary, .binary, .ternary⟩

def words (ctx : Context) (locals : String → Word) : Algebra Word :=
  ⟨BitVec.ofNat 256, locals, Nullary.eval ctx, Unary.eval, Binary.eval, Ternary.eval⟩

/-- Reject every invalid reference, including in an unused node. Only earlier
nodes are available, so forward references, cycles, and out-of-range IDs fail. -/
def run (algebra : Algebra α) : List Node → List α → Option (List α)
  | [], values => some values
  | node :: rest, values => do
    let value ← node.run algebra values
    run algebra rest (values ++ [value])

def expand (nodes : List Node) (root : Nat) : Option Expression := do
  let values ← run expressions nodes []
  values[root]?

def evaluate (nodes : List Node) (root : Nat) (ctx : Context) (locals : String → Word) : Option Word := do
  let values ← run (words ctx locals) nodes []
  values[root]?

theorem Node.run_map (node : Node) (values : List Expression) (storage : Word → Word)
    (ctx : Context) (locals : String → Word) :
    node.run (words ctx locals) (values.map (Expression.eval storage ctx locals)) =
      (node.run expressions values).map (Expression.eval storage ctx locals) := by
  cases node with
  | literal => rfl
  | input => rfl
  | nullary => rfl
  | unary op arg =>
    cases h : values[arg]? <;> simp [Node.run, List.getElem?_map, h, expressions, words, Expression.eval]
  | binary op left right =>
    cases h : values[left]? <;> cases k : values[right]? <;>
      simp [Node.run, List.getElem?_map, h, k, expressions, words, Expression.eval]
  | ternary op first second third =>
    cases h : values[first]? <;> cases k : values[second]? <;> cases m : values[third]? <;>
      simp [Node.run, List.getElem?_map, h, k, m, expressions, words, Expression.eval]

theorem run_map (nodes : List Node) (values : List Expression) (storage : Word → Word)
    (ctx : Context) (locals : String → Word) :
    run (words ctx locals) nodes (values.map (Expression.eval storage ctx locals)) =
      (run expressions nodes values).map (List.map (Expression.eval storage ctx locals)) := by
  induction nodes generalizing values with
  | nil => rfl
  | cons node rest ih =>
    simp only [run, Node.run_map]
    cases step : node.run expressions values with
    | none => simp
    | some value => simpa [step, List.map_append] using ih (values ++ [value])

theorem evaluate_expand (nodes : List Node) (root : Nat) (storage : Word → Word)
    (ctx : Context) (locals : String → Word) :
    evaluate nodes root ctx locals = (expand nodes root).map (Expression.eval storage ctx locals) := by
  have mapped := run_map nodes [] storage ctx locals
  simp only [List.map_nil] at mapped
  simp only [evaluate, expand, mapped]
  cases run expressions nodes [] <;> simp [List.getElem?_map]

def validate (fuel : Nat) (before after : List Node) (beforeRoot afterRoot : Nat) : Bool :=
  match expand before beforeRoot, expand after afterRoot with
  | some a, some b => equivalent fuel a b
  | _, _ => false

/-- Acceptance is non-vacuous: both complete graphs evaluate successfully to the
exact same `Word` for every EVM execution `Context` and every variable assignment. -/
theorem validate_sound (fuel : Nat) (before after : List Node) (beforeRoot afterRoot : Nat)
    (accepted : validate fuel before after beforeRoot afterRoot = true)
    (ctx : Context) (locals : String → Word) :
    ∃ value, evaluate before beforeRoot ctx locals = some value ∧
      evaluate after afterRoot ctx locals = some value := by
  cases left : expand before beforeRoot with
  | none => simp [validate, left] at accepted
  | some a =>
    cases right : expand after afterRoot with
    | none => simp [validate, left, right] at accepted
    | some b =>
      simp only [validate, left, right] at accepted
      let storage : Word → Word := fun _ => 0#256
      have equal := equivalent_sound fuel a b accepted storage ctx locals
      rw [evaluate_expand before beforeRoot storage ctx locals,
        evaluate_expand after afterRoot storage ctx locals, left, right]
      exact ⟨a.eval storage ctx locals, rfl, congrArg some equal.symm⟩

#audit_contract_proof Compiler.Validation.validate_sound

end Compiler.Validation
