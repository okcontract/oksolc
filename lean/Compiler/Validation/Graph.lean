/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Validation.Normalize

/-! Dense, topologically ordered graph input for the production-pass validator.
This representation records actual node references, unlike a tree that could
hide malformed references or cyclic output during unchecked expansion. -/
namespace Compiler.Validation
open Contract.Yul

inductive Node where
  | literal (value : Nat)
  | input (name : String)
  | unary (op : Unary) (arg : Nat)
  | binary (op : Binary) (left right : Nat)
  deriving DecidableEq, Repr

structure Algebra (α : Type) where
  literal : Nat → α
  input : String → α
  unary : Unary → α → α
  binary : Binary → α → α → α

def Node.run (algebra : Algebra α) (values : List α) : Node → Option α
  | .literal n => some (algebra.literal n)
  | .input name => some (algebra.input name)
  | .unary op arg => do return algebra.unary op (← values[arg]?)
  | .binary op left right => do return algebra.binary op (← values[left]?) (← values[right]?)

def expressions : Algebra Expression := ⟨.literal, .variable, .unary, .binary⟩
def words (locals : String → Word) : Algebra Word := ⟨BitVec.ofNat 256, locals, Unary.eval, Binary.eval⟩

/-- Reject every invalid reference, including in an unused node. Only earlier
nodes are available, so forward references, cycles and out-of-range IDs fail. -/
def run (algebra : Algebra α) : List Node → List α → Option (List α)
  | [], values => some values
  | node :: rest, values => do
    let value ← node.run algebra values
    run algebra rest (values ++ [value])

def expand (nodes : List Node) (root : Nat) : Option Expression := do
  let values ← run expressions nodes []
  values[root]?

def evaluate (nodes : List Node) (root : Nat) (locals : String → Word) : Option Word := do
  let values ← run (words locals) nodes []
  values[root]?

theorem Node.run_map (node : Node) (values : List Expression) (storage : Word → Word)
    (ctx : Contract.Context) (locals : String → Word) :
    node.run (words locals) (values.map (Expression.eval storage ctx locals)) =
      (node.run expressions values).map (Expression.eval storage ctx locals) := by
  cases node with
  | literal => rfl
  | input => rfl
  | unary op arg =>
    cases h : values[arg]? <;> simp [Node.run, List.getElem?_map, h, expressions, words, Expression.eval]
  | binary op left right =>
    cases h : values[left]? <;> cases k : values[right]? <;>
      simp [Node.run, List.getElem?_map, h, k, expressions, words, Expression.eval]

theorem run_map (nodes : List Node) (values : List Expression) (storage : Word → Word)
    (ctx : Contract.Context) (locals : String → Word) :
    run (words locals) nodes (values.map (Expression.eval storage ctx locals)) =
      (run expressions nodes values).map (List.map (Expression.eval storage ctx locals)) := by
  induction nodes generalizing values with
  | nil => rfl
  | cons node rest ih =>
    simp only [run, Node.run_map]
    cases step : node.run expressions values with
    | none => simp
    | some value => simpa [step, List.map_append] using ih (values ++ [value])

theorem evaluate_expand (nodes : List Node) (root : Nat) (storage : Word → Word)
    (ctx : Contract.Context) (locals : String → Word) :
    evaluate nodes root locals = (expand nodes root).map (Expression.eval storage ctx locals) := by
  have mapped := run_map nodes [] storage ctx locals
  simp only [List.map_nil] at mapped
  simp only [evaluate, expand, mapped]
  cases run expressions nodes [] <;> simp [List.getElem?_map]

def validate (fuel : Nat) (before after : List Node) (beforeRoot afterRoot : Nat) : Bool :=
  match expand before beforeRoot, expand after afterRoot with
  | some a, some b => equivalent fuel a b
  | _, _ => false

/-- Acceptance is non-vacuous: both complete graphs evaluate successfully and
the selected roots agree for every variable environment. Neither invalid graph
nor two failed executions can establish this proposition. -/
theorem validate_sound (fuel : Nat) (before after : List Node) (beforeRoot afterRoot : Nat)
    (accepted : validate fuel before after beforeRoot afterRoot = true)
    (locals : String → Word) :
    ∃ value, evaluate before beforeRoot locals = some value ∧
      evaluate after afterRoot locals = some value := by
  cases left : expand before beforeRoot with
  | none => simp [validate, left] at accepted
  | some a =>
    cases right : expand after afterRoot with
    | none => simp [validate, left, right] at accepted
    | some b =>
      simp only [validate, left, right] at accepted
      let storage : Word → Word := fun _ => 0
      let ctx : Contract.Context := ⟨0, 0⟩
      have equal := equivalent_sound fuel a b accepted storage ctx locals
      rw [evaluate_expand before beforeRoot storage ctx locals,
        evaluate_expand after afterRoot storage ctx locals, left, right]
      exact ⟨a.eval storage ctx locals, rfl, congrArg some equal.symm⟩

end Compiler.Validation
