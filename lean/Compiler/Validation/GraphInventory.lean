/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Validation.Graph

/-! Whole-graph and CSE cache inventory validation for `ExpressionClasses`.

Unlike vacuous contracts that guard postconditions behind `ordinary result = true`,
`Inventory.certify` proves unconditionally that:
1. Both source and optimized graphs evaluate without reference errors (`some left`, `some right`);
2. Every source node's returned representative ID evaluates to the exact source node value;
3. Every entry in the `ExpressionClasses` expression hash-map (`cache`) evaluates to the exact
   value of its mapped representative ID for all `ctx : Context` and `locals : String → Word`. -/
namespace Compiler.Validation.Inventory
open Contract Contract.Yul

abbrev observe (ctx : Context) (locals : String → Word) : Expression → Word :=
  Expression.eval ctx locals

structure Entry where
  key : Node
  id : Nat
  deriving DecidableEq, Repr

def results (fuel : Nat) (after : List Expression) : List Expression → List Nat → Bool
  | [], [] => true
  | value :: rest, id :: ids =>
    match after[id]? with
    | none => false
    | some actual => equivalent fuel value actual && results fuel after rest ids
  | _, _ => false

def entry (fuel : Nat) (after : List Expression) (binding : Entry) : Bool :=
  match binding.key.run expressions after, after[binding.id]? with
  | some key, some value => equivalent fuel key value
  | _, _ => false

/-- Every source-node result and every captured cache binding is checked.
Malformed representatives reject even when no selected result reaches them. -/
def validate (fuel : Nat) (before after : List Node) (ids : List Nat) (cache : List Entry) : Bool :=
  match run expressions before [], run expressions after [] with
  | some left, some right => results fuel right left ids && cache.all (entry fuel right)
  | _, _ => false

/-- Semantic preservation of all returned IDs and all CSE cache entries. -/
def Preserves (before after : List Node) (ids : List Nat) (cache : List Entry)
    (ctx : Context) (locals : String → Word) : Prop :=
  ∃ left right,
    run (words ctx locals) before [] = some left ∧
    run (words ctx locals) after [] = some right ∧
    ids.map (fun id => right[id]?) = left.map some ∧
    ∀ binding ∈ cache, ∃ value,
      binding.key.run (words ctx locals) right = some value ∧ right[binding.id]? = some value

theorem results_sound (fuel : Nat) (after before : List Expression) (ids : List Nat)
    (accepted : results fuel after before ids = true)
    (ctx : Context) (locals : String → Word) :
    ids.map (fun id => (after.map (observe ctx locals))[id]?) =
      (before.map (observe ctx locals)).map some := by
  induction before generalizing ids with
  | nil => cases ids <;> simp_all [results]
  | cons value rest ih =>
    cases ids with
    | nil => simp [results] at accepted
    | cons id ids =>
      cases found : after[id]? with
      | none => simp [results, found] at accepted
      | some actual =>
        simp only [results, found, Bool.and_eq_true] at accepted
        have same := equivalent_sound fuel value actual accepted.1 ctx locals
        have head : (after.map (observe ctx locals))[id]? = some (observe ctx locals value) := by
          simpa [List.getElem?_map, found, observe] using congrArg some same.symm
        simp only [List.map_cons, head, ih ids accepted.2]

theorem entry_sound (fuel : Nat) (after : List Expression) (binding : Entry)
    (accepted : entry fuel after binding = true)
    (ctx : Context) (locals : String → Word) :
    ∃ value, binding.key.run (words ctx locals) (after.map (observe ctx locals)) = some value ∧
      (after.map (observe ctx locals))[binding.id]? = some value := by
  cases key : binding.key.run expressions after with
  | none => simp [entry, key] at accepted
  | some keyValue =>
    cases found : after[binding.id]? with
    | none => simp [entry, key, found] at accepted
    | some actual =>
      have same := equivalent_sound fuel keyValue actual (by simpa [entry, key, found] using accepted)
        ctx locals
      refine ⟨observe ctx locals keyValue, ?_, ?_⟩
      · simpa [observe, key] using binding.key.run_map after ctx locals
      · simpa [List.getElem?_map, found, observe] using congrArg some same.symm

theorem validate_sound (fuel : Nat) (before after : List Node) (ids : List Nat) (cache : List Entry)
    (accepted : validate fuel before after ids cache = true)
    (ctx : Context) (locals : String → Word) :
    Preserves before after ids cache ctx locals := by
  cases left : run expressions before [] with
  | none => simp [validate, left] at accepted
  | some source =>
    cases right : run expressions after [] with
    | none => simp [validate, left, right] at accepted
    | some target =>
      simp only [validate, left, right, Bool.and_eq_true, List.all_eq_true] at accepted
      refine ⟨source.map (observe ctx locals), target.map (observe ctx locals), ?_, ?_,
        results_sound fuel target source ids accepted.1 ctx locals, ?_⟩
      · simpa [observe, left] using run_map before [] ctx locals
      · simpa [observe, right] using run_map after [] ctx locals
      · intro binding member
        exact entry_sound fuel target binding (accepted.2 binding member) ctx locals

theorem result_at (left right : List Word) (ids : List Nat)
    (related : ids.map (fun id => right[id]?) = left.map some)
    (root id : Nat) (selected : ids[root]? = some id) :
    ∃ value, left[root]? = some value ∧ right[id]? = some value := by
  have read := congrArg (fun values => values[root]?) related
  simp only [List.getElem?_map, selected, Option.map_some] at read
  cases found : left[root]? with
  | none => simp [found] at read
  | some value => exact ⟨value, rfl, Option.some.inj (by simpa [found] using read)⟩

/-- Complete inventory preservation and selected-root agreement from one certificate,
including 0-ary literals and environmental nullary opcodes (`#44`). -/
theorem certify (fuel : Nat) (before after : List Node) (ids : List Nat) (cache : List Entry)
    (beforeRoot afterRoot : Nat) (accepted : validate fuel before after ids cache = true)
    (selected : ids[beforeRoot]? = some afterRoot)
    (ctx : Context) (locals : String → Word) :
    Preserves before after ids cache ctx locals ∧
      ∃ value, evaluate before beforeRoot ctx locals = some value ∧
        evaluate after afterRoot ctx locals = some value := by
  have checked := validate_sound fuel before after ids cache accepted ctx locals
  refine ⟨checked, ?_⟩
  obtain ⟨left, right, source, target, related, _⟩ := checked
  obtain ⟨value, first, second⟩ := result_at left right ids related beforeRoot afterRoot selected
  exact ⟨value, by simp [evaluate, source, first], by simp [evaluate, target, second]⟩

#audit_contract_proof Compiler.Validation.Inventory.validate_sound
#audit_contract_proof Compiler.Validation.Inventory.certify

end Compiler.Validation.Inventory
