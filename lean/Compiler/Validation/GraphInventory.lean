/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.Graph

namespace Compiler.Validation.Inventory
open Contract.Yul

abbrev observe (locals : String → Word) : Expression → Word :=
  Expression.eval (fun _ => 0) ⟨0, 0⟩ locals

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

/-- This relation covers all returned IDs, not just the selected root. Cache
validity states the exact property needed by a later lookup in this captured
graph. It does not assert that an unobserved future graph mutation is safe. -/
def Preserves (before after : List Node) (ids : List Nat) (cache : List Entry)
    (locals : String → Word) : Prop :=
  ∃ left right,
    run (words locals) before [] = some left ∧ run (words locals) after [] = some right ∧
    ids.map (fun id => right[id]?) = left.map some ∧
    ∀ binding ∈ cache, ∃ value,
      binding.key.run (words locals) right = some value ∧ right[binding.id]? = some value

theorem results_sound (fuel : Nat) (after before : List Expression) (ids : List Nat)
    (accepted : results fuel after before ids = true) (locals : String → Word) :
    ids.map (fun id => (after.map (observe locals))[id]?) = (before.map (observe locals)).map some := by
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
        have same := equivalent_sound fuel value actual accepted.1 (fun _ => 0) ⟨0, 0⟩ locals
        have head : (after.map (observe locals))[id]? = some (observe locals value) := by
          simpa [List.getElem?_map, found, observe] using congrArg some same.symm
        simp only [List.map_cons, head, ih ids accepted.2]

theorem entry_sound (fuel : Nat) (after : List Expression) (binding : Entry)
    (accepted : entry fuel after binding = true) (locals : String → Word) :
    ∃ value, binding.key.run (words locals) (after.map (observe locals)) = some value ∧
      (after.map (observe locals))[binding.id]? = some value := by
  cases key : binding.key.run expressions after with
  | none => simp [entry, key] at accepted
  | some keyValue =>
    cases found : after[binding.id]? with
    | none => simp [entry, key, found] at accepted
    | some actual =>
      have same := equivalent_sound fuel keyValue actual (by simpa [entry, key, found] using accepted)
        (fun _ => 0) ⟨0, 0⟩ locals
      refine ⟨observe locals keyValue, ?_, ?_⟩
      · simpa [observe, key] using binding.key.run_map after (fun _ => 0) ⟨0, 0⟩ locals
      · simpa [List.getElem?_map, found, observe] using congrArg some same.symm

theorem validate_sound (fuel : Nat) (before after : List Node) (ids : List Nat) (cache : List Entry)
    (accepted : validate fuel before after ids cache = true) (locals : String → Word) :
    Preserves before after ids cache locals := by
  cases left : run expressions before [] with
  | none => simp [validate, left] at accepted
  | some source =>
    cases right : run expressions after [] with
    | none => simp [validate, left, right] at accepted
    | some target =>
      simp only [validate, left, right, Bool.and_eq_true, List.all_eq_true] at accepted
      refine ⟨source.map (observe locals), target.map (observe locals), ?_, ?_,
        results_sound fuel target source ids accepted.1 locals, ?_⟩
      · simpa [observe, left] using run_map before [] (fun _ => 0) ⟨0, 0⟩ locals
      · simpa [observe, right] using run_map after [] (fun _ => 0) ⟨0, 0⟩ locals
      · intro binding member
        exact entry_sound fuel target binding (accepted.2 binding member) locals

theorem result_at (left right : List Word) (ids : List Nat)
    (related : ids.map (fun id => right[id]?) = left.map some)
    (root id : Nat) (selected : ids[root]? = some id) :
    ∃ value, left[root]? = some value ∧ right[id]? = some value := by
  have read := congrArg (fun values => values[root]?) related
  simp only [List.getElem?_map, selected, Option.map_some] at read
  cases found : left[root]? with
  | none => simp [found] at read
  | some value => exact ⟨value, rfl, Option.some.inj (by simpa [found] using read)⟩

/-- Complete inventory preservation and the existing selected-root observation
come from one certificate. No caller-supplied value or cache-validity oracle is
used; both graphs must evaluate successfully for every variable environment. -/
theorem certify (fuel : Nat) (before after : List Node) (ids : List Nat) (cache : List Entry)
    (beforeRoot afterRoot : Nat) (accepted : validate fuel before after ids cache = true)
    (selected : ids[beforeRoot]? = some afterRoot) (locals : String → Word) :
    Preserves before after ids cache locals ∧
      ∃ value, evaluate before beforeRoot locals = some value ∧ evaluate after afterRoot locals = some value := by
  have checked := validate_sound fuel before after ids cache accepted locals
  refine ⟨checked, ?_⟩
  obtain ⟨left, right, source, target, related, _⟩ := checked
  obtain ⟨value, first, second⟩ := result_at left right ids related beforeRoot afterRoot selected
  exact ⟨value, by simp [evaluate, source, first], by simp [evaluate, target, second]⟩

end Compiler.Validation.Inventory
