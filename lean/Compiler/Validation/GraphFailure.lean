/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.GraphInventory

namespace Compiler.Validation.Failure
open Contract.Yul

inductive Outcome where
  | complete | outOfMemory
  deriving DecidableEq, Repr

/-- The actual reached graph, including nodes created by a recursive call that
later failed. Only successfully returned source IDs belong to the prefix. -/
structure Attempt where
  outcome : Outcome
  after : List Node
  ids : List Nat
  cache : List Inventory.Entry
  deriving DecidableEq, Repr

def Progress (before : List Node) (attempt : Attempt) : Prop :=
  match attempt.outcome with
  | .complete => attempt.ids.length = before.length
  | .outOfMemory => attempt.ids.length < before.length

instance (before : List Node) (attempt : Attempt) : Decidable (Progress before attempt) := by
  unfold Progress
  cases attempt.outcome <;> infer_instance

def validateAttempt (fuel : Nat) (before : List Node) (attempt : Attempt) : Bool :=
  decide (Progress before attempt) &&
    Inventory.validate fuel (before.take attempt.ids.length) attempt.after attempt.ids attempt.cache

/-- Failure is not a successful compilation, and no rollback is inferred.
Every retained representative is well formed; all earlier results and all
captured cache entries have their meaning in the reached graph. -/
def Preserves (before : List Node) (attempt : Attempt) (locals : String → Word) : Prop :=
  Progress before attempt ∧
    Inventory.Preserves (before.take attempt.ids.length) attempt.after attempt.ids attempt.cache locals

theorem attempt_sound (fuel : Nat) (before : List Node) (attempt : Attempt)
    (accepted : validateAttempt fuel before attempt = true) (locals : String → Word) :
    Preserves before attempt locals := by
  simp only [validateAttempt, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact ⟨accepted.1, Inventory.validate_sound fuel _ _ _ _ accepted.2 locals⟩

/-- A nonempty observation family. Native failure-index coverage is checked by
the artifact binding layer; the kernel establishes semantics for every member. -/
def validate (fuel : Nat) (before : List Node) (attempts : List Attempt) : Bool :=
  !attempts.isEmpty && attempts.all (validateAttempt fuel before)

theorem certify (fuel : Nat) (before : List Node) (attempts : List Attempt)
    (accepted : validate fuel before attempts = true) (locals : String → Word) :
    attempts ≠ [] ∧ ∀ attempt ∈ attempts, Preserves before attempt locals := by
  simp only [validate, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    List.all_eq_true] at accepted
  exact ⟨accepted.1, fun attempt member => attempt_sound fuel before attempt (accepted.2 attempt member) locals⟩

end Compiler.Validation.Failure
