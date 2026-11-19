/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.StorageEffects

namespace Compiler.Extraction.Storage.EffectTests

structure Trace where
  calls : List Allocation := []
  cursor : Nat := 0
  deriving DecidableEq, Repr

/-- Controlled primitive outcomes, not a claim about allocation counts inside
the native clone or containers. Even a failing call retains its event. -/
def attempt (failAt : Nat) (site : Allocation) (before : Trace) : Bool × Trace :=
  (before.cursor != failAt, ⟨before.calls ++ [site], before.cursor + 1⟩)

def run (failAt : Nat) (deterministic room : Bool) (before : Trace := {}) :=
  insertProgram.runWith ⟨deterministic, room, fun _ => false⟩ (attempt failAt) {} before

theorem safe (failAt : Nat) (deterministic room : Bool) (before : Trace) :
    SafeResult deterministic (run failAt deterministic room before).1 := insert_effect_safe _ _ _

def successful := run 5 true true
def repeated := run 5 true true successful.2
def failedPublication := run 4 true true

theorem complete_order : successful.1.1 = some .success ∧
    successful.2 = ⟨[.arguments, .item, .clone, .append, .publish], 5⟩ := ⟨rfl, rfl⟩
theorem nondeterministic_order : (run 9 false true).1.1 = some .success ∧
    (run 9 false true).2 = ⟨[.item, .clone, .append], 3⟩ := ⟨rfl, rfl⟩
theorem repeated_failure : repeated.1.1 = some .allocationFailure ∧
    repeated.2 = ⟨[.arguments, .item, .clone, .append, .publish, .arguments], 6⟩ := ⟨rfl, rfl⟩
theorem publication_rollback : Released failedPublication.1.2 := safe 4 true true {}

example : (run 0 true true).2 = ⟨[.arguments], 1⟩ := by rfl
example : (run 1 true true).2 = ⟨[.arguments, .item], 2⟩ := by rfl
example : (run 2 true true).2 = ⟨[.arguments, .item, .clone], 3⟩ := by rfl
example : (run 3 true true).2 = ⟨[.arguments, .item, .clone, .append], 4⟩ := by rfl
example : failedPublication.2 = ⟨[.arguments, .item, .clone, .append, .publish], 5⟩ := by rfl
example : failedPublication.1.2.appended = false := by rfl
example : failedPublication.1.2.published = false := by rfl
example : (run 0 true false).2 = ({} : Trace) := by rfl
example : (run 0 false true).2 = ⟨[.item], 1⟩ := by rfl

-- A successful primitive can consume no allocator event, or several. The
-- source program counts primitive calls only through the supplied callback.
-- This fixture policy does not specify native container allocation behavior.
def variableAttempt (site : Allocation) (before : Trace) : Bool × Trace :=
  (true, ⟨before.calls ++ [site], before.cursor +
    (match site with | .clone => 0 | .append => 2 | _ => 1)⟩)
def variableResult := insertProgram.runWith ⟨true, true, fun _ => false⟩ variableAttempt {} ({} : Trace)
theorem variable_safe : SafeResult true variableResult.1 :=
  insert_effect_safe ⟨true, true, fun _ => false⟩ variableAttempt ({} : Trace)
example : variableResult.1.1 = some .success := by rfl
example : variableResult.2 = ⟨[.arguments, .item, .clone, .append, .publish], 5⟩ := by rfl
example : (variableAttempt .clone ⟨[.item], 1⟩).2 = ⟨[.item, .clone], 1⟩ := by rfl
example : (variableAttempt .append ⟨[.item, .clone], 1⟩).2 = ⟨[.item, .clone, .append], 3⟩ := by rfl

end Compiler.Extraction.Storage.EffectTests
