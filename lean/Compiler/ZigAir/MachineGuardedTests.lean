/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MachineGuarded
import Compiler.ZigAir.ControlTests

namespace Compiler.ZigAir.MachineGuardedTests
open Control Control.Machine ControlTests

def checked (event : Observation Bool Prim Nat (List Nat)) : Prop :=
  (event.site.1 = 0 ∧ event.state = []) ∨ (event.site.1 = 1 ∧ event.state = [7])

def code : Code Bool Prim Ref true := .bind 0 true (.record 7) (.bind 1 true (.fail 9) (.ret (.literal 0)))
def start : Execution Bool Prim Ref Nat Fault (List Nat) := .suspended ⟨code, fun _ => none, [], []⟩

theorem failing_path : GuardedSteps semantics [] checked start (.finished (.fault .operation [7, 9])) := by
  apply GuardedSteps.bind_ok semantics [] checked (by exact Or.inl ⟨rfl, rfl⟩) rfl rfl
  exact GuardedSteps.bind_fault semantics [] checked (by exact Or.inr ⟨rfl, rfl⟩) rfl

theorem failing_prefixes (fuel : Nat) : ∀ event ∈ (trace semantics [] fuel start).1, checked event :=
  failing_path.terminal_trace semantics [] checked fuel

theorem unchecked_attempt_rejected : ¬ GuardedSteps semantics [] (fun _ => False) start (.finished (.fault .operation [7, 9])) := by
  intro path
  cases path with
  | step config checked _ => exact checked ⟨(0, true, .record 7), fun _ => none, []⟩ (by simp [observe, code])

/-- A reflexive suspended prefix says nothing about subsequent attempts. -/
theorem suspension_is_not_terminal_evidence :
    GuardedSteps semantics [] (fun _ => False) start start ∧
      ∃ event, event ∈ (trace semantics [] 1 start).1 ∧ ¬(False : Prop) := by
  exact ⟨.refl _, ⟨⟨(0, true, .record 7), fun _ => none, []⟩, by simp [trace, start, code, observe], id⟩⟩

end Compiler.ZigAir.MachineGuardedTests
