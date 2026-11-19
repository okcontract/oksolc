/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.StorageProofs

namespace Compiler.Extraction.Storage

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

private theorem failure_beq_success : (Outcome.allocationFailure == Outcome.success) = false := rfl

/-- Cleanup changes the owned resources, retaining all private effects from the
body even on an error. This holds for every extracted program, not one trace. -/
theorem scope_retains_effects (input : Input) (attempt : Allocation → σ → Bool × σ)
    (errorOnly : Bool) (cleanup : Cleanup) (body : Program) (state : State) (effects : σ) :
    ((Program.scope errorOnly cleanup body).runWith input attempt state effects).2 =
      (body.runWith input attempt state effects).2 := by
  simp only [Program.runWith]
  split <;> rfl

/-- A ghost policy for the existing ownership proof. Later entries describe
hypothetical continuation after an earlier failure; `runWith` never executes
those callbacks. The projection theorem checks this order against the extracted
source program, including the non-deterministic branch that skips duplication.
Each primitive can consume zero, one or several allocator events internally. -/
def effectPolicy (deterministic : Bool) (attempt : Allocation → σ → Bool × σ)
    (effects : σ) : Allocation → Bool :=
  let arguments := if deterministic then attempt .arguments effects else (true, effects)
  let item := attempt .item arguments.2
  let clone := attempt .clone item.2
  let append := attempt .append clone.2
  let publish := attempt .publish append.2
  allocationPolicy arguments.1 item.1 clone.1 append.1 publish.1

/-- All effectful executions project to a checked ownership execution. No
independence, monotonicity or rollback assumption is imposed on private effects.
The equality covers the entire ownership state and every exit, not just success. -/
theorem insert_effect_projection (input : Input) (attempt : Allocation → σ → Bool × σ)
    (state : State) (effects : σ) :
    (insertProgram.runWith input attempt state effects).1 =
      insertProgram.run { input with succeeds := effectPolicy input.deterministic attempt effects } state := by
  rcases input with ⟨deterministic, room, ignored⟩
  cases room with
  | false => rfl
  | true =>
    cases deterministic with
    | false =>
      cases item : attempt .item effects with
      | mk i si =>
        cases clone : attempt .clone si with
        | mk c sc =>
          cases append : attempt .append sc with
          | mk a sa =>
            cases i <;> cases c <;> cases a <;>
              simp [insertProgram, Program.run, Program.runWith, Command.runWith,
                Command.allocation, Test.eval, effectPolicy, allocationPolicy, failure_beq_success,
                item, clone, append] <;> first | rfl | exact ⟨rfl, rfl⟩
    | true =>
      cases arguments : attempt .arguments effects with
      | mk a sa =>
        cases item : attempt .item sa with
        | mk i si =>
          cases clone : attempt .clone si with
          | mk c sc =>
            cases append : attempt .append sc with
            | mk p sp =>
              cases publish : attempt .publish sp with
              | mk u su =>
                cases a <;> cases i <;> cases c <;> cases p <;> cases u <;>
                  simp [insertProgram, Program.run, Program.runWith, Command.runWith,
                    Command.allocation, Test.eval, effectPolicy, allocationPolicy, failure_beq_success,
                    arguments, item, clone, append, publish] <;> first | rfl | exact ⟨rfl, rfl⟩

theorem insert_effect_safe (input : Input) (attempt : Allocation → σ → Bool × σ) (effects : σ) :
    SafeResult input.deterministic (insertProgram.runWith input attempt {} effects).1 := by
  rw [insert_effect_projection]
  exact insert_safe_any _

/-- Source capacity rejection precedes all fallible primitive calls. -/
theorem insert_effect_capacity (deterministic : Bool) (ignored : Allocation → Bool)
    (attempt : Allocation → σ → Bool × σ) (effects : σ) :
    (insertProgram.runWith ⟨deterministic, false, ignored⟩ attempt {} effects).1.1 = some .capacityFailure ∧
    (insertProgram.runWith ⟨deterministic, false, ignored⟩ attempt {} effects).2 = effects := ⟨rfl, rfl⟩

end Compiler.Extraction.Storage
