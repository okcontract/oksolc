/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WyhashUpdateAirLongExecution

namespace Compiler.ZigAir.WyhashUpdateAir.Index
open Memory AggregateAir Compiler.Extraction Control.Machine
abbrev Code := Round.Code

def guard : Code := (GeneratedWyhashUpdate.update.body.blockBody? 52).getD (.ret (.constant (.value (.scalar .unit))))
def continuation : Code := .block 52 (.scalar .unit) guard Loop.entry

theorem generated_entry : longBody =
    .bind 50 (.pointer true false usize) (.primitive (.memory (.alloc usize)))
      (.bind 51 (.scalar .unit) (.primitive (.store (.local 50) (.constant (.value (.scalar (.int false 64 0)))))) continuation) := by
  decide +kernel

def resultEnv (env : Env) (id : Nat) : Env :=
  (env.set 50 (.value (slot true usize id))).set 51 (.value (.scalar .unit))

theorem allocate_steps (state : State) (valid : state.valid = true)
    (args : List Register) (env : Env) (outer : List (Frame Ty AggregateCall.Prim Ref)) :
    ∃ after, StackFrame state after ∧
      (Steps AggregateCall.semantics args (.suspended ⟨longBody, env, state, outer⟩)
        (.finished (.fault .outOfMemory after)) ∨
       Steps AggregateCall.semantics args (.suspended ⟨longBody, env, state, outer⟩)
        (.suspended ⟨continuation, resultEnv env state.nextId, after, outer⟩) ∧
       Memory.load after (slot true usize state.nextId) = .ok (.scalar (.int false 64 0)) ∧
       after.nextAddress < addressLimit ∧
       ∃ counter : CellFrame after state.nextId,
         counter.cell.type = usize ∧ counter.cell.cells.valid usize = true) := by
  have head := AggregateCall.save_steps (.scalar (.int false 64 0)) (.constant (.value (.scalar (.int false 64 0))))
    50 51 continuation outer args env state rfl
  obtain ⟨result, after, ran, stack, failed | ⟨success, read, _⟩⟩ :=
    SavedValue.verified state (.scalar (.int false 64 0)) ⟨8, 8⟩ valid rfl rfl (by decide)
  · rw [failed] at ran
    rw [ran] at head
    exact ⟨after, stack, Or.inl (by rw [generated_entry]; exact head)⟩
  · rw [success] at ran
    rw [ran] at head
    exact ⟨after, stack, Or.inr ⟨by rw [generated_entry]; exact head, read,
      (SavedValue.success_cursors state after _ ran).2,
      SavedValue.owned state after _ ⟨8, 8⟩ rfl rfl (by decide) ran⟩⟩

/-- Rewrite the owned loop index without assuming a successful store. -/
theorem store {state : State} {id : Nat} (counter : CellFrame state id)
    (typed : counter.cell.type = usize) (valid : counter.cell.cells.valid usize = true)
    (value : Nat) (bound : value < addressLimit) :
    ∃ cells, Memory.store state (slot true usize id) (.scalar (.int false 64 value)) = .ok (counter.install cells) ∧
      cells.valid usize = true ∧
      Memory.load (counter.install cells) (slot true usize id) = .ok (.scalar (.int false 64 value)) := by
  have valueValid : (Value.scalar (.int false 64 value)).valid = true := Scalar.unsigned_nat_valid _ _ bound
  obtain ⟨cells, written⟩ := Cells.write_root counter.cell.cells (.scalar (.int false 64 value)) valueValid
  change counter.cell.cells.write usize 0 (.scalar (.int false 64 value)) = .ok cells at written
  have stored := counter.store_current (.scalar (.int false 64 value))
    (by simpa [Value.hasType, typed, Value.type, Scalar.Value.type, usize] using valueValid)
  rw [typed, written] at stored
  exact ⟨cells, stored, Cells.write_preserves_valid _ _ _ _ _ valid written,
    load_after_store state (slot true usize id) (.scalar (.int false 64 value)) (counter.install cells) stored⟩

end Compiler.ZigAir.WyhashUpdateAir.Index
