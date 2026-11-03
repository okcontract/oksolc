/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionDeinitProgram

namespace Compiler.Extraction.ExpressionDeinit
open Compiler.Extraction.Storage Compiler.Extraction.Memory
open Compiler.Extraction.Memory.Arguments
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.ZigAir.Memory.WordArray

def run (items : Items σ ε) (external : External σ) (allocator : Nat)
    (descriptor : Descriptor) (before : Session σ) : Except (Fault ε) Unit × State σ :=
  execute items.operations external allocator descriptor expressionDeinitCode ⟨before, false⟩

/-- Exact source order and effects, including each rejected operation. -/
theorem execute_equation (items : Operations σ ε) (external : External σ) (allocator : Nat)
    (descriptor : Descriptor) (before : Session σ) :
    execute items external allocator descriptor expressionDeinitCode ⟨before, false⟩ =
      let (valueResult, valueState) := items.deinit descriptor.item before
      match valueResult with
      | .error fault => (.error (.item fault), ⟨valueState, false⟩)
      | .ok () =>
        let (allocationResult, allocationState) := items.destroy descriptor.item valueState
        match allocationResult with
        | .error fault => (.error (.item fault), ⟨allocationState, false⟩)
        | .ok () =>
          let (argumentsResult, argumentState) := free external allocator descriptor.arguments allocationState
          match argumentsResult with
          | .error fault => (.error (.arguments fault), ⟨argumentState, false⟩)
          | .ok () => (.ok (), ⟨argumentState, true⟩) := by
  cases valueCall : items.deinit descriptor.item before with
  | mk valueResult valueState =>
    cases valueResult with
    | error fault => simp [execute, expressionDeinitCode, Stage.execute, itemStep, Except.mapError, valueCall]
    | ok returned =>
      cases returned
      dsimp only
      cases allocationCall : items.destroy descriptor.item valueState with
      | mk allocationResult allocationState =>
        cases allocationResult with
        | error fault => simp [execute, expressionDeinitCode, Stage.execute, itemStep, Except.mapError, valueCall, allocationCall]
        | ok returned =>
          cases returned
          cases argumentCall : free external allocator descriptor.arguments allocationState with
          | mk argumentsResult argumentState =>
            cases argumentsResult with
            | error fault => simp [execute, expressionDeinitCode, Stage.execute, itemStep, Except.mapError, valueCall, allocationCall, argumentCall]
            | ok returned =>
              cases returned
              simp [execute, expressionDeinitCode, Stage.execute, itemStep, Except.mapError, valueCall, allocationCall, argumentCall]

/-- Exact source order and effects, including each rejected operation. -/
theorem run_equation (items : Items σ ε) (external : External σ) (allocator : Nat)
    (descriptor : Descriptor) (before : Session σ) :
    run items external allocator descriptor before =
      let (valueResult, valueEffects) := items.deinit descriptor.item before
      let valueState := { before with effects := valueEffects }
      match valueResult with
      | .error fault => (.error (.item fault), ⟨valueState, false⟩)
      | .ok () =>
        let (allocationResult, allocationEffects) := items.destroy descriptor.item valueState
        let allocationState := { valueState with effects := allocationEffects }
        match allocationResult with
        | .error fault => (.error (.item fault), ⟨allocationState, false⟩)
        | .ok () =>
          let (argumentsResult, argumentState) := free external allocator descriptor.arguments allocationState
          match argumentsResult with
          | .error fault => (.error (.arguments fault), ⟨argumentState, false⟩)
          | .ok () => (.ok (), ⟨argumentState, true⟩) := by
  simpa only [run, Items.operations] using
    execute_equation items.operations external allocator descriptor before

/-- Argument lifetime and typed frames of the whole destructor under the framed
item interfaces. Item allocation/payload ownership is not asserted here. -/
structure Post (descriptor : Descriptor) (before : Session σ)
    (execution : Except (Fault ε) Unit × State σ) : Prop where
  valid : Valid execution.2.memory
  nextId : execution.2.memory.memory.nextId = before.memory.nextId
  nextAddress : execution.2.memory.memory.nextAddress = before.memory.nextAddress
  frame : ∀ id, id ≠ descriptor.arguments.address →
    execution.2.memory.heap id = before.heap id ∧
    execution.2.memory.memory.heap.lookup id = before.memory.heap.lookup id
  outcome : match execution.1 with
    | .ok () => Consumed descriptor.arguments execution.2.memory ∧ execution.2.invalidated = true
    | .error (.item _) => execution.2.memory.heap = before.heap ∧
        execution.2.memory.memory = before.memory ∧ execution.2.invalidated = false
    | .error _ => False

theorem run_verified (items : Items σ ε) (external : External σ) (allocator : Nat)
    (descriptor : Descriptor) (before : Session σ) (valid : Valid before)
    (live : SliceValid allocator before.heap descriptor.arguments) :
    Post descriptor before (run items external allocator descriptor before) := by
  rw [run_equation]
  cases valueCall : items.deinit descriptor.item before with
  | mk valueResult valueEffects =>
    cases valueResult with
    | error fault =>
      exact ⟨⟨valid.memory, valid.related, valid.injected⟩, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
    | ok returned =>
      cases returned
      dsimp only
      cases allocationCall : items.destroy descriptor.item { before with effects := valueEffects } with
      | mk allocationResult allocationEffects =>
        cases allocationResult with
        | error fault =>
          simp only [allocationCall]
          exact ⟨⟨valid.memory, valid.related, valid.injected⟩, rfl, rfl, fun _ _ => ⟨rfl, rfl⟩, rfl, rfl, rfl⟩
        | ok returned =>
          cases returned
          simp only [allocationCall]
          obtain ⟨after, released, afterValid, post, _⟩ := free_valid external allocator descriptor.arguments
            { before with effects := allocationEffects } ⟨valid.memory, valid.related, valid.injected⟩ live
          simp only [released]
          exact ⟨afterValid, post.nextId, post.nextAddress, post.frame, released_consumed post, rfl⟩

theorem Post.preserves_borrow (descriptor : Descriptor) (before : Session σ)
    (execution : Except (Fault ε) Unit × State σ) (post : Post descriptor before execution)
    (source : View) (values : List Compiler.Algebraic.NodeId)
    (represented : Represents before.memory source values)
    (separate : values ≠ [] → source.allocation ≠ descriptor.arguments.address) :
    Represents execution.2.memory.memory source values := by
  by_cases empty : values = []
  · subst values
    exact ⟨represented.1, fun _ impossible => False.elim (by simp at impossible)⟩
  · exact represented_frame source values represented (post.frame _ (separate empty)).2

end Compiler.Extraction.ExpressionDeinit
