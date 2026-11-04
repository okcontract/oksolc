/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyPreparationEffects

namespace Compiler.Extraction.AssemblyItem.Creation
open Compiler.Algebraic Compiler.Extraction.Memory.Arguments.Normalization

namespace Insertion
variable {project : σ → τ} {leftCreate : Allocate σ} {rightCreate : Allocate τ}
  {leftCopy : AssemblyClone.Physical.Allocate σ} {rightCopy : AssemblyClone.Physical.Allocate τ}
  (creation : HostTransport project leftCreate rightCreate) (cloning : HostTransport project leftCopy rightCopy)
  (leftBytes : AssemblyItemDeinit.Release σ) (rightBytes : AssemblyItemDeinit.Release τ)
  (leftObjects : AssemblyItem.Release σ) (rightObjects : AssemblyItem.Release τ)
  (leftExternal : External σ) (rightExternal : External τ) (allocator : Nat) (input : AssemblyClone.Value Metadata)
  (leftArguments : Storage.State → AssemblyClone.Physical.Insertion.State Metadata σ → Storage.ArgumentSlice)
  (rightArguments : Storage.State → AssemblyClone.Physical.Insertion.State Metadata τ → Storage.ArgumentSlice)
  (leftRest : Storage.Operations (State Metadata σ) Fault) (rightRest : Storage.Operations (State Metadata τ) Fault)
  (rest : ∀ site owner, Effect.Transport (State.mapEffects project)
    (leftRest.attempt site owner) (rightRest.attempt site owner))
include creation cloning rest

/-- Derive the allocation/clone callbacks from their actual bodies. Destructors
and descriptor selectors are unused by these attempts and need no premise here;
their release transport is a separate obligation. -/
theorem attempt_transport (site : Storage.Allocation) (owner : Storage.State) :
    Effect.Transport (State.mapEffects project)
      ((operations leftCreate leftCopy leftBytes leftObjects leftExternal allocator input leftArguments leftRest).attempt site owner)
      ((operations rightCreate rightCopy rightBytes rightObjects rightExternal allocator input rightArguments rightRest).attempt site owner) := by
  intro before
  cases site with
  | arguments | append | publish => exact rest _ owner before
  | item =>
    unfold operations
    simp only [show (before.mapEffects project).object = before.object from rfl,
      show (before.mapEffects project).clone.execution.memory = before.clone.execution.memory.mapEffects project from rfl]
    split
    · rfl
    · rw [create_transport project creation]
      cases create leftCreate allocator input.item before.clone.execution.memory with
      | mk result reached =>
        cases result with
        | ok object => rfl
        | error fault => cases fault <;> rfl
  | clone =>
    unfold operations
    simp only [show (before.mapEffects project).object = before.object from rfl]
    cases before.object with
    | none => rfl
    | some object =>
      simp only [cloneOperations, AssemblyClone.Physical.Insertion.operations,
        show (before.mapEffects project).clone.execution.memory = before.clone.execution.memory.mapEffects project from rfl]
      rw [AssemblyClone.Physical.run_transport project cloning]
      cases AssemblyClone.Physical.run leftCopy allocator input before.clone.execution.memory with
      | mk result reached =>
        cases result with
        | ok copied => rfl
        | error fault => cases fault <;> rfl

end Insertion

namespace NativeFields

theorem installResult_transport (project : σ → τ)
    (result : Except Compiler.ZigAir.Memory.Fault (Session σ)) (reached : State σ) :
    installResult (result.map (Session.mapEffects project)) (reached.mapEffects project) =
      ((installResult result reached).1, (installResult result reached).2.mapEffects project) := by
  cases result <;> rfl

theorem finish_transport (project : σ → τ) (object : Nat) (result : Except Insertion.Fault Bool) (reached : State σ) :
    finish object result (reached.mapEffects project) = ((finish object result reached).1, (finish object result reached).2.mapEffects project) := by
  unfold finish
  cases result with
  | error fault => rfl
  | ok success =>
    cases success with
    | false => rfl
    | true =>
      simp only [show (reached.mapEffects project).clone.value = reached.clone.value from rfl]
      cases reached.clone.value with
      | none => rfl
      | some copied =>
        simp only [show (reached.mapEffects project).clone.execution.memory = reached.clone.execution.memory.mapEffects project from rfl]
        rw [AssemblyClone.NativeFields.install_transport project]
        exact installResult_transport project (AssemblyClone.NativeFields.install copied object reached.clone.execution.memory) reached

variable {project : σ → τ} {leftCreate : Allocate σ} {rightCreate : Allocate τ}
  {leftCopy : AssemblyClone.Physical.Allocate σ} {rightCopy : AssemblyClone.Physical.Allocate τ}
  (creation : HostTransport project leftCreate rightCreate) (cloning : HostTransport project leftCopy rightCopy)
  (leftBytes : AssemblyItemDeinit.Release σ) (rightBytes : AssemblyItemDeinit.Release τ)
  (leftObjects : AssemblyItem.Release σ) (rightObjects : AssemblyItem.Release τ)
  (leftExternal : External σ) (rightExternal : External τ) (allocator : Nat)
  (source : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
  (leftArguments : Storage.State → AssemblyClone.Physical.Insertion.State Fields.Values σ → Storage.ArgumentSlice)
  (rightArguments : Storage.State → AssemblyClone.Physical.Insertion.State Fields.Values τ → Storage.ArgumentSlice)
  (leftRest : Storage.Operations (State σ) Insertion.Fault) (rightRest : Storage.Operations (State τ) Insertion.Fault)
  (rest : ∀ site owner, Effect.Transport (Insertion.State.mapEffects project)
    (leftRest.attempt site owner) (rightRest.attempt site owner))
include creation cloning rest

/-- Actual native source checks and final field assignment compose with the
same creation/clone callbacks. Every fault retains the exact reached locals. -/
theorem attempt_transport (site : Storage.Allocation) (owner : Storage.State) :
    Effect.Transport (Insertion.State.mapEffects project)
      ((operations leftCreate leftCopy leftBytes leftObjects leftExternal allocator source input leftArguments leftRest).attempt site owner)
      ((operations rightCreate rightCopy rightBytes rightObjects rightExternal allocator source input rightArguments rightRest).attempt site owner) := by
  intro before
  have base := Insertion.attempt_transport creation cloning leftBytes rightBytes leftObjects rightObjects leftExternal rightExternal
    allocator input leftArguments rightArguments leftRest rightRest rest site owner before
  unfold operations
  simp only [show (before.mapEffects project).object = before.object from rfl]
  cases site with
  | arguments | item | append | publish =>
    exact congrArg (fun result : Except Insertion.Fault Bool × State τ => (result.1.mapError Fault.base, result.2)) base
  | clone =>
    cases before.object with
    | none =>
      exact congrArg (fun result : Except Insertion.Fault Bool × State τ => (result.1.mapError Fault.base, result.2)) base
    | some object =>
      simp only [show (before.mapEffects project).clone.execution.memory.memory = before.clone.execution.memory.memory from rfl]
      cases AssemblyClone.NativeFields.checkSource before.clone.execution.memory.memory source input with
      | error fault => rfl
      | ok value =>
        cases value
        dsimp only
        exact (congrArg (fun result : Except Insertion.Fault Bool × State τ => finish object result.1 result.2) base).trans
          (finish_transport project object
            ((Insertion.operations leftCreate leftCopy leftBytes leftObjects leftExternal allocator input leftArguments leftRest).attempt .clone owner before).1
            ((Insertion.operations leftCreate leftCopy leftBytes leftObjects leftExternal allocator input leftArguments leftRest).attempt .clone owner before).2)

end NativeFields
end Compiler.Extraction.AssemblyItem.Creation
