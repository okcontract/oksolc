/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemCreationInsertion

namespace Compiler.Extraction.Memory.Arguments.Normalization.Insertion
open Compiler.Extraction.Storage

/-- Local preservation obligations for the complete insertion caller. A release
either rejects without changing storage or erases the same lifetime in both
registries. It need not be assumed to have been given an owned descriptor. -/
theorem erased_valid (before : Session σ) (id : Nat) (effects : σ) (initial : Valid before) :
    Valid (⟨write before.heap id none, Compiler.ZigAir.Memory.erase before.memory id, effects⟩ : Session σ) :=
  ⟨Compiler.ZigAir.Memory.erase_preserves_valid _ _ initial.memory,
    Arguments.related_erase _ _ _ initial.related, initial.injected.erased _⟩

theorem logical_release_shape (heap after : Memory.Heap) (allocator id : Nat)
    (released : Memory.release heap allocator id = .ok after) : after = write heap id none := by
  unfold Memory.release at released
  split at released
  · cases released
  · split at released
    · cases released; rfl
    · cases released

theorem typed_release_shape (before after : Compiler.ZigAir.Memory.State) (id : Nat) (type : Compiler.ZigAir.Memory.Ty)
    (released : Compiler.ZigAir.Memory.releaseOwned before id type = .ok after) :
    after = Compiler.ZigAir.Memory.erase before id := by
  unfold Compiler.ZigAir.Memory.releaseOwned at released
  split at released
  · cases released
  · split at released
    · split at released
      · cases released; rfl
      · cases released
    · cases released

theorem arguments_release_valid (external : External σ) (allocator : Nat) (slice : ArgumentSlice) (before : Session σ)
    (initial : Valid before) : Valid (free external allocator slice before).2 := by
  unfold free Arguments.release
  by_cases empty : slice.items.isEmpty = true
  · simp only [empty, ↓reduceIte]; exact initial
  · simp only [empty, Bool.false_eq_true, ↓reduceIte, Memory.releaseSlice, bind, Except.bind]
    cases logical : Memory.release before.heap allocator slice.address with
    | error fault => simp [Except.mapError]; exact initial
    | ok heap =>
      have shape := logical_release_shape before.heap heap allocator slice.address logical
      subst heap
      simp only [Except.mapError]
      cases typed : Compiler.ZigAir.Memory.releaseOwned before.memory slice.address (.array slice.items.length Compiler.ZigAir.Memory.WordArray.word) with
      | error fault => exact initial
      | ok memory =>
        have shape := typed_release_shape before.memory memory slice.address _ typed
        subst memory
        exact erased_valid before slice.address _ initial

theorem item_release_valid (external : AssemblyItem.Release σ) (allocator id : Nat) (before : Session σ)
    (initial : Valid before) : Valid (AssemblyItem.destroy external allocator id before).2 := by
  unfold AssemblyItem.destroy
  simp only [bind, Except.bind]
  cases logical : Memory.release before.heap allocator id with
  | error fault => exact initial
  | ok heap =>
    have shape := logical_release_shape before.heap heap allocator id logical
    subst heap
    simp only [Except.mapError]
    cases found : before.heap id with
    | none => exact initial
    | some allocation =>
      rcases allocation with ⟨owner, block⟩
      cases block with
      | arguments | representatives | bytes => exact initial
      | item value =>
        cases typed : Compiler.ZigAir.Memory.releaseOwned before.memory id AssemblyItem.viewType with
        | error fault => exact initial
        | ok memory =>
          have shape := typed_release_shape before.memory memory id _ typed
          subst memory
          exact erased_valid before id _ initial

theorem payload_release_valid (external : AssemblyItemDeinit.Release σ) (allocator : Nat) (slice : AssemblyItemDeinit.Bytes)
    (before : Session σ) (initial : Valid before) : Valid (AssemblyItemDeinit.free external allocator slice before).2 := by
  unfold AssemblyItemDeinit.free
  split
  · exact initial
  · split
    · exact initial
    · simp only [bind, Except.bind]
      cases logical : Memory.release before.heap allocator slice.address with
      | error fault => exact initial
      | ok heap =>
        have shape := logical_release_shape before.heap heap allocator slice.address logical
        subst heap
        simp only [Except.mapError]
        cases found : before.heap slice.address with
        | none => exact initial
        | some allocation =>
          rcases allocation with ⟨owner, block⟩
          cases block with
          | arguments | representatives | item => exact initial
          | bytes length =>
            dsimp only
            by_cases mismatch : length ≠ slice.length
            · rw [if_pos mismatch]
              exact initial
            · simp only [mismatch, ↓reduceIte]
              cases typed : Compiler.ZigAir.Memory.releaseOwned before.memory slice.address (.array slice.length AssemblyItemDeinit.byte) with
              | error fault => exact initial
              | ok memory =>
                have shape := typed_release_shape before.memory memory slice.address _ typed
                subst memory
                exact erased_valid before slice.address _ initial

theorem payload_run_valid (external : AssemblyItemDeinit.Release σ) (allocator : Nat) (payload : Option AssemblyItemDeinit.Bytes)
    (before : Session σ) (initial : Valid before) : Valid (AssemblyItemDeinit.run external allocator payload before).2.memory := by
  rw [AssemblyItemDeinit.run_equation]
  cases payload with
  | none => exact initial
  | some slice =>
    dsimp only
    cases called : AssemblyItemDeinit.free external allocator slice before with
    | mk result reached =>
      have kept := payload_release_valid external allocator slice before initial
      rw [called] at kept
      cases result <;> exact kept

theorem lifetime_stage_valid (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ)
    (external : External σ) (allocator : Nat) (payloads : Nat → Option AssemblyItemDeinit.Bytes)
    (descriptor : ExpressionDeinit.Descriptor) (stage : ExpressionDeinit.Stage) (before : ExpressionDeinit.State σ)
    (initial : Valid before.memory) :
    Valid (stage.execute (ExpressionDeinit.Lifetime.operations bytes objects allocator payloads) external allocator descriptor before).2.memory := by
  unfold ExpressionDeinit.Stage.execute
  split
  · exact initial
  · cases stage with
    | invalidate => exact initial
    | arguments => exact arguments_release_valid external allocator descriptor.arguments before.memory initial
    | itemValue =>
      simp only [ExpressionDeinit.itemStep, ExpressionDeinit.Lifetime.operations, ExpressionDeinit.Payload.operationsWith]
      exact payload_run_valid bytes allocator (payloads descriptor.item) before.memory initial
    | itemAllocation =>
      simp only [ExpressionDeinit.itemStep, ExpressionDeinit.Lifetime.operations, ExpressionDeinit.Payload.operationsWith]
      exact item_release_valid objects allocator descriptor.item before.memory initial

theorem lifetime_execute_valid (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ)
    (external : External σ) (allocator : Nat) (payloads : Nat → Option AssemblyItemDeinit.Bytes)
    (descriptor : ExpressionDeinit.Descriptor) (stages : List ExpressionDeinit.Stage) (before : ExpressionDeinit.State σ)
    (initial : Valid before.memory) :
    Valid (ExpressionDeinit.execute (ExpressionDeinit.Lifetime.operations bytes objects allocator payloads)
      external allocator descriptor stages before).2.memory := by
  induction stages generalizing before with
  | nil => exact initial
  | cons stage rest ih =>
    cases called : stage.execute (ExpressionDeinit.Lifetime.operations bytes objects allocator payloads) external allocator descriptor before with
    | mk result reached =>
      have step := lifetime_stage_valid bytes objects external allocator payloads descriptor stage before initial
      rw [called] at step
      cases result with
      | error fault => simpa only [ExpressionDeinit.execute, ExpressionDeinit.executeStages, called] using step
      | ok returned =>
        cases returned
        simpa only [ExpressionDeinit.execute, ExpressionDeinit.executeStages, called] using ih reached step

theorem lifetime_run_valid (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ)
    (external : External σ) (allocator : Nat) (payloads : Nat → Option AssemblyItemDeinit.Bytes)
    (descriptor : ExpressionDeinit.Descriptor) (before : Session σ) (initial : Valid before) :
    Valid (ExpressionDeinit.Lifetime.run bytes objects external allocator payloads descriptor before).2.memory :=
  lifetime_execute_valid bytes objects external allocator payloads descriptor _ ⟨before, false⟩ initial

end Compiler.Extraction.Memory.Arguments.Normalization.Insertion
