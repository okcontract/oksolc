/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionMemoryValidity
import Compiler.Extraction.StorageExecutionInvariant

namespace Compiler.Extraction.Memory.Arguments.Normalization.Insertion
open Compiler.Extraction.Storage
open AssemblyClone (Value)

def CloneValid (state : AssemblyClone.Physical.Insertion.State Metadata σ) : Prop := Valid state.execution.memory
def CreationValid (state : AssemblyItem.Creation.Insertion.State Metadata σ) : Prop := CloneValid state.clone

theorem clone_preserves (copy : AssemblyClone.Physical.Allocate σ) (bytes : AssemblyItemDeinit.Release σ)
    (objects : AssemblyItem.Release σ) (external : External σ) (allocator : Nat) (input : Value Metadata)
    (target : Storage.State → AssemblyClone.Physical.Insertion.State Metadata σ → ExpressionDeinit.Descriptor)
    (rest : Storage.Operations (AssemblyClone.Physical.Insertion.State Metadata σ) AssemblyClone.Physical.Insertion.Fault)
    (kept : Storage.Preserves rest CloneValid) :
    Storage.Preserves (AssemblyClone.Physical.Insertion.operations copy bytes objects external allocator input target rest) CloneValid := by
  constructor
  · intro site owner before result after initial called
    cases site with
    | arguments | item | append | publish => exact kept.attempt _ owner before result after initial called
    | clone =>
      cases ran : AssemblyClone.Physical.run copy allocator input before.execution.memory with
      | mk response reached =>
        cases response with
        | ok copied =>
          have post := AssemblyClone.Physical.run_valid copy allocator input copied before.execution.memory reached initial ran
          simp only [AssemblyClone.Physical.Insertion.operations, ran, Prod.mk.injEq, Except.ok.injEq] at called
          exact called.2 ▸ post.valid
        | error fault =>
          cases fault with
          | memory | registryCollision | sourceMismatch | copyMismatch =>
            simp [AssemblyClone.Physical.Insertion.operations, ran] at called
          | outOfMemory =>
            obtain ⟨heap, memory⟩ := AssemblyClone.Physical.run_oom copy allocator input before.execution.memory reached ran
            have valid : Valid reached := ⟨by simpa only [memory] using initial.memory,
              by simpa only [heap, memory] using initial.related, by simpa only [heap, memory] using initial.injected⟩
            simp only [AssemblyClone.Physical.Insertion.operations, ran, Prod.mk.injEq, Except.ok.injEq] at called
            exact called.2 ▸ valid
  · intro action owner before after initial called
    cases action with
    | normalized | arguments | allocation | pop => exact kept.release _ owner before after initial called
    | value =>
      dsimp only [AssemblyClone.Physical.Insertion.operations] at called
      split at called
      · simp at called
      · cases present : before.value with
        | none => simp [present] at called
        | some copied =>
          simp only [present] at called
          have post := payload_run_valid bytes allocator (AssemblyClone.Physical.payload copied) before.execution.memory initial
          have same := congrArg Prod.snd called
          dsimp only at same
          rw [← same]
          exact post
    | lastValue =>
      dsimp only [AssemblyClone.Physical.Insertion.operations] at called
      split at called
      · simp at called
      · cases present : before.value with
        | none => simp [present] at called
        | some copied =>
          simp only [present] at called
          have post := lifetime_run_valid bytes objects external allocator (fun _ => AssemblyClone.Physical.payload copied)
            (target owner before) before.execution.memory initial
          have same := congrArg Prod.snd called
          dsimp only at same
          rw [← same]
          exact post

theorem clone_callbacks_preserves (copy : AssemblyClone.Physical.Allocate σ) (bytes : AssemblyItemDeinit.Release σ)
    (objects : AssemblyItem.Release σ) (external : External σ) (allocator object : Nat) (input : Value Metadata)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Metadata σ → ArgumentSlice) :
    Storage.Preserves (AssemblyItem.Creation.Insertion.cloneOperations copy bytes objects external allocator object input arguments) CloneValid := by
  apply clone_preserves
  constructor
  · intro _ _ _ _ _ _ impossible; cases impossible
  · intro _ _ _ _ _ impossible; cases impossible

theorem creation_preserves (allocate : AssemblyItem.Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (input : Value Metadata)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Metadata σ → ArgumentSlice)
    (rest : Storage.Operations (AssemblyItem.Creation.Insertion.State Metadata σ) AssemblyItem.Creation.Insertion.Fault)
    (kept : Storage.Preserves rest CreationValid) :
    Storage.Preserves (AssemblyItem.Creation.Insertion.operations allocate copy bytes objects external allocator input arguments rest) CreationValid := by
  constructor
  · intro site owner before result after initial called
    cases site with
    | arguments | append | publish => exact kept.attempt _ owner before result after initial called
    | item =>
      dsimp only [AssemblyItem.Creation.Insertion.operations] at called
      split at called
      · simp at called
      · cases ran : AssemblyItem.Creation.create allocate allocator input.item before.clone.execution.memory with
        | mk response reached =>
          cases response with
          | ok object =>
            have post := AssemblyItem.Creation.create_verified allocate allocator object input.item before.clone.execution.memory reached initial ran
            simp only [ran, Prod.mk.injEq, Except.ok.injEq] at called
            exact called.2 ▸ post.valid
          | error fault =>
            cases fault with
            | memory | registryCollision => simp [ran] at called
            | outOfMemory =>
              obtain ⟨effects, _, same⟩ := AssemblyItem.Creation.create_oom allocate allocator input.item before.clone.execution.memory reached ran
              have valid : Valid reached := by rw [same]; exact ⟨initial.memory, initial.related, initial.injected⟩
              simp only [ran, Prod.mk.injEq, Except.ok.injEq] at called
              exact called.2 ▸ valid
    | clone =>
      dsimp only [AssemblyItem.Creation.Insertion.operations] at called
      cases present : before.object with
      | none => simp [present] at called
      | some object =>
        simp only [present] at called
        cases ran : (AssemblyItem.Creation.Insertion.cloneOperations copy bytes objects external allocator object input arguments).attempt .clone owner before.clone with
        | mk response reached =>
          cases response with
          | error fault => simp [ran, Except.mapError] at called
          | ok accepted =>
            have post := (clone_callbacks_preserves copy bytes objects external allocator object input arguments).attempt
              .clone owner before.clone accepted reached initial ran
            simp only [ran, Except.mapError, Prod.mk.injEq, Except.ok.injEq] at called
            exact called.2 ▸ post
  · intro action owner before after initial called
    cases action with
    | normalized | arguments | pop => exact kept.release _ owner before after initial called
    | allocation =>
      dsimp only [AssemblyItem.Creation.Insertion.operations] at called
      cases present : before.object with
      | none => simp [present] at called
      | some object =>
        simp only [present] at called
        have post := item_release_valid objects allocator object before.clone.execution.memory initial
        have same := congrArg Prod.snd called
        dsimp only at same
        rw [← same]
        exact post
    | value =>
      dsimp only [AssemblyItem.Creation.Insertion.operations] at called
      cases present : before.object with
      | none => simp [present] at called
      | some object =>
        simp only [present] at called
        cases ran : (AssemblyItem.Creation.Insertion.cloneOperations copy bytes objects external allocator object input arguments).release .value owner before.clone with
        | mk response reached =>
          cases response with
          | error fault => simp [ran, Except.mapError] at called
          | ok returned =>
            cases returned
            have post := (clone_callbacks_preserves copy bytes objects external allocator object input arguments).release
              .value owner before.clone reached initial ran
            simp only [ran, Except.mapError, Prod.mk.injEq] at called
            exact called.2 ▸ post

    | lastValue =>
      dsimp only [AssemblyItem.Creation.Insertion.operations] at called
      cases present : before.object with
      | none => simp [present] at called
      | some object =>
        simp only [present] at called
        cases ran : (AssemblyItem.Creation.Insertion.cloneOperations copy bytes objects external allocator object input arguments).release .lastValue owner before.clone with
        | mk response reached =>
          cases response with
          | error fault => simp [ran, Except.mapError] at called
          | ok returned =>
            cases returned
            have post := (clone_callbacks_preserves copy bytes objects external allocator object input arguments).release
              .lastValue owner before.clone reached initial ran
            simp only [ran, Except.mapError, Prod.mk.injEq] at called
            exact called.2 ▸ post

end Compiler.Extraction.Memory.Arguments.Normalization.Insertion
