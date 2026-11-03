/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNative
import Compiler.Extraction.InternerInsertionValidity
import Compiler.Extraction.PublicationNormalizationEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Preparation only changes allocator-private effects. The physical key table
is carried by the existing adapters, including every rejected/partial outcome. -/
theorem create_keys (allocate : AssemblyItem.Creation.Allocate σ) (allocator : Nat) (item : Item)
    (before : Session (Publication.Effects σ)) :
    (AssemblyItem.Creation.create (observe allocate) allocator item before).2.effects.keys = before.effects.keys := by
  unfold AssemblyItem.Creation.create
  split
  · rfl
  · unfold observe
    cases allocate AssemblyItem.Creation.layout (Publication.forget before) with
    | mk response effects =>
      cases response with
      | none => rfl
      | some base =>
        dsimp only
        split
        · rfl
        · cases before.heap before.memory.nextId <;> rfl

theorem clone_duplicate_keys (copy : AssemblyClone.Physical.Allocate σ) (allocator : Nat) (source : AssemblyClone.Bytes)
    (before : Session (Publication.Effects σ)) :
    (AssemblyClone.Physical.duplicate (observe copy) allocator source before).2.effects.keys = before.effects.keys := by
  unfold AssemblyClone.Physical.duplicate
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · unfold observe
        cases copy source.contents.length (Publication.forget before) with
        | mk response effects =>
          cases response with
          | none => rfl
          | some base =>
            dsimp only
            unfold AssemblyClone.Physical.copyAt
            dsimp only
            repeat' first | rfl | (split <;> try dsimp only)

theorem clone_keys (copy : AssemblyClone.Physical.Allocate σ) (allocator : Nat)
    (input : AssemblyClone.NativeFields.ItemValue) (before : Session (Publication.Effects σ)) :
    (AssemblyClone.Physical.run (observe copy) allocator input before).2.effects.keys = before.effects.keys := by
  unfold AssemblyClone.Physical.run AssemblyClone.CloneCode.run
  simp only [AssemblyClone.cloneCode]
  cases present : input.verbatim with
  | none => rfl
  | some source =>
    simp only [↓reduceIte, Scalar.run]
    have same := clone_duplicate_keys copy allocator source.data before
    cases ran : AssemblyClone.Physical.duplicate (observe copy) allocator source.data before with
    | mk result reached =>
      rw [ran] at same
      cases result <;> exact same

theorem arguments_keys (external : External σ) (allocator : Nat) (slice : ArgumentSlice)
    (before : Session (Publication.Effects σ)) :
    (takeOwned normalizationOwnershipCode (Publication.external external) allocator
      ⟨view slice, slice.items, none⟩ before).2.effects.keys = before.effects.keys :=
  Publication.take_keys external allocator _ before

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
