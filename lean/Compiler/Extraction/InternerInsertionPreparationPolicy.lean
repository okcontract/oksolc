/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparationOutcome
import Compiler.Extraction.ObservedInsertionFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache

/-- Local equations binding a logical preparation policy to actual reached
callbacks. Successful earlier stages use their returned sessions. These Boolean
observations do not admit semantic rejections: the failure theorem separately
requires `PreparationOOM`. Append/publication and a whole-invocation allocation
stream are not established by this relation. -/
structure PreparationPolicy (ops : Operations σ) (allocator : Nat)
    (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice)
    (before : Session (Publication.Effects σ)) (succeeds : Storage.Allocation → Bool) : Prop where
  duplicate : succeeds .arguments = (takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
    ⟨view normalized, normalized.items, none⟩ before).1.isOk
  create : ∀ operands remaining duplicated,
    takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before = (.ok (operands, remaining), duplicated) →
    succeeds .item = (AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated).1.isOk
  clone : ∀ operands remaining duplicated object allocated,
    takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before = (.ok (operands, remaining), duplicated) →
    AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated) →
    succeeds .clone = (AssemblyClone.Physical.run (observe ops.copy) allocator input allocated).1.isOk

/-- The matched policy retains the exact successful preparation prefix and
its first failing stage, rather than choosing an unrelated earlier OOM. -/
theorem PreparationPolicy.failure {ops : Operations σ} {allocator : Nat}
    {input : AssemblyClone.NativeFields.ItemValue} {normalized : ArgumentSlice}
    {before : Session (Publication.Effects σ)} {succeeds : Storage.Allocation → Bool}
    (policy : PreparationPolicy ops allocator input normalized before succeeds)
    (failed : PreparationOOM ops allocator input normalized before) :
    succeeds .arguments = false ∨
      succeeds .arguments = true ∧ (succeeds .item = false ∨ succeeds .item = true ∧ succeeds .clone = false) := by
  cases failed with
  | duplicate reached called =>
    exact Or.inl (by simpa only [called, Except.isOk, Except.toBool] using policy.duplicate)
  | create operands remaining duplicated reached taken called =>
    exact Or.inr ⟨by simpa only [taken, Except.isOk, Except.toBool] using policy.duplicate,
      Or.inl (by simpa only [called, Except.isOk, Except.toBool] using policy.create _ _ _ taken)⟩
  | clone operands remaining object duplicated allocated reached taken created called =>
    exact Or.inr ⟨by simpa only [taken, Except.isOk, Except.toBool] using policy.duplicate,
      Or.inr ⟨by simpa only [created, Except.isOk, Except.toBool] using policy.create _ _ _ taken,
        by simpa only [called, Except.isOk, Except.toBool] using policy.clone _ _ _ _ _ taken created⟩⟩

theorem PreparationPolicy.model_oom {ops : Operations σ} {allocator : Nat}
    {input : AssemblyClone.NativeFields.ItemValue} {normalized : ArgumentSlice}
    {before : Session (Publication.Effects σ)} {succeeds : Storage.Allocation → Bool}
    (policy : PreparationPolicy ops allocator input normalized before succeeds)
    (failed : PreparationOOM ops allocator input normalized before)
    (candidate : Storage.Cell) (key : Key) (heap : Interner.Heap) (rows : List Storage.Cell)
    (present : heap.representatives = some rows) (reads : heap.read = Storage.readValue rows)
    (room : rows.length < 2 ^ 32 - 1) :
    Interner.observedInsert candidate key true succeeds heap = (.error .outOfMemory, heap) := by
  apply Interner.observed_insert_preparation_oom candidate key succeeds heap rows present reads room
  rcases policy.failure failed with duplicate | ⟨_, created | ⟨_, cloned⟩⟩
  · exact Or.inl duplicate
  · exact Or.inr (Or.inl created)
  · exact Or.inr (Or.inr cloned)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
