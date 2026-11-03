/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- The existing publication adapter preserves the key ownership table on
all normalization allocation outcomes, including rejected descriptors and
partial copy/sort failures. Allocator-private effects remain exact. -/
theorem region_keys (external : External σ) (site : NormalizationOwnership.Allocation)
    (before : Session (Effects σ)) (type : Compiler.ZigAir.Memory.Ty) :
    (Compiler.ZigAir.Memory.RegionAllocation.reserve before.memory type
      (fun bytes _ => (Publication.external external).allocate site before bytes) before.effects).2.keys = before.effects.keys := by
  unfold Compiler.ZigAir.Memory.RegionAllocation.reserve
  cases type.layout with
  | none => rfl
  | some layout =>
    dsimp only
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · simp only [Publication.external]
          cases called : external.allocate site (Publication.forget before) layout.bytes before.effects.allocator with
          | mk response effects =>
            simp only [called]
            cases response with
            | none => rfl
            | some base => dsimp only; split <;> rfl

theorem word_keys (external : External σ) (site : NormalizationOwnership.Allocation)
    (before : Session (Effects σ)) (length : Nat) :
    (Compiler.ZigAir.Memory.WordAllocation.reserve before.memory length
      ((Publication.external external).allocate site before) before.effects).2.keys = before.effects.keys := by
  unfold Compiler.ZigAir.Memory.WordAllocation.reserve
  split
  · rfl
  · split
    · rfl
    · have same := region_keys external site before (.array length word)
      cases ran : Compiler.ZigAir.Memory.RegionAllocation.reserve before.memory (.array length word)
          (fun bytes _ => (Publication.external external).allocate site before bytes) before.effects with
      | mk outcome effects =>
        rcases outcome with ⟨result, memory⟩
        simpa only [ran] using same

theorem allocation_keys (external : External σ) (site : NormalizationOwnership.Allocation)
    (allocator : Nat) (values : List NodeId) (before : Session (Effects σ)) :
    (Allocation.reserve before.heap before.memory allocator values
      ((Publication.external external).allocate site before) before.effects).2.keys = before.effects.keys :=
  (congrArg Effects.keys (Allocation.reserve_reached before.heap before.memory allocator values
    ((Publication.external external).allocate site before) before.effects).2).trans
      (word_keys external site before values.length)

theorem duplication_keys (external : External σ) (allocator : Nat) (source : View)
    (values : List NodeId) (before : Session (Effects σ)) :
    (Duplication.run before.heap before.memory allocator source values
      ((Publication.external external).allocate .duplicate before) before.effects).2.keys = before.effects.keys := by
  by_cases length : source.length = values.length
  · exact (congrArg Effects.keys (Duplication.run_reached_effects before.heap before.memory allocator source values
      ((Publication.external external).allocate .duplicate before) before.effects length)).trans
        (allocation_keys external .duplicate allocator values before)
  · rw [Duplication.run_length_rejected _ _ _ _ _ _ _ length]

theorem take_keys (external : External σ) (allocator : Nat) (handle : Handle) (before : Session (Effects σ)) :
    (takeOwned normalizationOwnershipCode (Publication.external external) allocator handle before).2.effects.keys = before.effects.keys := by
  unfold takeOwned
  cases handle.owned with
  | some owned => rfl
  | none =>
    have same := duplication_keys external allocator handle.items handle.values before
    cases ran : Duplication.run before.heap before.memory allocator handle.items handle.values
        ((Publication.external external).allocate .duplicate before) before.effects with
    | mk outcome effects =>
      rcases outcome with ⟨result, heap, memory⟩
      rw [ran] at same
      cases result with
      | error reason => exact same
      | ok slice => cases slice <;> exact same

theorem reserve_keys (external : External σ) (allocator : Nat) (values : List NodeId) (before : Session (Effects σ)) :
    (reserve (Publication.external external) allocator values before).2.effects.keys = before.effects.keys := by
  have same := allocation_keys external .temporary allocator values before
  unfold reserve
  cases ran : Allocation.reserve before.heap before.memory allocator values
      ((Publication.external external).allocate .temporary before) before.effects with
  | mk outcome effects =>
    rcases outcome with ⟨result, heap, memory⟩
    rw [ran] at same
    cases result with
    | error reason => exact same
    | ok slice => cases slice <;> exact same

theorem prepare_keys (budget allocator bufferLength : Nat) (source target : View) (values : List NodeId)
    (allocated : Bool) (before : Session (Effects σ)) :
    (prepare normalizationOwnershipCode budget allocator bufferLength source target values allocated before).2.effects.keys = before.effects.keys := by
  unfold prepare
  cases InsertionSort.Copied.run budget before.memory source target with
  | mk result memory =>
    cases result with
    | error fault => rfl
    | ok value => cases value; cases allocated <;> rfl

theorem init_keys (external : External σ) (budget allocator : Nat) (commutative : Bool)
    (source buffer : View) (values : List NodeId) (before : Session (Effects σ)) :
    (init normalizationOwnershipCode (Publication.external external) budget allocator commutative source buffer values before).2.effects.keys = before.effects.keys := by
  unfold init
  split
  · rfl
  · split
    · exact prepare_keys _ _ _ _ _ _ _ _
    · have same := reserve_keys external allocator values before
      cases ran : reserve (Publication.external external) allocator values before with
      | mk result memory =>
        rw [ran] at same
        cases result with
        | error fault => exact same
        | ok slice => exact (prepare_keys _ _ _ _ _ _ _ _).trans same

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
