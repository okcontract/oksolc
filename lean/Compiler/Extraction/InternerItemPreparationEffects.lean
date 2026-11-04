/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyPreparationCallbacks
import Compiler.Extraction.InternerInsertionNative
import Compiler.Extraction.InternerPublicationEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

def State.mapEffects (project : σ → τ) (before : State Metadata σ) : State Metadata τ :=
  ⟨before.item.mapEffects (Publication.Effects.mapAllocator project), before.duplicate⟩

theorem memory_mapEffects (project : σ → τ) (before : State Metadata σ) :
    memory (before.mapEffects project) = (memory before).mapEffects (Publication.Effects.mapAllocator project) := rfl

theorem observe_transport (project : σ → τ)
    {left : α → Session σ → β × σ} {right : α → Session τ → β × τ}
    (mapped : HostTransport project left right) :
    HostTransport (Publication.Effects.mapAllocator project) (observe left) (observe right) := by
  intro argument before
  unfold observe
  rw [Publication.forget_mapEffects, mapped]
  rfl

namespace Native
variable {project : σ → τ} {left : Operations σ} {right : Operations τ}
  (creation : HostTransport project left.create right.create) (cloning : HostTransport project left.copy right.copy)
include creation cloning

/-- This is the actual native item-operation adapter, including source-field
admission and final assignment. Only its two host request equations are assumed;
no creation/clone success, ownership or enclosing-insertion result is supplied. -/
theorem items_attempt_transport (allocator : Nat) (source : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice) (owner : Storage.State)
    (before : Frame σ) (site : Storage.Allocation) :
    (items right allocator source input normalized owner (before.mapEffects project)).attempt site owner
        (before.mapEffects project).item =
      (((items left allocator source input normalized owner before).attempt site owner before.item).1,
       ((items left allocator source input normalized owner before).attempt site owner before.item).2.mapEffects
         (Publication.Effects.mapAllocator project)) :=
  AssemblyItem.Creation.NativeFields.attempt_transport (observe_transport project creation) (observe_transport project cloning)
    (release left.bytes) (release right.bytes) (release left.objects) (release right.objects)
    (Publication.external left.arguments) (Publication.external right.arguments) allocator source input _ _ _ _
    (fun _ _ _ => rfl) site owner before.item

/-- Consume preparation transport at the insertion executor's real item/clone
sites. Growth, argument duplication, publication and releases remain separate
local obligations; arbitrary functions for those unused branches are allowed. -/
theorem preparation_callback_transport
    (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
    (runtimeSafety : Bool) (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (cells : List Storage.Cell) (value : Contract.Yul.Word)
    (leftGraph : Storage.State → Frame σ → Interner.Heap) (rightGraph : Storage.State → Frame τ → Interner.Heap)
    (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ))
    (site : Storage.Allocation) (preparation : site = .item ∨ site = .clone) (owner : Storage.State) :
    Effect.Transport (State.mapEffects project)
      ((callbacks left leftAllocate runtimeSafety allocator container source itemSource input key normalized cells value leftGraph leftGrowth).attempt site owner)
      ((callbacks right rightAllocate runtimeSafety allocator container source itemSource input key normalized cells value rightGraph rightGrowth).attempt site owner) := by
  intro before
  have called := items_attempt_transport creation cloning allocator itemSource input normalized owner before site
  rcases preparation with rfl | rfl
  all_goals
    exact congrArg (fun result : Except AssemblyItem.Creation.NativeFields.Fault Bool ×
        AssemblyItem.Creation.NativeFields.State (Publication.Effects τ) =>
      (result.1.mapError Fault.item, ({ item := result.2, duplicate := before.duplicate } : Frame τ))) called

end Native
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
