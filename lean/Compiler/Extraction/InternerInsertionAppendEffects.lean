/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeAppendEffects
import Compiler.Extraction.InternerInsertionReleaseEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

theorem allocation_transport {project : σ → τ}
    {left : Backing.Registry.Allocate σ} {right : Backing.Registry.Allocate τ}
    (allocated : Backing.Registry.Allocate.Transport project left right) :
    Backing.Registry.Allocate.Transport (Publication.Effects.mapAllocator project) (allocation left) (allocation right) := by
  intro allocator bytes alignment effects
  unfold allocation
  dsimp only [Publication.Effects.mapAllocator]
  rw [allocated]

theorem growthCallbacks_transport {project : σ → τ}
    {left : Growth.Registered.Callbacks σ} {right : Growth.Registered.Callbacks τ}
    (calls : Growth.Registered.Callbacks.Transport project left right) :
    Growth.Registered.Callbacks.Transport (Publication.Effects.mapAllocator project) (growthCallbacks left) (growthCallbacks right) := by
  refine ⟨calls.remap, ?_⟩
  intro allocator base bytes alignment effects
  dsimp only [growthCallbacks, Publication.Effects.mapAllocator]
  rw [calls.release]

/-- Derive the last insertion-local obligation from actual reached locals,
native append control and local allocator/free equations. No append outcome,
registry refinement or enclosing insertion transport is assumed. -/
theorem append_transport {project : σ → τ}
    {left : Backing.Registry.Allocate σ} {right : Backing.Registry.Allocate τ}
    {leftGrowth : Option (Growth.Registered.Callbacks σ)} {rightGrowth : Option (Growth.Registered.Callbacks τ)}
    (allocated : Backing.Registry.Allocate.Transport project left right)
    (growth : Growth.Registered.Callbacks.OptionalTransport project leftGrowth rightGrowth)
    (runtimeSafety : Bool) (allocator container : Nat) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) :
    AppendTransport project left right runtimeSafety allocator container input key normalized leftGrowth rightGrowth := by
  intro cells value owner before
  unfold append
  dsimp only
  have selected : arguments normalized owner (before.mapEffects project) = arguments normalized owner before := rfl
  have described : cell input key normalized value owner (before.mapEffects project) = cell input key normalized value owner before := rfl
  rw [selected]
  change (if before.item.object.isNone || before.item.clone.value.isNone || (arguments normalized owner before).isNone then _ else _) = _
  split
  · rfl
  · rw [described, memory_mapEffects]
    cases leftGrowth with
    | none => cases rightGrowth with
      | none =>
        dsimp only
        rw [Append.Registered.run_transport (allocation_transport allocated)]
        rfl
      | some calls => cases growth
    | some leftCalls => cases rightGrowth with
      | none => cases growth
      | some rightCalls =>
        dsimp only
        rw [Append.Registered.runWithGrowth_transport (allocation_transport allocated) (growthCallbacks_transport growth)]
        rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
