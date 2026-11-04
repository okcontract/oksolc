/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyReleaseEffects
import Compiler.Extraction.RepresentativePopEffects
import Compiler.Extraction.InternerInsertionSharedEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

theorem release_transport (project : σ → τ) {left : α → Session σ → σ} {right : α → Session τ → τ}
    (mapped : HostReleaseTransport project left right) :
    HostReleaseTransport (Publication.Effects.mapAllocator project) (release left) (release right) := by
  intro argument before
  unfold release
  rw [Publication.forget_mapEffects, mapped]
  rfl

/-- Allocation cleanup uses the reached object local and the existing typed
destroy operation. Clear the local only when that operation succeeds. -/
theorem allocation_transport {project : σ → τ} {left : Operations σ} {right : Operations τ}
    (objects : HostReleaseTransport project left.objects right.objects)
    (allocator count : Nat) (source : View) (input : AssemblyClone.Value Metadata) (key : Key) (normalized : ArgumentSlice)
    (leftGraph : Storage.State → State Metadata σ → Interner.Heap) (rightGraph : Storage.State → State Metadata τ → Interner.Heap)
    (owner : Storage.State) :
    Effect.Transport (State.mapEffects project)
      ((callbacks left allocator count source input key normalized leftGraph).release .allocation owner)
      ((callbacks right allocator count source input key normalized rightGraph).release .allocation owner) := by
  intro before
  dsimp only [callbacks, itemOperations, AssemblyItem.Creation.Insertion.operations]
  dsimp only [State.mapEffects, AssemblyItem.Creation.Insertion.State.mapEffects,
    AssemblyClone.Physical.Insertion.State.mapEffects, ExpressionDeinit.State.mapEffects]
  cases found : before.item.object with
  | none => dsimp only; rw [found]
  | some object =>
    dsimp only
    have called := AssemblyItem.destroy_transport (Publication.Effects.mapAllocator project)
      (release_transport project objects) allocator object before.item.clone.execution.memory
    simp only [called]

namespace Native
variable {project : σ → τ} {left : Operations σ} {right : Operations τ}

theorem releaseValue_transport (bytes : HostReleaseTransport project left.bytes right.bytes) (allocator : Nat) :
    Effect.Transport (State.mapEffects project) (releaseValue left allocator) (releaseValue right allocator) := by
  intro before
  unfold releaseValue
  change (match before.item.object with | none => _ | some object => _) = _
  cases before.item.object with
  | none => rfl
  | some object =>
    dsimp only
    rw [memory_mapEffects, AssemblyItemDeinit.Native.run_transport (release_transport project bytes) allocator ⟨object, 0⟩ (memory before)]
    cases AssemblyItemDeinit.Native.run (release left.bytes) allocator ⟨object, 0⟩ (memory before) with
    | mk result reached => cases result with
      | error reason => rfl
      | ok value => cases value; rfl

theorem releaseLast_transport (bytes : HostReleaseTransport project left.bytes right.bytes)
    (objects : HostReleaseTransport project left.objects right.objects)
    (external : External.Transport left.arguments right.arguments project) (allocator container : Nat) :
    Effect.Transport (State.mapEffects project) (releaseLast left allocator container) (releaseLast right allocator container) := by
  intro before
  unfold releaseLast
  change (match Last.select (memory before).memory (Owner.headerAddress ⟨container, 0⟩) with | .error reason => _ | .ok descriptor => _) = _
  cases Last.select (memory before).memory (Owner.headerAddress ⟨container, 0⟩) with
  | error reason => rfl
  | ok descriptor =>
    dsimp only
    rw [memory_mapEffects, ExpressionDeinit.Native.run_transport (release_transport project bytes) (release_transport project objects)
      (Publication.external_transport external) allocator descriptor (memory before)]
    cases ExpressionDeinit.Native.run (release left.bytes) (release left.objects) (Publication.external left.arguments)
        allocator descriptor (memory before) with
    | mk result reached => cases result with
      | error reason => rfl
      | ok value => cases value; rfl

theorem pop_transport (project : σ → τ) (allocator container : Nat) :
    Effect.Transport (State.mapEffects project) (pop allocator container) (pop allocator container) := by
  intro before
  unfold pop
  rw [memory_mapEffects, Pop.Registered.run_transport (Publication.Effects.mapAllocator project) allocator container]
  rfl

variable (bytes : HostReleaseTransport project left.bytes right.bytes) (objects : HostReleaseTransport project left.objects right.objects)
  (external : External.Transport left.arguments right.arguments project)
  (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
  (runtimeSafety : Bool) (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
  (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
  (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ))
include bytes objects external

theorem release_callbacks_transport (cells : List Storage.Cell) (value : Contract.Yul.Word)
    (leftGraph : Storage.State → Frame σ → Interner.Heap) (rightGraph : Storage.State → Frame τ → Interner.Heap)
    (action : Storage.Release) (owner : Storage.State) :
    Effect.Transport (State.mapEffects project)
      ((callbacks left leftAllocate runtimeSafety allocator container source itemSource input key normalized cells value leftGraph leftGrowth).release action owner)
      ((callbacks right rightAllocate runtimeSafety allocator container source itemSource input key normalized cells value rightGraph rightGrowth).release action owner) := by
  cases action with
  | normalized =>
    exact shared_release_transport external leftAllocate rightAllocate runtimeSafety allocator container source itemSource input
      key normalized cells value leftGraph rightGraph leftGrowth rightGrowth .normalized (Or.inl rfl) owner
  | arguments =>
    exact shared_release_transport external leftAllocate rightAllocate runtimeSafety allocator container source itemSource input
      key normalized cells value leftGraph rightGraph leftGrowth rightGrowth .arguments (Or.inr rfl) owner
  | value => exact releaseValue_transport bytes allocator
  | lastValue => exact releaseLast_transport bytes objects external allocator container
  | pop => exact pop_transport project allocator container
  | allocation =>
    intro before
    exact congrArg (fun output : Except Rejection Unit × Frame τ => (output.1.mapError Fault.base, output.2))
      (allocation_transport objects allocator cells.length source input key normalized leftGraph rightGraph owner before)

/-- Append has no dependency on the publication graph or item source address.
Retain just its actual native allocator/growth/input parameters. -/
def AppendTransport (project : σ → τ) (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
    (runtimeSafety : Bool) (allocator container : Nat) (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ)) : Prop :=
  ∀ cells value owner, Effect.Transport (State.mapEffects project)
    (fun before => append runtimeSafety leftAllocate allocator container cells input key normalized value owner before leftGrowth)
    (fun before => append runtimeSafety rightAllocate allocator container cells input key normalized value owner before rightGrowth)

theorem residual_obligations (appended : AppendTransport project leftAllocate rightAllocate runtimeSafety allocator container
    input key normalized leftGrowth rightGrowth) :
    ResidualObligations project left right leftAllocate rightAllocate runtimeSafety allocator container
      source itemSource input key normalized leftGrowth rightGrowth := by
  intro cells value leftGraph rightGraph _
  refine ⟨appended cells value, ?_⟩
  intro action _ _ owner
  exact release_callbacks_transport bytes objects external leftAllocate rightAllocate runtimeSafety allocator container source itemSource
    input key normalized leftGrowth rightGrowth cells value leftGraph rightGraph action owner

end Native
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
