/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNativeTrace
import Compiler.Extraction.InternerCallerRecursionEffects

namespace Compiler.Extraction.Storage.Trace

def Recorded.mapEffects (project : σ → τ) (before : Recorded σ ε) : Recorded τ ε :=
  ⟨project before.effects, before.events⟩

theorem record_map {left : Operations σ ε} {right : Operations τ ε} {project : σ → τ}
    (mapped : Operations.Transport left right project) :
    Operations.Transport (record left) (record right) (Recorded.mapEffects project) := by
  constructor
  · intro site owner before
    exact congrArg (fun ran : Except ε Bool × τ =>
      (ran.1, (⟨ran.2, before.events ++ [.attempt site owner ran.1]⟩ : Recorded τ ε)))
      (mapped.attempt site owner before.effects)
  · intro action owner before
    exact congrArg (fun ran : Except ε Unit × τ =>
      (ran.1, (⟨ran.2, before.events ++ [.release action owner ran.1]⟩ : Recorded τ ε)))
      (mapped.release action owner before.effects)

end Compiler.Extraction.Storage.Trace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The existing local host equations, grouped for the native caller and its
protocol observation. No compiler callback or whole-execution result is a field. -/
structure HostBindings (left : Operations σ) (right : Operations τ)
    (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
    (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ))
    (project : σ → τ) : Prop where
  arguments : left.arguments.Transport right.arguments project
  probes : OwnedKeys.Physical.Probe.Transport left.probe right.probe project
  bytes : HostReleaseTransport project left.bytes right.bytes
  objects : HostReleaseTransport project left.objects right.objects
  creation : HostTransport project left.create right.create
  cloning : HostTransport project left.copy right.copy
  allocated : Backing.Registry.Allocate.Transport project leftAllocate rightAllocate
  growth : Growth.Registered.Callbacks.OptionalTransport project leftGrowth rightGrowth

namespace HostBindings
variable {left : Operations σ} {right : Operations τ}
    {leftAllocate : Backing.Registry.Allocate σ} {rightAllocate : Backing.Registry.Allocate τ}
    {leftGrowth : Option (Growth.Registered.Callbacks σ)} {rightGrowth : Option (Growth.Registered.Callbacks τ)}
    {project : σ → τ} (hosts : HostBindings left right leftAllocate rightAllocate leftGrowth rightGrowth project)
    (safety : Bool) (allocator owner : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (slice : ArgumentSlice)
include hosts

theorem obligations :
    CallbackObligations project left right leftAllocate rightAllocate safety allocator owner source address input key slice leftGrowth rightGrowth :=
  callback_obligations hosts.arguments leftAllocate rightAllocate safety allocator owner source address input key slice
    leftGrowth rightGrowth hosts.probes
    (residual_obligations hosts.bytes hosts.objects hosts.arguments leftAllocate rightAllocate safety allocator owner source address input key slice
      leftGrowth rightGrowth (append_transport hosts.allocated hosts.growth safety allocator owner input key slice))

theorem observedCalls (meaning : Meaning) (cells : List Storage.Cell) (before : World (Publication.Effects σ)) :
    Storage.Operations.Transport
      (Native.observedCalls left leftAllocate safety allocator owner source address meaning input key slice cells before leftGrowth)
      (Native.observedCalls right rightAllocate safety allocator owner source address meaning input key slice cells
        (before.mapEffects (Publication.Effects.mapAllocator project)) rightGrowth)
      (State.mapEffects project) :=
  callbacks_transport hosts.creation hosts.cloning leftAllocate rightAllocate safety allocator owner source address input key slice
    cells ((key.eval meaning before.graph.read).getD 0) _ _ leftGrowth rightGrowth
    (obligations hosts safety allocator owner source address input key slice _ _ _ _ (fun _ _ => rfl))

/-- Reuse the same insertion callbacks and source executor on both sides.
Every event retains the actual allocation/release site, owner and result. -/
theorem recordExecution (meaning : Meaning) (deterministic : Bool) (cells : List Storage.Cell)
    (before : World (Publication.Effects σ)) (leading : List (Trace.Event Fault)) :
    Native.recordExecution right rightAllocate safety allocator owner source address meaning input key slice deterministic cells
        (before.mapEffects (Publication.Effects.mapAllocator project)) rightGrowth leading =
      ((Native.recordExecution left leftAllocate safety allocator owner source address meaning input key slice deterministic cells before leftGrowth leading).1,
       (Native.recordExecution left leftAllocate safety allocator owner source address meaning input key slice deterministic cells before leftGrowth leading).2.mapEffects
         (State.mapEffects project)) :=
  (Trace.record_map (observedCalls hosts safety allocator owner source address input key slice meaning cells before)).execute
    ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ insertProgram {} ⟨Native.observedStart before, leading⟩

theorem callerBase (meaning : Meaning)
    {leftBase : ConstructorItem.PairInput.Context (Publication.Effects σ)} {rightBase : ConstructorItem.PairInput.Context (Publication.Effects τ)}
    (budgets : leftBase.budget = rightBase.budget) (allocators : leftBase.allocator = rightBase.allocator)
    (queries : leftBase.queries = rightBase.queries) :
    ConstructorItem.NativeRecursion.BaseTransport
      (ConstructorItem.NativeRecursion.callerContext left leftAllocate safety owner meaning leftBase leftGrowth)
      (ConstructorItem.NativeRecursion.callerContext right rightAllocate safety owner meaning rightBase rightGrowth)
      (Publication.Effects.mapAllocator project) := by
  refine ⟨Publication.external_transport hosts.arguments, budgets, allocators, queries, ?_, ?_⟩
  · intro source address input key slice id
    simpa only [ConstructorItem.NativeRecursion.callerContext, callerPrimitives, Publication.callbacks, allocators] using
      Publication.EffectTransport.publish hosts.arguments hosts.probes rightBase.allocator source key slice id
  · intro source address input key slice deterministic
    simpa only [ConstructorItem.NativeRecursion.callerContext, callerPrimitives, allocators] using
      insert_transport hosts.creation hosts.cloning leftAllocate rightAllocate safety rightBase.allocator owner
        source address input key slice leftGrowth rightGrowth
        (obligations hosts safety rightBase.allocator owner source address input key slice) meaning deterministic

end HostBindings
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
