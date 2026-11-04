/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeAllocationTrace
import Compiler.Extraction.InternerRecursiveProtocolEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace ConstructorItem.ProtocolTrace

variable {outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent)} {ops : Insertion.Operations σ}
    {outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent)} {allocate : Backing.Registry.Allocate σ}
    {outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))}
    {growth : Option (Growth.Registered.Callbacks σ)}
    (hosts : Insertion.Native.HostBindings outerOps ops outerAllocate allocate outerGrowth growth Prod.fst)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    {outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent))}
    {base : PairInput.Context (Publication.Effects σ)}
    (allocators : outerBase.allocator = base.allocator) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
include hosts allocators

theorem checkpoint_observations_traced (debug : AssemblyItem.Fields.Values)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue) :
    (graphObservations outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug source address input).Transport
    (graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input)
    (Publication.Effects.mapAllocator Prod.fst) := by
  have original := Caller.ProtocolTrace.Native.graphObservations_traced hosts safety owner meaning allocators usizeBits children observations debug source address input
  refine ⟨original.simplify, original.publish, ?_⟩
  intro key slice deterministic before
  change insertionEntry before :: _ = insertionEntry (ChildTrace.erase before) :: _
  rw [original.insert]
  rfl

theorem checkpoint_step_traced (budgets : outerBase.budget = base.budget) (queries : outerBase.queries = base.queries) :
    mapConstructors (m := Capture (Publication.Effects σ))
      (n := fun α => ChildTrace.TracedWorld σ ProtocolEvent → List ProtocolEvent → Except Fault α × Recorded (Publication.Effects σ))
      (fun action before leading => action (ChildTrace.erase before) leading)
      (step ops allocate safety owner meaning base growth usizeBits children observations) =
    mapConstructors (fun action before leading => mapReturn (Publication.Effects.mapAllocator Prod.fst) (action before leading))
      (step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
        (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations)) := by
  unfold step ProtocolTrace.stepWith
  rw [ProtocolTrace.map_atDebug, ProtocolTrace.map_atDebug]
  apply congrArg ProtocolTrace.atDebug
  funext debug
  exact ConstructorItem.ProtocolTrace.EffectTransport.constructors
    (context_erases (hosts.callerBase safety owner meaning budgets allocators queries) owner usizeBits
      (ChildTrace.constructors_erase children observations) debug)
    (checkpoint_observations_traced hosts safety owner meaning allocators usizeBits children observations debug)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
