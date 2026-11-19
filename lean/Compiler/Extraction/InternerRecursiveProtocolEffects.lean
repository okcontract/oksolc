/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolEffects
import Compiler.Extraction.InternerInsertionProtocolEffects
import Compiler.Extraction.InternerCallerProtocolHistory
import Compiler.Extraction.InternerRecursiveProtocolTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Caller.ProtocolTrace ConstructorItem.ProtocolTrace

variable {outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent)} {ops : Insertion.Operations σ}
    {outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent)} {allocate : Backing.Registry.Allocate σ}
    {outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))}
    {growth : Option (Growth.Registered.Callbacks σ)}
    (hosts : Insertion.Native.HostBindings outerOps ops outerAllocate allocate outerGrowth growth Prod.fst)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    {outerBase : ConstructorItem.PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent))}
    {base : ConstructorItem.PairInput.Context (Publication.Effects σ)}
    (allocators : outerBase.allocator = base.allocator) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
include hosts allocators

/-- The three source-selected observations agree under the child-history
projection. The simplifier uses the existing nested-history theorem; publication
and insertion use actual host calls and the same source guards and executor. -/
theorem Caller.ProtocolTrace.Native.graphObservations_traced (debug : AssemblyItem.Fields.Values)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue) :
    (Native.graphObservations outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug source address input).Transport
    (Native.graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input)
    (Publication.Effects.mapAllocator Prod.fst) := by
  constructor
  · intro key slice before
    exact (Native.dispatch_history owner usizeBits children observations debug key slice before).symm
  · intro key slice id before
    simp only [Native.graphObservations, ← allocators, Publication.admit_transport]
    cases Publication.admit outerBase.allocator source key slice before with
    | error reason => rfl
    | ok value =>
      dsimp only
      exact congrArg (fun ran => [Interner.InvocationTrace.Event.publicationProbe key ran.1])
        (hosts.probes key (Publication.forget before.memory))
  · intro key slice deterministic before
    simp only [Native.graphObservations, ← allocators,
      show (before.mapEffects (Publication.Effects.mapAllocator Prod.fst)).graph = before.graph from rfl,
      show (before.mapEffects (Publication.Effects.mapAllocator Prod.fst)).memory.memory = before.memory.memory from rfl]
    cases before.graph.representatives with
    | none => rfl
    | some cells =>
      dsimp only
      cases Insertion.Native.checkedCount before.memory.memory owner cells with
      | error fault => rfl
      | ok count =>
        dsimp only
        rw [hosts.recordExecution safety outerBase.allocator owner source address input key slice meaning deterministic cells before []]
        rfl

namespace ConstructorItem.NativeRecursion.ProtocolTrace

/-- One actual step keeps the same complete capture while removing the private
child-history layer. All constructor entries share the caller/wrapper proof;
local host equations derive native callbacks and computed graph observations. -/
theorem step_traced (budgets : outerBase.budget = base.budget) (queries : outerBase.queries = base.queries) :
    mapConstructors (m := Capture (Publication.Effects σ))
      (n := fun α => ChildTrace.TracedWorld σ ProtocolEvent → List ProtocolEvent → Except Fault α × Recorded (Publication.Effects σ))
      (fun action before leading => action (ChildTrace.erase before) leading)
      (step ops allocate safety owner meaning base growth usizeBits children observations) =
    mapConstructors (fun action before leading => mapReturn (Publication.Effects.mapAllocator Prod.fst) (action before leading))
      (step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
        (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations)) := by
  unfold step stepWith
  rw [map_atDebug, map_atDebug]
  apply congrArg atDebug
  funext debug
  exact ConstructorItem.ProtocolTrace.EffectTransport.constructors
    (context_erases (hosts.callerBase safety owner meaning budgets allocators queries) owner usizeBits
      (ChildTrace.constructors_erase children observations) debug)
    (Caller.ProtocolTrace.Native.graphObservations_traced hosts safety owner meaning allocators usizeBits children observations debug)

/-- Bind the history-carrying step used by the shared miss theorem to the
actual next finite native capture. Proper-child observations are computed by
the same finite family; no whole-caller or final-state correspondence is assumed. -/
theorem unfold_step_traced (budgets : outerBase.budget = base.budget) (queries : outerBase.queries = base.queries) (depth : Nat) :
    mapConstructors (m := Capture (Publication.Effects σ))
      (n := fun α => ChildTrace.TracedWorld σ ProtocolEvent → List ProtocolEvent → Except Fault α × Recorded (Publication.Effects σ))
      (fun action before leading => action (ChildTrace.erase before) leading)
      (unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)) =
    mapConstructors (fun action before leading => mapReturn (Publication.Effects.mapAllocator Prod.fst) (action before leading))
      (step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
        (ProtocolTrace.children ops allocate safety owner meaning base growth usizeBits depth)
        (ChildTrace.liftObservations (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))) :=
  step_traced hosts safety owner meaning allocators usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) budgets queries

end ConstructorItem.NativeRecursion.ProtocolTrace
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
