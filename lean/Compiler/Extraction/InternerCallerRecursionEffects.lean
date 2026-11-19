/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendRecursionEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

attribute [local irreducible] Insertion.Native.insert

/-- Bind the existing caller's allocator and source to actual publication and
native insertion. The recursive context supplies the actual simplifier. Seed
callbacks are retained only as composition inputs, never as native behavior. -/
def callerContext (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (container : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ)) :
    PairInput.Context (Publication.Effects σ) :=
  { base with
    external := Publication.external ops.arguments
    primitives := fun source address input =>
      Insertion.Native.callerPrimitives ops allocate runtimeSafety base.allocator container source address meaning input
        (Publication.callbacks ops.probe ops.arguments base.allocator source (base.primitives source address input)) growth }

theorem context_publishes (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (container : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (owner usizeBits : Nat) (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue) :
    ((context (callerContext ops allocate runtimeSafety container meaning base growth) owner usizeBits children debug).primitives
        source address input).publish = Publication.publish ops.probe ops.arguments base.allocator source := rfl

theorem context_inserts (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (container : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (owner usizeBits : Nat) (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue) :
    ((context (callerContext ops allocate runtimeSafety container meaning base growth) owner usizeBits children debug).primitives
        source address input).insert = fun key slice deterministic =>
      Insertion.Native.insert ops allocate runtimeSafety base.allocator container source address meaning input key slice deterministic growth := by
  dsimp only [context, callerContext, Insertion.Native.callerPrimitives, Publication.callbacks]

/-- Every seed callback and the seed host are replaced. Unrelated seed
implementations cannot change this complete native caller context. -/
theorem context_seed_independent (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (container : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (owner usizeBits : Nat) (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (external : External (Publication.Effects σ))
    (primitives : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects σ)) :
    context (callerContext ops allocate runtimeSafety container meaning { base with external, primitives } growth) owner usizeBits children debug =
      context (callerContext ops allocate runtimeSafety container meaning base growth) owner usizeBits children debug := rfl

/-- Every finite native constructor observation erases from local host-call
equations. Actual publication discharges the last seed callback premise; no
recursive, insertion, append, release or publication result is assumed. This
does not establish word preservation, host ownership or recursion termination. -/
theorem unfold_caller_erases {project : σ → τ} {left : Insertion.Operations σ} {right : Insertion.Operations τ}
    (arguments : External.Transport left.arguments right.arguments project)
    (probes : OwnedKeys.Physical.Probe.Transport left.probe right.probe project)
    (bytes : HostReleaseTransport project left.bytes right.bytes)
    (objects : HostReleaseTransport project left.objects right.objects)
    (creation : HostTransport project left.create right.create) (cloning : HostTransport project left.copy right.copy)
    {leftAllocate : Backing.Registry.Allocate σ} {rightAllocate : Backing.Registry.Allocate τ}
    (allocated : Backing.Registry.Allocate.Transport project leftAllocate rightAllocate)
    (runtimeSafety : Bool) (container : Nat) (meaning : Meaning)
    {leftGrowth : Option (Growth.Registered.Callbacks σ)} {rightGrowth : Option (Growth.Registered.Callbacks τ)}
    (growth : Growth.Registered.Callbacks.OptionalTransport project leftGrowth rightGrowth)
    {leftBase : PairInput.Context (Publication.Effects σ)} {rightBase : PairInput.Context (Publication.Effects τ)}
    (budgets : leftBase.budget = rightBase.budget) (allocators : leftBase.allocator = rightBase.allocator)
    (queries : leftBase.queries = rightBase.queries) (owner usizeBits depth : Nat) :
    (Recursive.erasing (Publication.Effects.mapAllocator project)).Constructors
      (unfold (callerContext left leftAllocate runtimeSafety container meaning leftBase leftGrowth) owner usizeBits depth)
      (unfold (callerContext right rightAllocate runtimeSafety container meaning rightBase rightGrowth) owner usizeBits depth) := by
  have published : ∀ source address input key owned id,
      Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator project))
        ((Publication.callbacks left.probe left.arguments leftBase.allocator source (leftBase.primitives source address input)).publish key owned id)
        ((Publication.callbacks right.probe right.arguments rightBase.allocator source (rightBase.primitives source address input)).publish key owned id) := by
    intro source address input key owned id
    simpa only [Publication.callbacks, allocators] using Publication.EffectTransport.publish arguments probes rightBase.allocator source key owned id
  simpa only [callerContext, allocators] using
    (unfold_append_erases arguments probes bytes objects creation cloning allocated runtimeSafety rightBase.allocator container meaning growth
      (leftBase := { leftBase with
        external := Publication.external left.arguments
        primitives := fun source address input =>
          Publication.callbacks left.probe left.arguments leftBase.allocator source (leftBase.primitives source address input) })
      (rightBase := { rightBase with
        external := Publication.external right.arguments
        primitives := fun source address input =>
          Publication.callbacks right.probe right.arguments rightBase.allocator source (rightBase.primitives source address input) })
      (Publication.external_transport arguments) budgets allocators queries published owner usizeBits depth)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
