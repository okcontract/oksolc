/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReleaseEffects
import Compiler.Extraction.InternerInsertionSharedRecursionEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Every native insertion release now derives from the actual destructor/pop
bodies. Append/growth remains the only insertion-local transport obligation;
seed publication and the shared host boundaries remain explicit. -/
theorem unfold_release_erases {project : σ → τ} {left : Insertion.Operations σ} {right : Insertion.Operations τ}
    (arguments : External.Transport left.arguments right.arguments project)
    (probes : OwnedKeys.Physical.Probe.Transport left.probe right.probe project)
    (bytes : HostReleaseTransport project left.bytes right.bytes)
    (objects : HostReleaseTransport project left.objects right.objects)
    (creation : HostTransport project left.create right.create) (cloning : HostTransport project left.copy right.copy)
    (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
    (runtimeSafety : Bool) (allocator container : Nat) (meaning : Meaning)
    (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ))
    (appended : ∀ input key normalized,
      Insertion.Native.AppendTransport project leftAllocate rightAllocate runtimeSafety allocator container
        input key normalized leftGrowth rightGrowth)
    {leftBase : PairInput.Context (Publication.Effects σ)} {rightBase : PairInput.Context (Publication.Effects τ)}
    (external : leftBase.external.Transport rightBase.external (Publication.Effects.mapAllocator project))
    (budgets : leftBase.budget = rightBase.budget) (allocators : leftBase.allocator = rightBase.allocator)
    (queries : leftBase.queries = rightBase.queries)
    (published : ∀ source address input key owned id,
      Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator project))
        ((leftBase.primitives source address input).publish key owned id)
        ((rightBase.primitives source address input).publish key owned id))
    (owner usizeBits depth : Nat) :
    (Recursive.erasing (Publication.Effects.mapAllocator project)).Constructors
      (unfold { leftBase with primitives := fun source address input =>
        (Insertion.Native.callerPrimitives left leftAllocate runtimeSafety allocator container source address meaning input
          (leftBase.primitives source address input) leftGrowth) } owner usizeBits depth)
      (unfold { rightBase with primitives := fun source address input =>
        (Insertion.Native.callerPrimitives right rightAllocate runtimeSafety allocator container source address meaning input
          (rightBase.primitives source address input) rightGrowth) } owner usizeBits depth) :=
  unfold_shared_erases arguments probes creation cloning leftAllocate rightAllocate runtimeSafety allocator container meaning leftGrowth rightGrowth
    (fun source address input key normalized => Insertion.Native.residual_obligations bytes objects arguments leftAllocate rightAllocate
      runtimeSafety allocator container source address input key normalized leftGrowth rightGrowth
      (appended input key normalized))
    external budgets allocators queries published owner usizeBits depth

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
