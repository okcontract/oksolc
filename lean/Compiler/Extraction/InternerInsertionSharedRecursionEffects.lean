/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionSharedEffects
import Compiler.Extraction.InternerInsertionRecursionEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Consume the shared argument/publication derivation in all five native
entries at every finite observation depth. Only append and non-argument releases
remain as insertion-local obligations. Seed publication is still arbitrary and
needs its own equation; no seed insertion or simplification is assumed. -/
theorem unfold_shared_erases {project : σ → τ} {left : Insertion.Operations σ} {right : Insertion.Operations τ}
    (arguments : External.Transport left.arguments right.arguments project)
    (probes : OwnedKeys.Physical.Probe.Transport left.probe right.probe project)
    (creation : HostTransport project left.create right.create) (cloning : HostTransport project left.copy right.copy)
    (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
    (runtimeSafety : Bool) (allocator container : Nat) (meaning : Meaning)
    (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ))
    (remaining : ∀ source address input key normalized,
      Insertion.Native.ResidualObligations project left right leftAllocate rightAllocate runtimeSafety allocator container
        source address input key normalized leftGrowth rightGrowth)
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
  unfold_native_erases creation cloning leftAllocate rightAllocate runtimeSafety allocator container meaning leftGrowth rightGrowth
    (fun source address input key normalized => Insertion.Native.callback_obligations arguments leftAllocate rightAllocate
      runtimeSafety allocator container source address input key normalized leftGrowth rightGrowth probes
      (remaining source address input key normalized))
    external budgets allocators queries published owner usizeBits depth

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
