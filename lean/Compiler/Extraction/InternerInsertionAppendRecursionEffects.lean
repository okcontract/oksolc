/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendEffects
import Compiler.Extraction.InternerInsertionReleaseRecursionEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Actual insertion now erases from its host equations: no local insertion,
append or release preservation result is a premise. The arbitrary seed
publication still requires binding, and erasure is not word preservation. -/
theorem unfold_append_erases {project : σ → τ} {left : Insertion.Operations σ} {right : Insertion.Operations τ}
    (arguments : External.Transport left.arguments right.arguments project)
    (probes : OwnedKeys.Physical.Probe.Transport left.probe right.probe project)
    (bytes : HostReleaseTransport project left.bytes right.bytes)
    (objects : HostReleaseTransport project left.objects right.objects)
    (creation : HostTransport project left.create right.create) (cloning : HostTransport project left.copy right.copy)
    {leftAllocate : Backing.Registry.Allocate σ} {rightAllocate : Backing.Registry.Allocate τ}
    (allocated : Backing.Registry.Allocate.Transport project leftAllocate rightAllocate)
    (runtimeSafety : Bool) (allocator container : Nat) (meaning : Meaning)
    {leftGrowth : Option (Growth.Registered.Callbacks σ)} {rightGrowth : Option (Growth.Registered.Callbacks τ)}
    (growth : Growth.Registered.Callbacks.OptionalTransport project leftGrowth rightGrowth)
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
  unfold_release_erases arguments probes bytes objects creation cloning leftAllocate rightAllocate runtimeSafety allocator container meaning
    leftGrowth rightGrowth (fun input key normalized => Insertion.Native.append_transport allocated growth runtimeSafety allocator container input key normalized)
    external budgets allocators queries published owner usizeBits depth

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
