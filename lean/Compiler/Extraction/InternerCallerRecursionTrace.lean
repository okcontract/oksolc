/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerRecursionEffects
import Compiler.Extraction.RepresentativeBackingTrace
import Compiler.Extraction.AssemblyReleaseTrace
import Compiler.Extraction.InternerPublicationHostTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Recording
open Normalization.HostTrace

/-- Instrument each host port used by native insertion. Native append uses
the separate backing allocator, not the legacy append port; that unused port
is forwarded transparently and emits no invented native event. The publication
probe is still a host boundary, not a certificate of its internal map buckets. -/
def operations (ops : Operations σ) : Operations (Recorded σ) where
  arguments := record ops.arguments
  create := recordCreate ops.create
  copy := recordCopy ops.copy
  bytes := recordBytes ops.bytes
  objects := recordObject ops.objects
  append := fun count before =>
    let (result, reached) := ops.append count (before.mapEffects Recorded.effects)
    (result, { before.effects with effects := reached })
  probe := Publication.Recording.recordProbe ops.probe

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Recording

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache
open RepresentativeArray Normalization.HostTrace

/-- All five native entries erase at every finite depth with actual host
recorders. No host or seed callback transport theorem is supplied by the caller.
The initial state may contain arbitrary history. This erasure statement does
not connect events to a scoped resource protocol or establish trace coverage. -/
theorem unfold_recorded_erases (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (runtimeSafety : Bool) (container : Nat) (meaning : Meaning)
    (growth : Option (Growth.Registered.Callbacks σ))
    {leftBase : PairInput.Context (Publication.Effects (Recorded σ))} {rightBase : PairInput.Context (Publication.Effects σ)}
    (budgets : leftBase.budget = rightBase.budget) (allocators : leftBase.allocator = rightBase.allocator)
    (queries : leftBase.queries = rightBase.queries) (owner usizeBits depth : Nat) :
    (Recursive.erasing (Publication.Effects.mapAllocator Recorded.effects)).Constructors
      (unfold (callerContext (Insertion.Recording.operations ops) (recordBacking allocate) runtimeSafety container meaning leftBase
        (growth.map recordGrowth)) owner usizeBits depth)
      (unfold (callerContext ops allocate runtimeSafety container meaning rightBase growth) owner usizeBits depth) :=
  unfold_caller_erases (HostTrace.transport ops.arguments) (Publication.Recording.probe_transport ops.probe)
    (bytes_transport ops.bytes) (object_transport ops.objects) (create_transport ops.create) (copy_transport ops.copy)
    (backing_transport allocate) runtimeSafety container meaning (optional_growth_transport growth)
    budgets allocators queries owner usizeBits depth

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
