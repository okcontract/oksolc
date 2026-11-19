/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionControlEffects
import Compiler.Extraction.InternerCallerNativeRouting
import Compiler.Extraction.InternerNativeRecursionEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

variable {project : σ → τ} {left : Insertion.Operations σ} {right : Insertion.Operations τ}
  (creation : HostTransport project left.create right.create) (cloning : HostTransport project left.copy right.copy)
  (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
  (runtimeSafety : Bool) (allocator container : Nat) (meaning : Meaning)
  (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ))
  (remaining : ∀ source address input key normalized,
    Insertion.Native.CallbackObligations project left right leftAllocate rightAllocate runtimeSafety allocator container
      source address input key normalized leftGrowth rightGrowth)
  {leftBase : PairInput.Context (Publication.Effects σ)} {rightBase : PairInput.Context (Publication.Effects τ)}
  (external : leftBase.external.Transport rightBase.external (Publication.Effects.mapAllocator project))
  (budgets : leftBase.budget = rightBase.budget) (allocators : leftBase.allocator = rightBase.allocator)
  (queries : leftBase.queries = rightBase.queries)
  (published : ∀ source address input key owned id,
    Effect.Transport (World.mapEffects (Publication.Effects.mapAllocator project))
      ((leftBase.primitives source address input).publish key owned id)
      ((rightBase.primitives source address input).publish key owned id))
include creation cloning remaining external budgets allocators queries published

/-- The production caller adapter replaces seed insertion. Its complete
transport is derived from the source executor and local callback obligations;
neither seed insertion nor seed simplification agreement is required. -/
theorem base_native_transport :
    BaseTransport
      { leftBase with primitives := fun source address input =>
        (Insertion.Native.callerPrimitives left leftAllocate runtimeSafety allocator container source address meaning input
          (leftBase.primitives source address input) leftGrowth) }
      { rightBase with primitives := fun source address input =>
        (Insertion.Native.callerPrimitives right rightAllocate runtimeSafety allocator container source address meaning input
          (rightBase.primitives source address input) rightGrowth) }
      (Publication.Effects.mapAllocator project) := by
  refine ⟨external, budgets, allocators, queries, ?_, ?_⟩
  · exact published
  · intro source address input key normalized deterministic
    exact Insertion.Native.insert_transport creation cloning leftAllocate rightAllocate runtimeSafety allocator container
      source address input key normalized leftGrowth rightGrowth (remaining source address input key normalized) meaning deterministic

/-- Consume the derived insertion boundary in the existing all-entry induction.
The remaining assumptions name compiler-local callbacks; no whole-insertion
erasure premise or proper-child erasure hypothesis survives in this statement. -/
theorem unfold_native_erases (owner usizeBits depth : Nat) :
    (Recursive.erasing (Publication.Effects.mapAllocator project)).Constructors
      (unfold { leftBase with primitives := fun source address input =>
        (Insertion.Native.callerPrimitives left leftAllocate runtimeSafety allocator container source address meaning input
          (leftBase.primitives source address input) leftGrowth) } owner usizeBits depth)
      (unfold { rightBase with primitives := fun source address input =>
        (Insertion.Native.callerPrimitives right rightAllocate runtimeSafety allocator container source address meaning input
          (rightBase.primitives source address input) rightGrowth) } owner usizeBits depth) :=
  unfold_erases (base_native_transport creation cloning leftAllocate rightAllocate runtimeSafety allocator container meaning
    leftGrowth rightGrowth remaining external budgets allocators queries published) owner usizeBits depth

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
