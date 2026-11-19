/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerEnclosingMissFrames
import Compiler.Extraction.InternerEnclosingInsertionCoverage

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Derive the complete miss frame from original caller ownership and actual
native callbacks. Capacity, preparation/backing refusal, successful publication,
publication rollback and transferred insertion reuse the enclosing reducer.
Source coverage derives every ordinary insertion case for the admitted item
tag; no residual insertion-frame premise remains. -/
theorem Enclosing.native_miss_frames {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects σ) → Prop} (stack : Enclosing safety allocator owner parent)
    {before : World (Publication.Effects σ)} (initial : parent before)
    {source : View} {request : Interner.Request} {values : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator source request values before taken owned lookup)
    (rows : List Storage.Cell) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning)
    (p : Primitives (Publication.Effects σ))
    (published : p.publish = Publication.publish ops.probe ops.arguments allocator source)
    (inserted : p.insert = fun key slice deterministic =>
      Insertion.Native.insert ops allocate safety allocator owner source address meaning native key slice deterministic growth)
    (key : Key) (deterministic simplifying : Bool) (admitted : Admitted ops.arguments)
    (aligned : key.arguments = owned.items)
    (domain : (native.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) :
    MissFrames (Publication.external ops.arguments) allocator p
      (CallFrame safety allocator owner rows source request.arguments owned address native parent)
      (GraphFrame safety allocator owner rows parent) key owned lookup deterministic simplifying := by
  apply stack.missFrames initial origin rows address native ops.probe ops.arguments p published
    key deterministic simplifying aligned
  intro world frame
  simpa only [inserted] using stack.insertion_covered initial origin frame ops allocate growth meaning key deterministic
    admitted aligned domain

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
