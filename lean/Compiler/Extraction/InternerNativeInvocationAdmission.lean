/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationInvocationWords
import Compiler.Extraction.InternerRecursiveHostLift

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive

attribute [local irreducible] NativeRecursion.unfold callerContext

/-- The same complete native invocation needs only its original host ports.
Recorded operations, growth, static context bindings and allocator admission
are constructed, rather than supplied as a second implementation. Initial
compiler graph/source/debug and query obligations remain explicit. -/
theorem native_invocation_verified (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (env : AddressMask.Environment) (other : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (debug : AssemblyItem.Fields.Values) (seed : Interner.Primitives) (mismatch : Insertion.Native.Fault)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (closedQuery : ∀ item, base.queries.deterministic item = Interner.Queries.queries.deterministic item)
    (capacityQuery : ∀ heap cursor, seed.atCapacity {heap with allocationCursor := cursor} = base.queries.atCapacity heap)
    (classificationQuery : ∀ item, seed.deterministic item = base.queries.deterministic item)
    (pushes : Associative.Pushes other) (pushValues : Insertion.Native.PushValues other)
    (depth : Nat) (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (stack : Enclosing safety base.allocator owner parent)
    (source : View) (request : Interner.Request) (before : World (Publication.Effects σ))
    (initial : parent before) (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph) (expected : Word)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some expected) :
    let nativeBase := callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth
    let nativeChildren := NativeRecursion.unfold nativeBase owner usizeBits depth
    InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent) before.graph
      (invoke nativeBase.external base.budget base.allocator
        ((context nativeBase owner usizeBits nativeChildren debug).primitives source) base.queries source request debug before) expected := by
  have hosts := ChildTrace.HostLift.hosts (ε := Caller.ProtocolTrace.ProtocolEvent) ops allocate growth
  exact recursive_invocation_verified ops allocate safety owner usizeBits env other base growth
    (ChildTrace.HostLift.operations ops) (ChildTrace.HostLift.backing allocate) (ChildTrace.HostLift.base base)
    (growth.map ChildTrace.HostLift.growth) hosts rfl rfl rfl debug seed mismatch admitted (hosts.arguments.admitted admitted)
    typed closedQuery capacityQuery classificationQuery pushes pushValues depth rows parent stack source request before
    initial data capacity facts represented privateSource array domain valid expected evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
