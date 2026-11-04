/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeLocalSetupTests
import Compiler.Extraction.InternerNativeCacheHit

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime)
open RecursiveTests (Call debug)
open RecursiveBorrowedTests (childContext)

def child (safety : Bool) : Call :=
  ⟨Interner.constructorCode.operationRequest 22 [0, 1], localSource, (copied safety).2⟩

attribute [local irreducible] BinaryPreludeTests.ready rootArguments copied

def cacheObservations (call : Call) :=
  ((prepare call.request.item debug call.before).1, call.constructed.memory.memory.nextId,
    Compiler.ZigAir.Memory.allocate call.constructed.memory.memory (.array 2 word),
    call.prepared.1, call.prepared.2.scope, Interner.Queries.queries.atCapacity call.constructed.graph,
    Interner.Queries.queries.deterministic call.request.item, call.constructed.graph.table call.key,
    Interner.makeKey call.request call.request.arguments)

def cacheExpected (call : Call) (id : NodeId) :=
  ((Except.ok call.address : Except Fault Compiler.ZigAir.Memory.Address), call.before.memory.memory.nextId + 1,
    (Except.ok (.pointer (.pointer true false (.array 2 word)) ⟨call.before.memory.memory.nextId + 1, 0⟩, call.stack) :
      Except Compiler.ZigAir.Memory.Fault (Compiler.ZigAir.Memory.Value × Compiler.ZigAir.Memory.State)),
    (Except.ok call.request.arguments : Except Fault (List NodeId)), (⟨some call.lookup, none, false⟩ : Local), false,
    (Except.ok true : Except Interner.Error Bool), some id, (Except.ok call.key : Except Interner.Error Key))

set_option maxHeartbeats 800000 in
/-- The cache-hit prefix never evaluates take or a recursive simplifier. -/
theorem cache_observed (safety : Bool) : cacheObservations (child safety) = cacheExpected (child safety) 4 := by
  cases safety <;> insertion_kernel_rfl

theorem cache_route (call : Call) (id : NodeId)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (observed : cacheObservations call = cacheExpected call id) :
    call.invoked p =
      (let done := OwnedCall.finish (Publication.external ops.arguments) 7 (.ok id) call.prepared.2
       if ordinary done.1 then (done.1, call.returned done.2) else done) := by
  simp only [cacheObservations, cacheExpected, Prod.mk.injEq] at observed
  obtain ⟨made, count, allocated, initialized, _, room, classified, found, keyed⟩ := observed
  have created : prepare call.request.item debug call.before = (.ok call.address, call.constructed) := Prod.ext made rfl
  have init : Caller.initLookup (Publication.external ops.arguments) 160 7 call.source
      ⟨call.constructed.memory.memory.nextId, 0, 2⟩ call.request
      ⟨{ call.constructed with memory := { call.constructed.memory with memory := call.stack } }, { lookup := none }⟩ =
        (.ok call.request.arguments, call.prepared.2) := by
    rw [count]; exact Prod.ext initialized rfl
  have routed := invoke_cached (Publication.external ops.arguments) 160 7 p Interner.Queries.queries
    call.source call.request debug call.before call.constructed call.address _ call.stack
    call.request.arguments call.prepared.2 call.key id created room allocated init classified keyed found
  simpa only [Call.invoked, returnWorld, Call.returned, Call.returnedWorld, count] using routed

/-- The fixture has a detached lookup. Its result specializes the general
cache routing; ownership-sensitive cleanup is proved by the general entry theorem. -/
theorem cache_result (call : Call) (id : NodeId)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives (Publication.Effects Nat))
    (observed : cacheObservations call = cacheExpected call id) :
    call.invoked p = (.ok id, call.returned ⟨call.prepared.2.world, ⟨none, none, false⟩⟩) := by
  have routed := cache_route call id p observed
  simp only [cacheObservations, cacheExpected, Prod.mk.injEq] at observed
  have closed := deinit_detached (Publication.external ops.arguments) 7 call.prepared.2 call.lookup
    (by rw [observed.2.2.2.2.1]) rfl
  simpa only [OwnedCall.finish, ordinary, ↓reduceIte, OwnedCall.cleanup, observed.2.2.2.2.1,
    Bool.false_eq_true, closed] using routed

def localReturned (safety : Bool) :=
  TemporaryArguments.unwind (parent safety).taken.2.world.memory.memory.nextId
    (.ok 4, (child safety).returned ⟨(child safety).prepared.2.world, ⟨none, none, false⟩⟩)

/-- The complete child constructor returns through lookup, scratch, item and
named-local cleanup. Its proper recursive callbacks are arbitrary: cache lookup
proves that none of them is reached. -/
theorem local_result (safety : Bool) (children : NativeRecursion.Constructors (Publication.Effects Nat)) :
    ViewInput.localOperation (NativeRecursion.context (childContext safety) 6 64 children debug)
      22 (view BinaryPreludeTests.operands) 0 1 0 0 true debug (parent safety).taken.2.world = localReturned safety := by
  have routed := cache_result (child safety) 4
    ((NativeRecursion.context (childContext safety) 6 64 children debug).primitives localSource) (cache_observed safety)
  have prepared : LocalArguments.zigLocal (view BinaryPreludeTests.operands) 0 0 true (parent safety).taken.2.world =
      (.ok localSource, (copied safety).2) := by
    simpa only [copied] using
      (Prod.ext (parent_observed safety).2.2 rfl : copied safety = (.ok localSource, (copied safety).2))
  rw [ViewInput.local_prepared _ _ _ _ _ _ _ _ _ _ _ _ prepared]
  change TemporaryArguments.unwind _ ((child safety).invoked _) = _
  rw [routed]
  rfl

/-- The cache-hit child retains the live parent through its actual item,
scratch and normalization prefix, then retires its named local at the captured
mark. Final graph correspondence and local death are not fixture observations. -/
theorem local_native (safety : Bool) :
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (localReturned safety).2 (BinaryPreludeTests.rows safety false) ∧
    (localReturned safety).2.graph = (parent safety).taken.2.world.graph ∧
    (localReturned safety).2.memory.effects.keys = (parent safety).taken.2.world.memory.effects.keys ∧
    (∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell →
      (localReturned safety).2.memory.memory.heap.lookup id = some cell) ∧
    (∀ id block, (parent safety).taken.2.world.memory.heap id = some block →
      (localReturned safety).2.memory.heap id = some block) ∧
    (localReturned safety).2.memory.memory.heap.lookup localSource.allocation = none := by
  have preparedLocal := (local_input safety 0).1
  have prior := (parent_established safety).taken.native (by rw [BinaryPreludeTests.rows_count]; decide)
  have observed := cache_observed safety
  simp only [cacheObservations, cacheExpected, Prod.mk.injEq] at observed
  obtain ⟨made, count, allocated, initialized, _, room, classified, found, keyed⟩ := observed
  have initializedCall : Caller.initLookup (Publication.external ops.arguments) 160 7 localSource
      ⟨(child safety).constructed.memory.memory.nextId, 0, 2⟩ (child safety).request
      ⟨{ (child safety).constructed with memory := { (child safety).constructed.memory with memory := (child safety).stack } },
        { lookup := none }⟩ = (.ok (child safety).request.arguments, (child safety).prepared.2) := by
    rw [count]; exact Prod.ext initialized rfl
  have verified := invoke_cached_native ops.arguments 160 7 6 5 safety ⟨ReachablePrefixTests.backing, 0⟩
    (BinaryPreludeTests.rows safety false) ((childContext safety).primitives localSource) Interner.Queries.queries
    localSource (child safety).request debug (child safety).before (child safety).constructed (child safety).address
    _ (child safety).stack (child safety).request.arguments (child safety).prepared.2 (child safety).key 4
    (local_input safety 0).2.1 preparedLocal.good.2 (Normalization.Tests.external_admitted _)
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid
    (Prod.ext made rfl) room allocated initializedCall classified keyed found
  have routed := cache_result (child safety) 4 ((childContext safety).primitives localSource) (cache_observed safety)
  unfold Call.invoked at routed
  rw [show (child safety).source = localSource from rfl] at routed
  dsimp only at verified
  rw [routed] at verified
  obtain ⟨_, _, innerGood, _, innerGraph, innerKeys, innerFrame, innerRegistry, _⟩ := verified
  have innerValid := innerGood.1
  let inner := (child safety).returnedWorld (child safety).prepared.2.world
  have reached : (localReturned safety).2 = { inner with memory := { inner.memory with
      memory := Compiler.ZigAir.Memory.cleanup (parent safety).taken.2.world.memory.memory.nextId inner.memory.memory } } := rfl
  have valid : Valid (localReturned safety).2.memory := by rw [reached]; exact innerValid.cleanup _ _
  have frame : ∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell →
      (localReturned safety).2.memory.memory.heap.lookup id = some cell := by
    intro id cell found
    rw [reached]
    exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id
      (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory found).1).trans
      (innerFrame id cell (preparedLocal.frame id cell found))
  have registry : ∀ id block, (parent safety).taken.2.world.memory.heap id = some block →
      (localReturned safety).2.memory.heap id = some block := by
    intro id block found
    apply innerRegistry id block
    change (copied safety).2.memory.heap id = _
    rw [preparedLocal.heap]; exact found
  have graph : (localReturned safety).2.graph = (parent safety).taken.2.world.graph :=
    innerGraph.trans preparedLocal.graph
  have keys : (localReturned safety).2.memory.effects.keys = (parent safety).taken.2.world.memory.effects.keys :=
    innerKeys.trans (congrArg Publication.Effects.keys preparedLocal.effects)
  refine ⟨prior.frame valid ((congrArg Interner.Heap.representatives graph).trans prior.projected)
    (congrArg Interner.Heap.table graph) keys (fun id cell found _ => frame id cell found) registry,
    graph, keys, frame, registry, ?_⟩
  obtain ⟨cell, found, _, _, _⟩ := preparedLocal.storage (by decide)
  rw [reached]
  exact preparedLocal.retire [0, 1] _ _ localSource (by decide) _ innerValid.memory
    ((innerFrame _ _ found).trans found.symm)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests
