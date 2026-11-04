/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationConstructorWords
import Compiler.Extraction.InternerAllocationConstructorTransfer

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (env : AddressMask.Environment) (other : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (hosts : Insertion.Native.HostBindings outerOps ops outerAllocate allocate outerGrowth growth Prod.fst)
    (allocators : outerBase.allocator = base.allocator) (budgets : outerBase.budget = base.budget)
    (queries : outerBase.queries = base.queries)
    (debug : AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (mismatch : Insertion.Native.Fault)
    (admitted : Admitted ops.arguments) (outerAdmitted : Admitted outerOps.arguments)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (closedQuery : ∀ item, outerBase.queries.deterministic item = Interner.Queries.queries.deterministic item)
    (capacityQuery : ∀ heap cursor, seed.atCapacity {heap with allocationCursor := cursor} = outerBase.queries.atCapacity heap)
    (classificationQuery : ∀ item, seed.deterministic item = outerBase.queries.deterministic item)

include hosts allocators budgets queries admitted outerAdmitted typed closedQuery capacityQuery classificationQuery mismatch

variable (pushes : Associative.Pushes other) (pushValues : Insertion.Native.PushValues other) (depth : Nat)
    (rows : List Storage.Cell) (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner parent)
    (before : World (Publication.Effects σ))
    (initial : CallFrame safety base.allocator owner rows source values normalized address native parent before)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)

include pushes pushValues stack initial valid

/-- Complete raw operation preservation at every finite depth. Replay, child
word laws and the allocation stream are derived, not supplied by the caller. -/
theorem recursive_operation_words (opcode : Opcode) (operands : List NodeId) (expected : Word)
    (evaluated : (Interner.constructorCode.operationRequest opcode operands).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read operands 0 = some expected) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other)
      (CallFrame safety base.allocator owner rows source values normalized address native parent) before.graph
      ((NativeRecursion.unfold (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
        owner usizeBits depth).operation opcode operands debug before) expected := by
  refine captured_constructor_words _ _ _ _
    (fun stream => (streamReplay stream (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)).operation
      opcode operands debug)
    ((children_erases ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits depth).operation opcode operands debug)
    before initial expected ?_ ?_
  · intro stream
    have related := recursive_sources ops allocate safety owner usizeBits (Dispatch.wordDispatchMeaning env other)
      base growth outerOps outerAllocate outerBase outerGrowth hosts allocators budgets queries debug seed mismatch
      admitted outerAdmitted typed closedQuery capacityQuery classificationQuery depth
      [] stream (ChildTrace.restore [] before) rows source values normalized address native parent stack
    exact related.operation opcode operands ()
  · intro stream
    exact recursive_operation_safe env other usizeBits seed stream mismatch pushes pushValues depth opcode operands debug _ expected
      (valid.with_cursor _) evaluated

/-- Complete native constant creation, including the enclosing frame and return. -/
theorem recursive_constant_words (value : Word) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other)
      (CallFrame safety base.allocator owner rows source values normalized address native parent) before.graph
      ((NativeRecursion.unfold (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
        owner usizeBits depth).constant value debug before) value := by
  refine captured_constructor_words _ _ _ _
    (fun stream => (streamReplay stream (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)).constant value debug)
    ((children_erases ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits depth).constant value debug)
    before initial value ?_ ?_
  · intro stream
    have related := recursive_sources ops allocate safety owner usizeBits (Dispatch.wordDispatchMeaning env other)
      base growth outerOps outerAllocate outerBase outerGrowth hosts allocators budgets queries debug seed mismatch
      admitted outerAdmitted typed closedQuery capacityQuery classificationQuery depth
      [] stream (ChildTrace.restore [] before) rows source values normalized address native parent stack
    exact related.constant value ()
  · intro stream
    exact recursive_constant_safe env other usizeBits seed stream mismatch pushes pushValues depth value debug _
      (valid.with_cursor _)

/-- Materialization preserves the requested value for every original node ID. -/
theorem recursive_materialize_words (original : NodeId) (value : Word) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other)
      (CallFrame safety base.allocator owner rows source values normalized address native parent) before.graph
      ((NativeRecursion.unfold (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
        owner usizeBits depth).materialize original value debug before) value := by
  refine captured_constructor_words _ _ _ _
    (fun stream => (streamReplay stream (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)).materialize original value debug)
    ((children_erases ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits depth).materialize original value debug)
    before initial value ?_ ?_
  · intro stream
    have related := recursive_sources ops allocate safety owner usizeBits (Dispatch.wordDispatchMeaning env other)
      base growth outerOps outerAllocate outerBase outerGrowth hosts allocators budgets queries debug seed mismatch
      admitted outerAdmitted typed closedQuery capacityQuery classificationQuery depth
      [] stream (ChildTrace.restore [] before) rows source values normalized address native parent stack
    exact related.materialize original value ()
  · intro stream
    exact recursive_materialize_safe env other usizeBits seed stream mismatch pushes pushValues depth original value debug _
      (valid.with_cursor _)

/-- The borrowed slice must be returned by the actual graph query. The requested
operation may differ from the queried opcode, as in the native dispatcher. -/
theorem recursive_borrowed_words (id : NodeId) (queried opcode : Opcode) (slice : ArgumentSlice)
    (found : (Nested.storageReads rows).operation id queried = .ok (some slice))
    (expected : Word)
    (evaluated : (Interner.constructorCode.operationRequest opcode slice.items).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read slice.items 0 = some expected) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other)
      (CallFrame safety base.allocator owner rows source values normalized address native parent) before.graph
      ((NativeRecursion.unfold (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
        owner usizeBits depth).borrowedOperation slice.address opcode slice.items debug before) expected := by
  refine captured_constructor_words _ _ _ _
    (fun stream => (streamReplay stream (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)).borrowedOperation slice.address opcode slice.items debug)
    ((children_erases ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits depth).borrowedOperation slice.address opcode slice.items debug)
    before initial expected ?_ ?_
  · intro stream
    have related := recursive_sources ops allocate safety owner usizeBits (Dispatch.wordDispatchMeaning env other)
      base growth outerOps outerAllocate outerBase outerGrowth hosts allocators budgets queries debug seed mismatch
      admitted outerAdmitted typed closedQuery capacityQuery classificationQuery depth
      [] stream (ChildTrace.restore [] before) rows source values normalized address native parent stack
    exact related.borrowedOperation id queried slice found opcode ()
  · intro stream
    exact recursive_borrowed_safe env other usizeBits seed stream mismatch pushes pushValues depth slice.address opcode slice.items debug _ expected
      (valid.with_cursor _) evaluated

/-- Local construction retains the source query, binary shape, overwrite bound,
and exact operands after the conditional overwrite. -/
theorem recursive_local_words (id : NodeId) (opcode : Opcode) (slice : ArgumentSlice)
    (found : (Nested.storageReads rows).operation id opcode = .ok (some slice)) (shape : slice.items.length = 2)
    (selected : Nat) (bound : selected < 2) (repeated : NodeId) (first : Bool) (expected : Word)
    (evaluated : (Interner.constructorCode.operationRequest opcode
      (if first then slice.items.set selected repeated else slice.items)).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read
      (if first then slice.items.set selected repeated else slice.items) 0 = some expected) :
    ConstructorPost (Dispatch.wordDispatchMeaning env other)
      (CallFrame safety base.allocator owner rows source values normalized address native parent) before.graph
      ((NativeRecursion.unfold (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
        owner usizeBits depth).localOperation opcode slice selected repeated first debug before) expected := by
  refine captured_constructor_words _ _ _ _
    (fun stream => (streamReplay stream (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed stream mismatch depth)).localOperation opcode slice selected repeated first debug)
    ((children_erases ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits depth).localOperation opcode slice selected repeated first debug)
    before initial expected ?_ ?_
  · intro stream
    have related := recursive_sources ops allocate safety owner usizeBits (Dispatch.wordDispatchMeaning env other)
      base growth outerOps outerAllocate outerBase outerGrowth hosts allocators budgets queries debug seed mismatch
      admitted outerAdmitted typed closedQuery capacityQuery classificationQuery depth
      [] stream (ChildTrace.restore [] before) rows source values normalized address native parent stack
    exact related.localOperation id opcode slice found shape selected bound repeated first ()
  · intro stream
    exact recursive_local_safe env other usizeBits seed stream mismatch pushes pushValues depth opcode slice selected repeated first debug _ expected
      (valid.with_cursor _) evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
