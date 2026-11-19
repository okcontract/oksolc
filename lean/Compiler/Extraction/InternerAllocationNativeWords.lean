/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationRecursiveWords
import Compiler.Extraction.InternerAllocationRecursiveReplay

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


/-- Native dispatch consumes both closed recursive replay and closed recursive
word induction for the same stream and models. The complete actual execution
supplies the stream and its admission. Host/query admission and the live native
call frame remain explicit; there is no child-preservation or replay premise. -/
theorem recursive_dispatch_words (pushes : Associative.Pushes other) (pushValues : Insertion.Native.PushValues other)
    (depth : Nat)
    (rows : List Storage.Cell) (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop) (stack : Enclosing safety base.allocator owner parent)
    (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (initial : CallFrame safety base.allocator owner rows source values normalized address native parent (ChildTrace.erase before))
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety outerBase.allocator owner data capacity before rows)
    (key : Key) (aligned : key.arguments = normalized.items) (expected : Word) (operation : key.kind = 1)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : key.eval (Dispatch.wordDispatchMeaning env other) before.graph.read = some expected) :
    let nativeChildren := children ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits depth
    let action := ((context outerBase owner usizeBits nativeChildren debug).primitives source address native).simplify key normalized
    Semantic.Ensures (Dispatch.wordDispatchMeaning env other) before.graph (action before).1 (action before).2.graph
        (fun found after => ∀ id, found = some id → after.read id = some expected) := by
  intro nativeChildren action
  let leading : List ProtocolEvent := []
  let root := before
  let stream := ChildTrace.history (action before).2
  have inside : Resource.Admitted ChildTrace.history stream action before :=
    List.prefix_refl _
  let cursor := MissStream.childCursor leading.length root
  let predicate := Frame root (CallFrame safety base.allocator owner rows source values normalized address native parent)
  let completeStream := rebase leading (ChildTrace.history root).length stream
  let model := streamReplay completeStream
    (recursiveModels (Dispatch.wordDispatchMeaning env other) usizeBits seed completeStream mismatch depth)
  have proper := recursive_sources ops allocate safety owner usizeBits (Dispatch.wordDispatchMeaning env other)
    base growth outerOps outerAllocate outerBase outerGrowth hosts allocators budgets queries debug seed mismatch
    admitted outerAdmitted typed closedQuery capacityQuery classificationQuery depth
    leading stream root rows source values normalized address native parent stack
  have inputFrame : ∀ world, predicate world → InputFrame safety outerBase.allocator owner rows source values normalized world := by
    intro world held
    rw [allocators]
    have erased := held.1.1
    simpa only [ChildTrace.erase, InputFrame.mapAllocator_iff] using erased
  have words := recursive_words env other usizeBits seed completeStream mismatch pushes pushValues depth
  apply (Semantic.Ensures.cursor_iff _ before.graph (action before).2.graph (action before).1
    (cursor before) (cursor (action before).2) (fun found read => ∀ id, found = some id → read id = some expected)).mp
  apply safe_at _ (cursorGraph cursor before) (cursorGraph cursor (action before).2) (action before).1
    (Dispatch.simplify (Nested.storageReads rows) model usizeBits key.instruction key.arguments debug) _
  · intro completed
    exact (dispatcher_resource_projected ChildTrace.history stream (cursorGraph cursor) safety owner usizeBits
      outerBase nativeChildren model debug source values address native key normalized rows before data capacity
      facts aligned predicate ⟨initial, List.prefix_refl _⟩ inputFrame proper inside completed).2
  · have sound := Interner.representative_reads_sound (Dispatch.wordDispatchMeaning env other) before.graph valid
    simp only [Interner.representativeReads, facts.projected] at sound
    exact Dispatch.default_key_simplify_safe env other (Nested.storageReads rows) model words.correct words.addresses words.shifts
      (cursorGraph cursor before) (valid.with_cursor _) sound key operation expected debug usizeBits evaluated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
