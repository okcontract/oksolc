/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInvocationTrace
import Compiler.Extraction.InternerInsertionNativeReplay
import Compiler.Extraction.InternerCallerTakenStream
import Compiler.Extraction.InternerCallerCloseTake
import Compiler.Extraction.InternerInvocationClose
import Compiler.Extraction.InternerCallerInsertionCapacityCompletion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Interner.InvocationTrace

-- Composition compares captured calls through their proved interfaces. Avoid
-- unfolding complete native executions when reporting a mismatched binding.
attribute [local irreducible] Caller.Initialization.capture Caller.Take.capture recordExecution

variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell)

/-- The exact insertion transcript occupies its own tagged slots in a shared
stream. Both protocol views retain the same indices; no cursor conversion or
synthetic allocation response stands in for a different protocol's call. -/
theorem scoped_insert_stream (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (mismatch : Fault)
    (leading trailing : List (Event Failure Fault)) (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells) (scope : Interner.Scoped.Scope) :
    let captured := recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth []
    let candidate := cell input key normalized ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects
    let stream := leading ++ captured.2.events.map Event.insertion ++ trailing
    let action := Interner.InsertionExecution.action candidate key deterministic (operations stream mismatch)
    let actual := insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before
    let logical := Interner.Scoped.liftGraph action ⟨scope, { before.graph with allocationCursor := leading.length }⟩
    actual.1 = logical.1.mapError OwnedCall.Fault.language ∧
      logical.2 = ⟨scope, { actual.2.graph with allocationCursor := leading.length + captured.2.events.length }⟩ ∧
      actual.2.memory = memory captured.2.effects := by
  have checked := scoped_insert_replayed ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch (insertions leading) (insertions trailing) backing header rows scope
  simpa only [operations, insertions_append, insertions_embed, insertions_length] using checked

/-- Source-order handoff, insertion and ordinary deferred close share the
actual insertion transcript. Its end cursor also starts close; no independent
final cursor or reached-world correspondence is assumed. -/
theorem finished_insert_stream (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (mismatch : Fault)
    (leading trailing : List (Event Failure Fault)) (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells) (scope : Interner.Scoped.Scope)
    (handle : Handle) (lookup : NormalizationOwnership.State)
    (present : scope.lookup = some lookup) (contents : scope.items = handle.values)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (owner : lookup.owner = .caller) :
    let captured := recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth []
    let candidate := cell input key normalized ((key.eval meaning before.graph.read).getD 0) captured.1.2 captured.2.effects
    let closeLeading := leading ++ captured.2.events.map Event.insertion
    let stream := closeLeading ++ trailing
    let action := Interner.InsertionExecution.action candidate key deterministic (operations stream mismatch)
    let logical := (do Interner.Scoped.handoff; Interner.Scoped.liftGraph action)
      ⟨scope, { before.graph with allocationCursor := leading.length }⟩
    let actual := insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before
    let finished := finishInsertion ops allocate safety allocator container source address meaning input key deterministic
      ⟨before, ⟨some handle, some normalized, false⟩⟩ growth
    Caller.Close.HandoffCompletion (Publication.external ops.arguments) allocator lookup handle normalized
      closeLeading trailing actual logical finished := by
  intro captured candidate closeLeading stream action logical actual finished
  have insertion := scoped_insert_stream ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch leading trailing backing header rows { scope with phase := .transfer }
  have shape : { scope with phase := .transfer } = ⟨some lookup, handle.values, .transfer⟩ := by
    cases scope
    simp_all only
  have result : actual.1 = logical.1.mapError OwnedCall.Fault.language := insertion.1
  have reached : logical.2 = ⟨⟨some lookup, handle.values, .transfer⟩,
      { actual.2.graph with allocationCursor := closeLeading.length }⟩ := by
    change (Interner.Scoped.liftGraph action
      ⟨{ scope with phase := .transfer }, { before.graph with allocationCursor := leading.length }⟩).2 = _
    simpa only [closeLeading, List.length_append, List.length_map, shape] using insertion.2.1
  refine ⟨?_, result, reached, ?_⟩
  · exact finish_handoff (Publication.external ops.arguments) allocator handle normalized before
      (fun slice => insert ops allocate safety allocator container source address meaning input key slice deterministic growth) detached
  · intro _
    have closed := Caller.Close.transferred_stream (Publication.external ops.arguments) allocator lookup handle normalized
      actual.2 closeLeading trailing detached unowned owner
    simpa only [reached] using closed.2.2.2

/-- Join actual successful initialization and take to insertion and close on
one tagged stream. Take supplies the entry heap, cursor and detached lookup;
insertion supplies the reached state and cursor consumed by deferred close.
Intervening dispatcher/children remain a separate composition obligation. -/
theorem initialized_insert_stream (external : External (Publication.Effects σ)) (budget : Nat) (commutative : Bool)
    (request : Interner.Request) (values : List NodeId) (before : World (Publication.Effects σ))
    (stack : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (prepared called : OwnedCall.State (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (mismatch : Fault)
    (leading trailing : List (Event Failure Fault)) (backing : Compiler.ZigAir.Memory.Address)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, stack))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted external)
    (initialized : Caller.initLookup external budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : OwnedCall.take external allocator prepared = (.ok (), called))
    (selectedSlice : called.scope.slice = some normalized)
    (header : readItems called.world.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : called.world.graph.representatives = some cells)
    (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let start := { before with memory := { before.memory with memory := stack } }
    let initialization := Caller.Initialization.capture external budget allocator commutative source buffer request.arguments start.memory
    let captured := recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells called.world growth []
    let candidate := cell input key normalized ((key.eval meaning called.world.graph.read).getD 0) captured.1.2 captured.2.effects
    ∃ lookup, initialization.1 = .ok (some lookup) ∧
      let handle := initialization.2.effects.handle
      let taken := Caller.Take.capture external allocator lookup.origin handle prepared.world.memory
      let insertionLeading := leading ++ initialization.2.events.map Event.normalization ++ taken.2.events.map Event.normalization
      let stream := insertionLeading ++ captured.2.events.map Event.insertion ++ trailing
      let resources := Interner.InvocationTrace.resources stream (.preparation .incomplete)
      let initialScope := Interner.Scoped.initScope resources request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
      let takeScope := Interner.Scoped.take resources initialScope.2
      let action := Interner.InsertionExecution.action candidate key deterministic (operations stream mismatch)
      let logical := Interner.Scoped.liftGraph action takeScope.2
      let actual := insert ops allocate safety allocator container source address meaning input key normalized deterministic growth called.world
      Caller.Initialization.checked initialization (normalizations leading)
        (taken.2.events ++ normalizations (captured.2.events.map Event.insertion ++ trailing)) request
        { before.graph with allocationCursor := leading.length } = .ok initialScope ∧
      Caller.Take.checked taken (normalizations leading ++ initialization.2.events)
        (normalizations (captured.2.events.map Event.insertion ++ trailing)) lookup values initialScope.2.heap = .ok takeScope ∧
      takeScope.1 = .ok () ∧
      takeScope.2.heap = { called.world.graph with allocationCursor := insertionLeading.length } ∧
      normalized.items = values ∧ Represents called.world.memory.memory (view normalized) values ∧
      request.item.eval (Folding.wordMeaning other) read values sequence =
        request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
      actual.1 = logical.1.mapError OwnedCall.Fault.language ∧
      logical.2 = ⟨takeScope.2.scope, { actual.2.graph with allocationCursor := insertionLeading.length + captured.2.events.length }⟩ ∧
      actual.2.memory = memory captured.2.effects ∧
      ∃ remaining, called.scope = ⟨some remaining, some normalized, false⟩ ∧ remaining.owned = none ∧
        takeScope.2.scope.lookup = some taken.1.2 ∧ takeScope.2.scope.items = remaining.values ∧
        taken.1.2.owned = false ∧ taken.1.2.owner = .caller ∧
        Caller.Close.HandoffCompletion (Publication.external ops.arguments) allocator taken.1.2 remaining normalized
          (insertionLeading ++ captured.2.events.map Event.insertion) trailing actual
          ((do Interner.Scoped.handoff; Interner.Scoped.liftGraph action) takeScope.2)
          (finishInsertion ops allocate safety allocator container source address meaning input key deterministic called growth) := by
  intro buffer start initialization captured candidate
  obtain ⟨lookup, recorded, prefixProof⟩ := Caller.Take.initialized_taken_stream external budget allocator commutative
    source request before stack pointer values prepared called leading other read sequence
    valid represented allocated decoded admitted initialized transferred
  refine ⟨lookup, recorded, ?_⟩
  intro handle taken insertionLeading stream resources initialScope takeScope action logical actual
  obtain ⟨slice, remaining, locals, lifetime, contents, unowned, owner, word, prefixProof⟩ := prefixProof
  have sameSlice : slice = normalized := Option.some.inj ((congrArg Local.slice locals).symm.trans selectedSlice)
  subst slice
  obtain ⟨_, _, initialCheck, takeCheck, takenResult, takenState⟩ := prefixProof (captured.2.events.map Event.insertion ++ trailing)
  have takenHeap : takeScope.2.heap = { called.world.graph with allocationCursor := insertionLeading.length } := by
    simpa only [takeScope, initialScope, resources, stream, insertionLeading, List.append_assoc] using congrArg Interner.Scoped.Session.heap takenState
  have represents : Represents called.world.memory.memory (view normalized) values := by
    simpa only [contents] using lifetime.contents
  have inserted := scoped_insert_stream ops allocate safety allocator container source address meaning input key normalized
    deterministic cells called.world growth mismatch insertionLeading trailing backing header rows takeScope.2.scope
  rw [← takenHeap] at inserted
  have tokenPresent : takeScope.2.scope.lookup = some taken.1.2 := by
    simpa only [takeScope, initialScope, resources, stream, insertionLeading, List.append_assoc] using
      congrArg (fun state : Interner.Scoped.Session => state.scope.lookup) takenState
  have tokenContents : takeScope.2.scope.items = remaining.values := by
    simpa only [takeScope, initialScope, resources, stream, insertionLeading, List.append_assoc] using
      congrArg (fun state : Interner.Scoped.Session => state.scope.items) takenState
  refine ⟨?_, ?_, ?_, takenHeap, lifetime.values.trans contents, represents, word,
    inserted.1, inserted.2.1, inserted.2.2, remaining, locals, lifetime.detached,
    tokenPresent, tokenContents, unowned, owner, ?_⟩
  · simpa only [initialScope, resources, stream, insertionLeading, List.append_assoc] using initialCheck
  · simpa only [takeScope, initialScope, resources, stream, insertionLeading, List.append_assoc] using takeCheck
  · simpa only [takeScope, initialScope, resources, stream, insertionLeading, List.append_assoc] using takenResult
  · have finished := finished_insert_stream ops allocate safety allocator container source address meaning input key normalized
      deterministic cells called.world growth mismatch insertionLeading trailing backing header rows takeScope.2.scope
      remaining taken.1.2 tokenPresent tokenContents lifetime.detached unowned owner
    have calledShape : (⟨called.world, ⟨some remaining, some normalized, false⟩⟩ : OwnedCall.State (Publication.Effects σ)) = called := by
      rw [← locals]
    rw [calledShape, ← takenHeap] at finished
    exact finished

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
