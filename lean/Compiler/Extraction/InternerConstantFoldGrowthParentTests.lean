/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantFoldGrowthReturnTests
import Compiler.Extraction.InternerRecursiveGrowthTests
import Compiler.Extraction.InternerConstantFoldDispatchTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)
open RecursiveTests (Call debug)
open ConstantFoldTests

attribute [local irreducible] ConstantPublicationTests.ready rootArguments Call.constructed Call.stack

theorem child_equivalent (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) :
    (RecursiveGrowthTests.children safety (depth + 1) publishOK).constant (Unary.iszero.eval value) debug
      (parent safety value).taken.2.world = ((fullChild safety value).1, (fullChild safety value).2.world) := by
  have current := child_established safety value
  have room : Interner.Queries.queries.atCapacity (child safety value).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected, ConstantPublicationTests.rows_count]; decide
  have continuation :
      (child safety value).continuation (RecursiveGrowthTests.primitives safety depth ⟨0, 0, 0⟩ publishOK
        (child safety value).address (child safety value).native) =
      (child safety value).continuation (childPrimitives safety (child safety value).address (child safety value).native) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (child safety value).request.item.kind = 2 from rfl, BitVec.reduceBEq, Bool.false_eq_true,
      Bool.true_and, ↓reduceIte, handoff, graph, current.entry.origin.scope, bind, Effect.bind, pure, Effect.pure]
    rfl
  have same := NativeRecursion.Tests.same_call (child safety value)
    (RecursiveGrowthTests.primitives safety depth ⟨0, 0, 0⟩ publishOK) (childPrimitives safety)
    (child_observed safety value) current.item.graph room rfl continuation
  rw [RecursiveGrowthTests.children, NativeRecursion.constant_succ]
  exact congrArg (fun ran => (ran.1, ran.2.world)) same

theorem parent_simplified (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool)
    (after : Native.Frame Nat)
    (called : ((fullChild safety value).1, (fullChild safety value).2.world) = (.ok 5, returnedChild safety value after)) :
    (RecursiveGrowthTests.primitives safety (depth + 1) (rootSource safety value) publishOK
      (parent safety value).address (parent safety value).native).simplify (parent safety value).key
      (parent safety value).normalized (parent safety value).taken.2.world = (.ok (some 5), returnedChild safety value after) := by
  have current := (established safety value).taken
  have facts := current.native (by rw [ConstantPublicationTests.rows_count]; decide)
  simp only [RecursiveGrowthTests.primitives, NativeRecursion.dispatcher_snapshot]
  rw [facts.reads]
  apply iszero_result (input := NativeRecursion.operand) (address := (parent safety value).normalized.address)
    _ _ value _ _ _ (.ok 5) (ConstantPublicationTests.value_read safety value _ current).1
  exact (child_equivalent safety depth value publishOK).trans called

def inner (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) :=
  (parent safety value).invoked (RecursiveGrowthTests.primitives safety depth (rootSource safety value) publishOK)

theorem inner_contract (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) : ∃ after cleaned,
    ((fullChild safety value).1, (fullChild safety value).2.world) = (.ok 5, returnedChild safety value after) ∧
    inner safety (depth + 1) value publishOK =
      (if publishOK then .ok 5 else .error (.language .outOfMemory), (parent safety value).returned cleaned) ∧
    NativeGraph.Facts safety 7 6 ⟨backing safety value, 0⟩ 13
      (inner safety (depth + 1) value publishOK).2.world (rows safety value) ∧
    Closed (inner safety (depth + 1) value publishOK).2.scope ∧
    (inner safety (depth + 1) value publishOK).2.world.memory.effects.keys =
      (if publishOK then OwnedKeys.store (returnedChild safety value after).memory.effects.keys
        (parent safety value).key ⟨(parent safety value).normalized.address, 5⟩
       else (returnedChild safety value after).memory.effects.keys) ∧
    (if publishOK then SliceValid 7 (inner safety (depth + 1) value publishOK).2.world.memory.heap (parent safety value).normalized
     else Consumed (parent safety value).normalized (inner safety (depth + 1) value publishOK).2.world.memory) ∧
    (inner safety (depth + 1) value publishOK).2.world.memory.memory.heap.lookup (rootSource safety value).allocation =
      (parent safety value).before.memory.memory.heap.lookup (rootSource safety value).allocation ∧
    (inner safety (depth + 1) value publishOK).2.world.memory.heap ReachablePrefixTests.backing = none ∧
    (inner safety (depth + 1) value publishOK).2.world.memory.memory.heap.lookup ReachablePrefixTests.backing = none ∧
    (inner safety (depth + 1) value publishOK).2.world.graph.read = Storage.readValue (rows safety value) := by
  obtain ⟨after, called, facts, _, childKeys, native, _, oldDead, nativeDead, held, custody, privateSource⟩ := child_contract safety value
  have current := established safety value
  have origin := current.entry.origin
  have nativeFacts := facts.native (by simp only [rows, List.length_append, List.length_singleton, ConstantPublicationTests.rows_count]; decide)
  let entered : OwnedCall.State (Publication.Effects Nat) := ⟨returnedChild safety value after, (parent safety value).taken.2.scope⟩
  let resume : Action (Publication.Effects Nat) NodeId := do
    let _ ← graph (fun slice => Publication.publish (RecursiveGrowthTests.publicationProbe publishOK) ops.arguments 7
      (rootSource safety value) (parent safety value).key slice 5)
    handoff
    pure 5
  obtain ⟨published, cleaned, publication, finished, _, cleanFacts, post, keys, ownership, _⟩ :=
    nativeFacts.finish_publication (before := entered) (RecursiveGrowthTests.publicationProbe publishOK) ops.arguments
      (rootSource safety value) [4] (parent safety value).key (parent safety value).normalized (parent safety value).lookup
      5 publishOK ((returnedChild safety value after).memory.effects.allocator * 10 + 8)
      origin.scope origin.detached rfl held custody privateSource rfl
  have simplified := parent_simplified safety depth value publishOK after called
  have continued : (parent safety value).continuation (RecursiveGrowthTests.primitives safety (depth + 1)
      (rootSource safety value) publishOK (parent safety value).address (parent safety value).native) =
      resume entered := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (parent safety value).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      resume, entered, graph, origin.scope, simplified, bind, Effect.bind]
    simp only [RecursiveGrowthTests.primitives, NativeRecursion.context, RecursiveGrowthTests.base, callerPrimitives,
      Interner.findCode, Interner.ResultId.run]
  have room : Interner.Queries.queries.atCapacity (parent safety value).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected, ConstantPublicationTests.rows_count]; decide
  have routed := (parent safety value).route
    (RecursiveGrowthTests.primitives safety (depth + 1) (rootSource safety value) publishOK)
    (observed safety value) current.item.graph room rfl
  rw [continued] at routed
  change inner safety (depth + 1) value publishOK =
    (let done := (let (result, reached) := resume entered
       OwnedCall.finish (Publication.external ops.arguments) 7 result reached)
     if ordinary done.1 then (done.1, (parent safety value).returned done.2) else done) at routed
  change (let (result, reached) := resume entered
    OwnedCall.finish (Publication.external ops.arguments) 7 result reached) =
      (if publishOK then .ok 5 else .error (.language .outOfMemory), cleaned) at finished
  rw [finished] at routed
  have result : inner safety (depth + 1) value publishOK =
      (if publishOK then .ok 5 else .error (.language .outOfMemory), (parent safety value).returned cleaned) := by
    cases publishOK <;> exact routed
  have prior := (ConstantFoldTests.literal safety value).2.2.1
  obtain ⟨owner, found, _⟩ := prior.owner
  have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory found).1
  have finalFacts := (cleanFacts.cleanup ((parent safety value).before.memory.memory.nextId + 1) (by omega)).cleanup
    (parent safety value).before.memory.memory.nextId older
  have input := custody.publication (rootSource safety value) (parent safety value).key rfl privateSource nativeFacts.live
  have parentAbsent : (returnedChild safety value after).memory.effects.keys (parent safety value).key = none := by
    have apart : (parent safety value).key ≠ (child safety value).key := by
      intro same
      have kinds := congrArg Key.kind same
      exact (by decide : (1#32) ≠ 2#32) kinds
    rw [childKeys, OwnedKeys.store, if_neg apart]
    change (parent safety value).taken.2.world.memory.effects.keys (parent safety value).key = none
    have missed := (congrArg (fun graph => graph.table (parent safety value).key)
      (origin.graph.trans current.item.graph)).trans (parent_missed safety value)
    rw [current.taken.linked] at missed
    cases selected : (parent safety value).taken.2.world.memory.effects.keys (parent safety value).key with
    | none => rfl
    | some entry => simp only [OwnedKeys.view, selected, Option.map_some] at missed; contradiction
  have publishedMemory : published.memory.memory = (returnedChild safety value after).memory.memory ∧
      published.memory.heap = (returnedChild safety value after).memory.heap ∧
      published.graph.read = (returnedChild safety value after).graph.read := by
    cases publishOK with
    | false =>
      have ran := Publication.publish_oom (RecursiveGrowthTests.publicationProbe false) ops.arguments 7
        (rootSource safety value) (parent safety value).key (parent safety value).normalized 5 _ _
        (Publication.admit_complete _ _ _ _ _ input) rfl
      have same := congrArg Prod.snd (publication.symm.trans ran)
      change published = _ at same
      rw [same]
      exact ⟨rfl, rfl, rfl⟩
    | true =>
      have ran := Publication.publish_absent (RecursiveGrowthTests.publicationProbe true) ops.arguments 7
        (rootSource safety value) (parent safety value).key (parent safety value).normalized 5 _ _ rfl parentAbsent rfl
      have same := congrArg Prod.snd (publication.symm.trans ran)
      change published = _ at same
      rw [same]
      exact ⟨rfl, rfl, rfl⟩
  have sourcePublished := congrArg (fun memory => memory.heap.lookup (rootSource safety value).allocation) publishedMemory.1
  have publishedDead : published.memory.heap ReachablePrefixTests.backing = none ∧
      published.memory.memory.heap.lookup ReachablePrefixTests.backing = none := by
    rw [publishedMemory.1, publishedMemory.2.1]
    exact ⟨oldDead, nativeDead⟩
  have sourceClean : cleaned.world.memory.memory.heap.lookup (rootSource safety value).allocation =
      (returnedChild safety value after).memory.memory.heap.lookup (rootSource safety value).allocation ∧
      cleaned.world.memory.heap ReachablePrefixTests.backing = none ∧
      cleaned.world.memory.memory.heap.lookup ReachablePrefixTests.backing = none := by
    cases publishOK with
    | true => rw [post.handedOff rfl]; exact ⟨sourcePublished, publishedDead⟩
    | false =>
      have preserved := nativeFacts.publish (RecursiveGrowthTests.publicationProbe false) ops.arguments
        (rootSource safety value) [4] (parent safety value).key (parent safety value).normalized 5 false _
        rfl held custody privateSource rfl
      rw [publication] at preserved
      have pubHeld := preserved.2.2.1
      obtain ⟨memory, freed, _, released, _⟩ := free_valid (Publication.external ops.arguments) 7
        (parent safety value).normalized published.memory pubHeld.1.1 pubHeld.2.1
      have same : memory = cleaned.world.memory := congrArg Prod.snd (freed.symm.trans (post.freed rfl).1)
      rw [same] at released
      obtain ⟨_, _, array, arrayFound, _⟩ := current.constructed.owned
      have frame := released.frame ReachablePrefixTests.backing (origin.freshNative _ array arrayFound).symm
      exact ⟨(released.frame _ (held.2.2 (by decide))).2.trans sourcePublished,
        frame.1.trans publishedDead.1, frame.2.trans publishedDead.2⟩
  obtain ⟨sourceCell, sourceFound, _⟩ := (ConstantFoldTests.literal safety value).2.1.storage (by decide)
  have sourceChild := native _ sourceCell (origin.memory _ _ (current.item.memory _ _ sourceFound))
    (source_private safety value).2.1 (source_private safety value).2.2
  have sourceReturned := (parent safety value).returned_cell cleaned.world prior.valid _ sourceCell sourceFound
    (sourceClean.1.trans sourceChild)
  refine ⟨after, cleaned, called, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [result]; exact finalFacts
  · rw [result]; exact post.closed
  · rw [result]; exact keys
  · rw [result]
    cases publishOK with
    | true => exact ownership
    | false =>
      rcases ownership with empty | dead
      · exact Or.inl empty
      · refine Or.inr ⟨dead.1, ?_⟩
        apply Call.cleanup_missing _ _ _ (cleanFacts.valid.cleanup _ ((parent safety value).before.memory.memory.nextId + 1)).memory
        exact Call.cleanup_missing _ _ _ cleanFacts.valid.memory dead.2
  · rw [result]; exact sourceReturned.trans sourceFound.symm
  · rw [result]; exact sourceClean.2.1
  · rw [result]
    apply Call.cleanup_missing _ _ _ (cleanFacts.valid.cleanup _ ((parent safety value).before.memory.memory.nextId + 1)).memory
    exact Call.cleanup_missing _ _ _ cleanFacts.valid.memory sourceClean.2.2
  · rw [result]
    change cleaned.world.graph.read = _
    rw [post.graph, publishedMemory.2.2]
    rfl


def root (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) :=
  (RecursiveGrowthTests.children safety depth publishOK).operation 21 [4] debug (old safety value)

theorem root_route (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) :
    root safety (depth + 1) value publishOK =
      TemporaryArguments.unwind (old safety value).memory.memory.nextId (inner safety depth value publishOK) := by
  have prepared : Arguments.prepare [4] (old safety value) = (.ok (rootSource safety value), (parent safety value).before) := by
    simpa only [rootArguments] using (ConstantFoldTests.literal safety value).1
  rw [root, RecursiveGrowthTests.children, NativeRecursion.operation_succ,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ prepared]
  exact Arguments.returned_nonempty [4] _ _ rfl

theorem root_contract (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) :
    (root safety (depth + 2) value publishOK).1 = (if publishOK then .ok 5 else .error (.language .outOfMemory)) ∧
    NativeGraph.Facts safety 7 6 ⟨backing safety value, 0⟩ 13
      (root safety (depth + 2) value publishOK).2 (rows safety value) ∧
    (root safety (depth + 2) value publishOK).2.memory.memory.heap.lookup (rootSource safety value).allocation = none ∧
    (root safety (depth + 2) value publishOK).2.memory.effects.keys =
      (inner safety (depth + 1) value publishOK).2.world.memory.effects.keys ∧
    (if publishOK then SliceValid 7 (root safety (depth + 2) value publishOK).2.memory.heap (parent safety value).normalized
     else Consumed (parent safety value).normalized (root safety (depth + 2) value publishOK).2.memory) ∧
    (root safety (depth + 2) value publishOK).2.memory.heap ReachablePrefixTests.backing = none ∧
    (root safety (depth + 2) value publishOK).2.memory.memory.heap.lookup ReachablePrefixTests.backing = none ∧
    (root safety (depth + 2) value publishOK).2.graph.read = Storage.readValue (rows safety value) := by
  obtain ⟨after, cleaned, called, result, facts, closed, keys, ownership, sourceFrame, oldDead, nativeDead, reads⟩ :=
    inner_contract safety depth value publishOK
  have prepared := (ConstantFoldTests.literal safety value).2.1
  have prior := (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.1
  have returned := congrArg Prod.fst result
  have completed : ordinary (inner safety (depth + 1) value publishOK).1 = true := by
    rw [returned]; cases publishOK <;> rfl
  have reached : (root safety (depth + 2) value publishOK).2 =
      { (inner safety (depth + 1) value publishOK).2.world with memory :=
        { (inner safety (depth + 1) value publishOK).2.world.memory with memory :=
          (Compiler.ZigAir.Memory.cleanup (old safety value).memory.memory.nextId
            (inner safety (depth + 1) value publishOK).2.world.memory.memory) } } := by
    rw [show depth + 2 = (depth + 1) + 1 from rfl, root_route]
    simp only [TemporaryArguments.unwind, completed, ↓reduceIte]
  obtain ⟨owner, ownerFound, _⟩ := prior.owner
  have finalFacts := facts.cleanup (old safety value).memory.memory.nextId
    (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory ownerFound).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show depth + 2 = (depth + 1) + 1 from rfl, root_route]; exact returned
  · rw [reached]; exact finalFacts
  · rw [reached]
    exact prepared.retire [4] _ _ (rootSource safety value) (by decide) _ facts.valid.memory sourceFrame
  · rw [reached]
  · rw [reached]
    cases publishOK with
    | true => exact ownership
    | false =>
      rcases ownership with empty | dead
      · exact Or.inl empty
      · exact Or.inr ⟨dead.1, Call.cleanup_missing _ _ _ facts.valid.memory dead.2⟩
  · rw [reached]; exact oldDead
  · rw [reached]; exact Call.cleanup_missing _ _ _ facts.valid.memory nativeDead
  · rw [reached]; exact reads


/-- Child publication changes the actual key table before the parent resumes. -/
theorem child_keys (safety : Bool) (value : Word) :
    (fullChild safety value).2.world.memory.effects.keys =
      OwnedKeys.store (old safety value).memory.effects.keys (child safety value).key ⟨(child safety value).normalized.address, 5⟩ := by
  obtain ⟨after, called, _, _, keys, _⟩ := child_contract safety value
  have reached : (fullChild safety value).2.world = returnedChild safety value after := congrArg Prod.snd called
  rw [reached, keys]
  change OwnedKeys.store (parent safety value).taken.2.world.memory.effects.keys _ _ = _
  have current := established safety value
  rw [current.entry.keys, current.item.effects, (ConstantFoldTests.literal safety value).2.1.effects]

def resultKeys (safety : Bool) (value : Word) (publishOK : Bool) :=
  let keys := OwnedKeys.store (old safety value).memory.effects.keys (child safety value).key ⟨(child safety value).normalized.address, 5⟩
  if publishOK then OwnedKeys.store keys (parent safety value).key ⟨(parent safety value).normalized.address, 5⟩ else keys

theorem root_keys (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) :
    (root safety (depth + 2) value publishOK).2.memory.effects.keys = resultKeys safety value publishOK := by
  obtain ⟨after, _, called, _, _, _, keys, _⟩ := inner_contract safety depth value publishOK
  have reached : (fullChild safety value).2.world = returnedChild safety value after := congrArg Prod.snd called
  rw [(root_contract safety depth value publishOK).2.2.2.1, keys, ← reached, child_keys]
  rfl

/-- Both Push data reads follow the final native rows, after relocation,
publication and all local returns. The old and folded words are arbitrary. -/
theorem native_words (safety : Bool) (value : Word) (world : World (Publication.Effects Nat))
    (facts : NativeGraph.Facts safety 7 6 ⟨backing safety value, 0⟩ 13 world (rows safety value)) :
    Constant.value world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok (some value)) ∧
    Constant.value world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 5 = .ok (.ok (some (Unary.iszero.eval value))) := by
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have original : (rows safety value)[(4 : NodeId).toNat]? = some (ConstantPublicationTests.row safety value) := by
    change (ConstantPublicationTests.rows safety value ++ [row safety value])[4]? = _
    rw [List.getElem?_append, if_pos (by rw [ConstantPublicationTests.rows_count]; decide)]
    change (ReachablePrefixTests.cells safety 3 ++ [ConstantPublicationTests.row safety value])[4]? = _
    rw [List.getElem?_append, prior.count]
    rfl
  have added : (rows safety value)[(5 : NodeId).toNat]? = some (row safety value) := by
    change (ConstantPublicationTests.rows safety value ++ [row safety value])[5]? = _
    rw [List.getElem?_append, ConstantPublicationTests.rows_count]
    rfl
  have first : Storage.constantProgram.run (rows safety value) 4 = .ok (some value) := by
    simp only [Storage.constantProgram, Storage.ConstantRead.run, Storage.representative_correct, original]
    rfl
  have second : Storage.constantProgram.run (rows safety value) 5 = .ok (some (Unary.iszero.eval value)) := by
    simp only [Storage.constantProgram, Storage.ConstantRead.run, Storage.representative_correct, added]
    rfl
  exact ⟨(facts.constants 4).trans (congrArg Except.ok first), (facts.constants 5).trans (congrArg Except.ok second)⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldGrowthTests
