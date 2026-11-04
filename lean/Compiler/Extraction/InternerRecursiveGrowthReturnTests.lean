/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveGrowthAllocationTests
import Compiler.Extraction.InternerNativeParentReturn
import Compiler.Extraction.InternerNativeParentEntry
import Compiler.Extraction.InternerEnclosingRollbackFrames

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime growth GraphFacts)
open RecursiveTests (Call debug cleanup_missing)
open RecursiveNonemptyTests

attribute [local irreducible] ready rootArguments childArguments Arguments.operation

/-- Select the simplified-call publication outcome. The existing native
insertion continues to use its successful probe in the same recursive context. -/
def publicationProbe (accepted : Bool) : OwnedKeys.Physical.Probe Nat :=
  fun key state => (accepted, (ops.probe key state).2)

def base (safety : Bool) (publishOK : Bool := true) : AlgebraicInput.Context (Publication.Effects Nat) :=
  ⟨Publication.external ops.arguments, 160, 7,
    fun source address native => callerPrimitives ops ReachablePrefixTests.allocate safety 7 6 source address
      Insertion.Tests.model native
      { childSeed source with publish := Publication.publish (publicationProbe publishOK) ops.arguments 7 source }
      (some growth), Interner.Queries.queries⟩
def children (safety : Bool) (depth : Nat) (publishOK : Bool := true) :=
  NativeRecursion.unfold (base safety publishOK) 6 64 depth
def primitives (safety : Bool) (depth : Nat) (source : View) (publishOK : Bool := true) :=
  (NativeRecursion.context (base safety publishOK) 6 64 (children safety depth publishOK) debug).primitives source
def returnedChild (safety : Bool) (after : Native.Frame Nat) :=
  let world := (child safety).returnedWorld (appendedWorld safety after)
  { world with memory := { world.memory with
    memory := Compiler.ZigAir.Memory.cleanup (parent safety).taken.2.world.memory.memory.nextId world.memory.memory } }

theorem prefix_keys (safety : Bool) :
    (child safety).constructed.memory.effects.keys = (parent safety).taken.2.world.memory.effects.keys ∧
    (child safety).constructed.memory.effects.keys (child safety).key = none ∧
    (child safety).constructed.memory.effects.keys (parent safety).key = none := by
  refine ⟨(congrArg Publication.Effects.keys (child_established safety).item.effects).trans
    (congrArg Publication.Effects.keys (child_literal safety).1.effects), ?_, ?_⟩ <;>
    cases safety <;> insertion_kernel_rfl

theorem prefix_geometry (safety : Bool) :
    (child safety).before.memory.memory.nextId = 29 ∧ (parent safety).normalized.address = 27 := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl⟩

/-- The reached caller frame comes from the actual literal, item initialization
and normalization/take. Literal freshness also separates it from the two native
regions that child relocation may change. -/
theorem parent_input (safety : Bool) :
    NativeRecursion.InputFrame safety 7 6 (rows safety) rootSource [0, 4]
      (parent safety).normalized (parent safety).taken.2.world ∧
    rootSource.allocation ≠ 6 ∧ rootSource.allocation ≠ ReachablePrefixTests.backing := by
  have literal := (parent_literal safety).1
  have initial := (zero_contract safety).2.1
  have established := parent_established safety
  have privateSource : Caller.SourcePrivate rootSource (parent safety).constructed.memory.effects.keys := by
    rw [congrArg Publication.Effects.keys established.item.effects]
    change Caller.SourcePrivate rootSource (rootArguments safety).2.memory.effects.keys
    rw [congrArg Publication.Effects.keys literal.effects]
    exact fun key => literal.key_apart [0, 4] _ _ rootSource initial.valid 7 key initial.live
  obtain ⟨ownerCell, ownerFound, _⟩ := initial.owner
  obtain ⟨_, _, backingCell, backingFound, _⟩ := initial.owned
  exact ⟨NativeRecursion.InputFrame.caller established.entry
      (established.constructed.native (by rw [rows_count]; decide)) privateSource,
    literal.native_apart [0, 4] _ _ rootSource initial.valid 6 ownerCell ownerFound (by decide),
    literal.native_apart [0, 4] _ _ rootSource initial.valid ReachablePrefixTests.backing backingCell backingFound (by decide)⟩

/-- The actual parent literal retains its allocation type through item
initialization and normalization. Proper children now carry this same fact. -/
theorem parent_array (safety : Bool) : ArraySource rootSource (parent safety).taken.2.world.memory.memory :=
  (parent_literal safety).1.arraySource.frame (fun _ cell found =>
    (parent_established safety).entry.origin.memory _ cell ((parent_established safety).item.memory _ cell found))

/-- Literal, item and normalization preparation specialize the general child
entry. Both live frames are derived before the existing growth continuation. -/
theorem child_entry (safety : Bool) :
    NativeRecursion.CallFrame safety 7 6 (rows safety) rootSource [0, 4] (parent safety).normalized
      (parent safety).address (parent safety).native (fun _ => True) (child safety).constructed ∧
    NativeRecursion.CallFrame safety 7 6 (rows safety) childSource [0] (child safety).normalized
      (child safety).address (child safety).native
      (NativeRecursion.CallFrame safety 7 6 (rows safety) rootSource [0, 4] (parent safety).normalized
        (parent safety).address (parent safety).native (fun _ => True)) (child safety).taken.2.world := by
  have literal := (child_literal safety).1
  have initial : NativeRecursion.CallFrame safety 7 6 (rows safety) rootSource [0, 4] (parent safety).normalized
      (parent safety).address (parent safety).native (fun _ => True) (parent safety).taken.2.world :=
    ⟨(parent_input safety).1, (parent_established safety).entry.item, trivial, parent_array safety⟩
  have before := initial.arguments literal trivial
  have facts := (child_literal safety).2.native (by rw [rows_count]; decide)
  have privateSource : Caller.SourcePrivate childSource (child safety).before.memory.effects.keys := by
    change Caller.SourcePrivate childSource (childArguments safety).2.memory.effects.keys
    rw [congrArg Publication.Effects.keys literal.effects]
    exact fun key => literal.key_apart [0] _ _ childSource initial.1.2.1.1 7 key
      (parent_established safety).taken.live
  obtain ⟨made, count, allocated, initialized, transferred, scope, _, keyed⟩ :=
    (child safety).prefix_results (calls_observed safety true)
  have initCall : Caller.initLookup (Publication.external ops.arguments) 160 7 childSource
      ⟨(child safety).constructed.memory.memory.nextId, 0, 2⟩ (child safety).request
      ⟨{ (child safety).constructed with memory := { (child safety).constructed.memory with memory := (child safety).stack } },
        { lookup := none }⟩ = (.ok [0], (child safety).prepared.2) := by
    rw [count]; exact Prod.ext initialized rfl
  obtain ⟨_, parentConstructed, normalized, lookup, entry, ready⟩ := NativeRecursion.CallFrame.enter_child
    ops.arguments 160 childSource (child safety).request debug (child safety).before (child safety).constructed
    (child safety).address (child safety).stack _ [0] (child safety).prepared.2 (child safety).taken.2
    (child safety).key facts before literal.good literal.arraySource privateSource (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide)
    AssemblyItem.Initializers.Tests.debug_valid (Normalization.Tests.external_admitted _)
    made allocated initCall
    (by simpa only [Call.taken] using (Prod.ext transferred rfl : (child safety).taken = (.ok (), (child safety).taken.2)))
    keyed trivial trivial
  have same := Local.mk.inj (entry.origin.scope.symm.trans scope)
  cases Option.some.inj same.1
  cases Option.some.inj same.2.1
  exact ⟨parentConstructed, ready⟩

/-- Reuse the existing child prefix, changing only the admitted publication
outcome of native insertion. The effects remain those of the original probe. -/
def rollbackOps : Insertion.Operations Nat := { ops with probe := publicationProbe false }

theorem child_refused (safety : Bool) :
    RelocatedPublication rollbackOps ReachablePrefixTests.allocate safety 7 6 Insertion.Tests.model
      (child safety).native (child safety).key (child safety).normalized (some growth) false (child safety).taken.2.world := by
  obtain ⟨_, oldCapacity, capacity, capacityRead, nonempty, full, selected, size,
    context, returnAddress, release, growthIdentity, operands, remaining, duplicated, object, allocated,
    copied, middle, base, effects, probeEffects, duplicateCall, createCall, cloneCall, backing, response, unlocked⟩ :=
    child_published safety
  refine ⟨oldCapacity, capacity, capacityRead, nonempty, full, selected, size,
    context, returnAddress, release, growthIdentity, operands, remaining, duplicated, object, allocated,
    copied, middle, base, effects, probeEffects, duplicateCall, createCall, cloneCall, backing, ?_, unlocked⟩
  intro installed assigned
  have effectsEqual := congrArg Prod.snd (response installed assigned)
  change (false, _) = (false, probeEffects)
  exact Prod.ext rfl effectsEqual

/-- A real nested child relocates storage, then fails publication. Its parent
keeps its source, native item and normalized allocation; the child's private
owner is consumed. This specializes the same enclosing law as the joint item. -/
theorem child_rollback_parent (safety : Bool) :
    let actual := Insertion.Native.insert rollbackOps ReachablePrefixTests.allocate safety 7 6 childSource
      (child safety).address Insertion.Tests.model (child safety).native (child safety).key
      (child safety).normalized true (some growth) (child safety).taken.2.world
    actual.1 = .error (.language .outOfMemory) ∧
      NativeRecursion.CallFrame safety 7 6 (rows safety) rootSource [0, 4] (parent safety).normalized
        (parent safety).address (parent safety).native (fun _ => True) actual.2 ∧
      Consumed (child safety).normalized actual.2.memory := by
  have established := child_established safety
  have current := established.taken.native (by rw [rows_count]; decide)
  let stack : NativeRecursion.Enclosing (σ := Nat) safety 7 6
      (NativeRecursion.CallFrame safety 7 6 (rows safety) rootSource [0, 4] (parent safety).normalized
        (parent safety).address (parent safety).native (fun _ => True)) := .call .root
  obtain ⟨result, added, data, capacity, facts, post⟩ := (child_entry safety).2.publication_rollback_frame
    rollbackOps ReachablePrefixTests.allocate (some growth) Insertion.Tests.model (child safety).key
    (Normalization.Tests.external_admitted _) established.entry.publication.aligned
    (by rw [current.projected]; simp only [Option.getD_some, rows_count]; decide)
    (Or.inr (Or.inr (child_refused safety)))
  exact ⟨result, stack.rolled_back (child_entry safety).1 (child_entry safety).2.parent
    established.entry.origin facts post, post.consumed⟩

/-- The actual lower recursive family is used by the child dispatcher. Its
native queries prove that this ISZERO reaches insertion without a grandchild. -/
theorem child_simplifier (safety : Bool) (depth : Nat) (publishOK : Bool := true) :
    (primitives safety depth childSource publishOK (child safety).address (child safety).native).simplify
      (child safety).key (child safety).normalized (child safety).taken.2.world = (.ok none, (child safety).taken.2.world) := by
  have facts := (child_established safety).taken.native (by rw [rows_count]; decide)
  simp only [primitives, NativeRecursion.dispatcher_snapshot]
  rw [facts.reads]
  exact iszero_miss (input := NativeRecursion.operand) (address := (child safety).normalized.address) _ _ _ (first_constant safety _ (child_established safety).taken).1
    (first_operation safety _ 21 (child_established safety).taken (by decide)).1
    (first_operation safety _ 24 (child_established safety).taken (by decide)).1
    (first_operation safety _ 3 (child_established safety).taken (by decide)).1

theorem child_result (safety : Bool) (depth : Nat) (after : Native.Frame Nat)
    (inserted : Native.insert ops ReachablePrefixTests.allocate safety 7 6 childSource (child safety).address Insertion.Tests.model
      (child safety).native (child safety).key (child safety).normalized true (some growth) (child safety).taken.2.world =
        (.ok 5, appendedWorld safety after)) (publishOK : Bool := true) :
    (children safety (depth + 1) publishOK).operation 21 [0] debug (parent safety).taken.2.world = (.ok 5, returnedChild safety after) := by
  have established := child_established safety
  have room : Interner.Queries.queries.atCapacity (child safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have routed := (child safety).route (primitives safety depth childSource publishOK) (calls_observed safety true) established.item.graph room rfl
  have continued : (child safety).continuation (primitives safety depth childSource publishOK (child safety).address (child safety).native) =
      (do handoff; graph (fun slice => Native.insert ops ReachablePrefixTests.allocate safety 7 6 childSource (child safety).address
        Insertion.Tests.model (child safety).native (child safety).key slice true (some growth)) : Action (Publication.Effects Nat) NodeId)
        (child safety).taken.2 := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (child safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      graph, established.entry.origin.scope, child_simplifier, bind, Effect.bind]
    rw [← established.entry.origin.scope]; rfl
  rw [continued] at routed
  have finished := established.entry.finish_native ops ReachablePrefixTests.allocate safety 7 6 childSource (child safety).address
    Insertion.Tests.model (child safety).request (child safety).request.arguments (child safety).native (child safety).key
    (child safety).normalized (child safety).lookup (child safety).constructed (child safety).taken.2 true (some growth)
  rw [inserted] at finished
  change (child safety).invoked (primitives safety depth childSource publishOK) =
    (let done := finishInsertion ops ReachablePrefixTests.allocate safety 7 6 childSource (child safety).address
      Insertion.Tests.model (child safety).native (child safety).key true (child safety).taken.2 (some growth)
     if ordinary done.1 then (done.1, (child safety).returned done.2) else done) at routed
  rw [finished] at routed
  have literal : Arguments.prepare [0] (parent safety).taken.2.world = (.ok childSource, (child safety).before) := by
    simpa only [child, childArguments] using
      (Prod.ext (literals_observed safety).2.2.1 rfl : childArguments safety = (.ok childSource, (childArguments safety).2))
  rw [children, NativeRecursion.operation_succ, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  change Arguments.returned [0] _ ((child safety).invoked (primitives safety depth childSource publishOK)) = _
  rw [routed]; rfl

/-- Nonempty relocation returns into a live parent frame. The old backing is
retired; the parent literal and normalized owner survive, and the final native
graph is reconstructed through both child locals and its outer literal cleanup. -/
theorem child_contract (safety : Bool) (depth : Nat) (publishOK : Bool := true) : ∃ after,
    (children safety (depth + 1) publishOK).operation 21 [0] debug (parent safety).taken.2.world = (.ok 5, returnedChild safety after) ∧
    GraphFacts safety (backing safety) 13 (returnedChild safety after) (appendedRows safety) ∧
    Held 7 rootSource [0, 4] (parent safety).normalized (returnedChild safety after) ∧
    (returnedChild safety after).memory.effects.keys = OwnedKeys.store (parent safety).taken.2.world.memory.effects.keys
      (child safety).key ⟨(child safety).normalized.address, 5⟩ ∧
    (∀ id native, (parent safety).taken.2.world.memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ ReachablePrefixTests.backing →
      (returnedChild safety after).memory.memory.heap.lookup id = some native) ∧
    (∀ id block, (parent safety).taken.2.world.memory.heap id = some block → id ≠ ReachablePrefixTests.backing →
      (returnedChild safety after).memory.heap id = some block) ∧
    (returnedChild safety after).memory.heap ReachablePrefixTests.backing = none ∧
    (returnedChild safety after).memory.memory.heap.lookup ReachablePrefixTests.backing = none ∧
    Caller.GraphCustody 7 (parent safety).normalized (appendedRows safety) (returnedChild safety after).memory ∧
    Caller.SourcePrivate rootSource (returnedChild safety after).memory.effects.keys ∧
    AssemblyClone.NativeFields.Represents (returnedChild safety after).memory.memory (parent safety).address (parent safety).native := by
  obtain ⟨after, inserted, facts, oldDead, nativeDead, keys, native, registry, _, _⟩ := child_native safety
  have established := child_established safety
  have literal := (child_literal safety).1
  have prior := (parent_established safety).taken
  have bounded : (appendedRows safety).length ≤ 13 := by simp only [appendedRows, List.length_append, List.length_singleton, rows_count]; decide
  have innerFacts := (facts.cleanup ((child safety).before.memory.memory.nextId + 1)
    (by rw [(prefix_geometry safety).1]; decide) (by rw [(prefix_geometry safety).1]; decide) bounded).cleanup
    (child safety).before.memory.memory.nextId (by rw [(prefix_geometry safety).1]; decide)
    (by rw [(prefix_geometry safety).1]; decide) bounded
  have returnedFacts := innerFacts.cleanup (parent safety).taken.2.world.memory.memory.nextId
    (by rw [(literals_observed safety).2.2.2]; decide) (by rw [(literals_observed safety).2.2.2]; decide) bounded
  have retained : ∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell → id ≠ 6 → id ≠ ReachablePrefixTests.backing →
      (appendedWorld safety after).memory.memory.heap.lookup id = some cell := by
    intro id cell found ownerApart backingApart
    exact native id cell (established.item.memory id cell (literal.frame id cell found)) ownerApart backingApart
      (by intro old impossible; rw [(prefix_keys safety).2.1] at impossible; cases impossible)
  have frame : ∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell → id ≠ 6 → id ≠ ReachablePrefixTests.backing →
      (returnedChild safety after).memory.memory.heap.lookup id = some cell := by
    intro id cell found ownerApart backingApart
    have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ prior.valid.memory found).1
    have childOlder : id < (child safety).before.memory.memory.nextId := by
      rw [(literals_observed safety).2.2.2] at older
      rw [(prefix_geometry safety).1]; omega
    exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id older).trans
      ((Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id childOlder).trans
        ((Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id (by omega)).trans
          (retained id cell found ownerApart backingApart)))
  have registered : ∀ id block, (parent safety).taken.2.world.memory.heap id = some block → id ≠ ReachablePrefixTests.backing →
      (returnedChild safety after).memory.heap id = some block := by
    intro id block found apart
    apply registry id block _ apart
      (by intro old impossible; rw [(prefix_keys safety).2.1] at impossible; cases impossible)
    rw [established.item.heap]
    change (childArguments safety).2.memory.heap id = _
    rw [literal.heap]; exact found
  have parentFrame := (parent_input safety).1
  have initialCall : NativeRecursion.CallFrame safety 7 6 (rows safety) rootSource [0, 4] (parent safety).normalized
      (parent safety).address (parent safety).native (fun _ => True) (parent safety).taken.2.world :=
    ⟨parentFrame, (parent_established safety).entry.item, trivial, parent_array safety⟩
  have reachedCall : NativeRecursion.CallFrame safety 7 6 (rows safety) rootSource [0, 4] (parent safety).normalized
      (parent safety).address (parent safety).native (fun _ => True) (appendedWorld safety after) := by
    have current := established.taken.native (by rw [rows_count]; decide)
    let stack : NativeRecursion.Enclosing (σ := Nat) safety 7 6
        (NativeRecursion.CallFrame safety 7 6 (rows safety) rootSource [0, 4] (parent safety).normalized
          (parent safety).address (parent safety).native (fun _ => True)) := .call .root
    obtain ⟨_, added, data, capacity, row, before, post⟩ := (child_entry safety).2.published_frame
      ops ReachablePrefixTests.allocate (some growth) Insertion.Tests.model (child safety).key
      (Normalization.Tests.external_admitted _) established.entry.publication.aligned
      (by rw [current.projected]; simp only [Option.getD_some, rows_count]; decide)
      (Or.inr (Or.inr (child_published safety)))
    have kept := stack.published (child_entry safety).1 (child_entry safety).2.parent established.entry.origin before post
    rw [inserted] at kept
    exact kept
  have reachedCustody : Caller.GraphCustody 7 (parent safety).normalized (appendedRows safety) (appendedWorld safety after).memory := by
    obtain ⟨added, data, capacity, reached, custody, _⟩ := reachedCall.1.1
    have same := Option.some.inj (reached.projected.symm.trans (facts.native bounded).projected)
    exact same ▸ custody
  have reachedPrivate : Caller.SourcePrivate rootSource (appendedWorld safety after).memory.effects.keys := by
    obtain ⟨_, _, _, _, _, privateSource⟩ := reachedCall.1.1
    exact privateSource
  have itemOrdered : (parent safety).taken.2.world.memory.memory.nextId ≤ (child safety).before.memory.memory.nextId := by
    rw [(literals_observed safety).2.2.2, (prefix_geometry safety).1]; decide
  have returnedCall := initialCall.locals (child safety).before.memory.memory.nextId
    ((child safety).before.memory.memory.nextId + 1) itemOrdered (Nat.le_trans itemOrdered (Nat.le_succ _))
    (fun _ _ => trivial) (appendedWorld safety after) reachedCall
  have returnedParent := initialCall.cleanup returnedCall (parent safety).taken.2.world.memory.memory.nextId (Nat.le_refl _) trivial
  refine ⟨after, child_result safety depth after inserted publishOK, returnedFacts, returnedParent.1.2, ?_, frame, registered, oldDead, ?_, ?_, reachedPrivate, returnedParent.2.1⟩
  · exact keys.trans (congrArg (fun table => OwnedKeys.store table (child safety).key ⟨(child safety).normalized.address, 5⟩) (prefix_keys safety).1)
  · apply cleanup_missing _ _ _ innerFacts.valid.memory
    apply cleanup_missing _ _ _ (facts.valid.cleanup _ ((child safety).before.memory.memory.nextId + 1)).memory
    exact cleanup_missing _ _ _ facts.valid.memory nativeDead
  · exact ⟨⟨reachedCustody.live, reachedCustody.apart⟩, reachedCustody.operands⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests
