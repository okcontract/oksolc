/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveBorrowedAllocationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveBorrowedTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime growth GraphFacts)
open RecursiveTests (Call debug cleanup_missing)

attribute [local irreducible] ready rootArguments

def childSeed (source : View) := RecursiveNonemptyTests.childSeed source
def childPrimitives (safety : Bool) (source : View) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue) :=
  callerPrimitives ops failing safety 7 6 source address Insertion.Tests.model native (childSeed source) (some growth)
def childContext (safety : Bool) : PairInput.Context (Publication.Effects Nat) :=
  ⟨Publication.external ops.arguments, 160, 7, childPrimitives safety, Interner.Queries.queries⟩
def childInner (safety : Bool) := operation (Publication.external ops.arguments) 160 7 (childPrimitives safety childSource)
  Interner.Queries.queries childSource 20 [0, 1] debug (child safety).before
def childFull (safety : Bool) := ViewInput.operation (childContext safety) childSource 20 [0, 1] debug (child safety).before
def childReturned (safety : Bool) (after : Native.Frame Nat) := (child safety).returnedWorld (failedWorld safety after)

theorem eq_miss (reads : Nested.Reads)
    (constructors : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)))
    (before : World (Publication.Effects Nat))
    (left : reads.constant 0 = .ok none) (right : reads.constant 1 = .ok none)
    (equality : reads.overrideEquality = none)
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat)) := Nested.logicalOperand)
    (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads constructors 64 20 [0, 1] debug input address) before = (.ok none, before) := by
  have collected : Dispatch.collectConstants reads [0, 1] = .ok none := by
    unfold Dispatch.collectConstants; rw [left]; rfl
  have first : (Dispatch.constantStage reads constructors 20 [0, 1] debug) before = (.ok none, before) := by
    simp only [Dispatch.constantStage, collected]; rfl
  have binary : (Dispatch.binaryStageWithInputs reads constructors 64 20 0 1 debug Dispatch.defaultOptions input) before = (.ok none, before) := by
    have different : Nested.sameExpression reads 0 1 = false := by
      simp only [Nested.sameExpression, equality]; rfl
    unfold Dispatch.binaryStageWithInputs
    simp (config := { zeta := false }) only [left, right, different]
    rfl
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  simp only [Dispatch.orNext, bind, Effect.bind, first, binary]
  rfl

theorem child_simplified (safety : Bool) : (childSeed childSource).simplify (child safety).key
    (child safety).normalized (child safety).taken.2.world = (.ok none, (child safety).taken.2.world) := by
  apply eq_miss _ _ _
  · exact (constants safety _ (child_established safety).taken 0 (Or.inl rfl)).1
  · exact (constants safety _ (child_established safety).taken 1 (Or.inr (Or.inl rfl))).1
  · simp only [Interner.representativeReads, (child_established safety).taken.projected, Nested.storageReads]

theorem child_result (safety : Bool) (after : Native.Frame Nat)
    (ran : executed safety = ((.ok (some .allocationFailure), closed), after)) :
    childInner safety = (.error (.language .outOfMemory),
      ⟨childReturned safety after, ⟨none, some (child safety).normalized, true⟩⟩) ∧
    childFull safety = (.error (.language .outOfMemory), childReturned safety after) := by
  have established := child_established safety
  have room : Interner.Queries.queries.atCapacity (child safety).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ established.constructed.projected, rows_count]; decide
  have routed := (child safety).route (childPrimitives safety childSource) (calls_observed safety true) established.item.graph room rfl
  have continued : (child safety).continuation (childPrimitives safety childSource (child safety).address (child safety).native) =
      (do handoff; graph (fun slice => Native.insert ops failing safety 7 6 childSource (child safety).address Insertion.Tests.model
        (child safety).native (child safety).key slice true (some growth)) : Action (Publication.Effects Nat) NodeId) (child safety).taken.2 := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (child safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      childPrimitives, callerPrimitives, graph, established.entry.origin.scope, child_simplified, bind, Effect.bind]
    rw [← established.entry.origin.scope]; rfl
  rw [continued] at routed
  have finished := established.entry.finish_native ops failing safety 7 6 childSource (child safety).address
    Insertion.Tests.model (child safety).request (child safety).request.arguments (child safety).native (child safety).key
    (child safety).normalized (child safety).lookup (child safety).constructed (child safety).taken.2 true (some growth)
  have inserted := child_insert safety after ran
  change Native.insert ops failing safety 7 6 childSource (child safety).address Insertion.Tests.model
    (child safety).native (child safety).key (child safety).normalized true (some growth) (child safety).taken.2.world = _ at inserted
  rw [inserted] at finished
  change childInner safety =
    (let done := finishInsertion ops failing safety 7 6 childSource (child safety).address
      Insertion.Tests.model (child safety).native (child safety).key true (child safety).taken.2 (some growth)
     if ordinary done.1 then (done.1, (child safety).returned done.2) else done) at routed
  rw [finished] at routed
  refine ⟨routed, ?_⟩
  change (let result := childInner safety; (result.1, result.2.world)) = _
  rw [routed]
  rfl

/-- The actual borrowed EQ constructor grows the nonempty representative
container, receives OOM, releases both new argument owners and its item, and
unwinds only its own frames. The parent's graph operand view stays live. -/
theorem child_contract (safety : Bool) : ∃ after,
    childFull safety = (.error (.language .outOfMemory), childReturned safety after) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (childReturned safety after) (rows safety) ∧
    (childReturned safety after).graph = (parent safety).taken.2.world.graph ∧
    (childReturned safety after).memory.effects.keys = (parent safety).taken.2.world.memory.effects.keys ∧
    (∀ id native, (parent safety).taken.2.world.memory.memory.heap.lookup id = some native →
      (childReturned safety after).memory.memory.heap.lookup id = some native) ∧
    (∀ id block, (parent safety).taken.2.world.memory.heap id = some block →
      (childReturned safety after).memory.heap id = some block) ∧
    (∀ id, id = childObject safety ∨ id = (childOperands safety).address ∨ id = (child safety).normalized.address →
      (childReturned safety after).memory.heap id = none ∧ (childReturned safety after).memory.memory.heap.lookup id = none) ∧
    Good childSource [0, 1] (childReturned safety after) := by
  obtain ⟨after, ran, valid, _, _, keys, native, registry, dead⟩ := child_allocation safety
  have established := child_established safety
  have parentFacts := (parent_established safety).taken
  have nativeBefore : ∀ id cell, (child safety).before.memory.memory.heap.lookup id = some cell →
      (failedWorld safety after).memory.memory.heap.lookup id = some cell := by
    intro id cell found; exact native id cell (established.item.memory id cell found)
  have frame := (child safety).returned_frame (failedWorld safety after) parentFacts.valid nativeBefore
  have reachedValid := (child safety).returned_valid (failedWorld safety after) valid
  have registered : ∀ id block, (child safety).before.memory.heap id = some block →
      (childReturned safety after).memory.heap id = some block := by
    intro id block found; apply registry id block; rw [established.item.heap]; exact found
  have graph : (childReturned safety after).graph = (parent safety).taken.2.world.graph :=
    established.entry.origin.graph.trans established.item.graph
  have keys := keys.trans (congrArg Publication.Effects.keys established.item.effects)
  refine ⟨after, (child_result safety after ran).2,
    parentFacts.frame (by rw [rows_count]; decide) reachedValid
      ((congrArg Interner.Heap.representatives graph).trans parentFacts.projected) (congrArg Interner.Heap.table graph) keys frame registered,
    graph, keys, frame, registered, ?_, good_frame _ _ _ _ (child_input safety).2.1 reachedValid frame⟩
  intro id selected
  refine ⟨(dead id selected).1, ?_⟩
  apply cleanup_missing _ _ _ (valid.cleanup _ ((child safety).before.memory.memory.nextId + 1)).memory
  exact cleanup_missing _ _ _ valid.memory (dead id selected).2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveBorrowedTests
