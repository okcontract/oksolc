/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveNonemptyAllocationTests
import Compiler.Extraction.InternerRecursiveChildTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveNonemptyTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime growth GraphFacts)
open RecursiveTests (Call debug)

attribute [local irreducible] ready rootArguments childArguments

def noChildren : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)) where
  constant := fun _ _ world => (.error (.language .unsupported), world)
  operation := fun _ _ _ world => (.error (.language .unsupported), world)
  materialize := fun _ _ _ world => (.error (.language .unsupported), world)
  borrowedOperation := fun _ _ _ _ world => (.error (.language .unsupported), world)

def childSeed (source : View) : Primitives (Publication.Effects Nat) where
  simplify := fun key _ before => Dispatch.simplify (Interner.representativeReads before.graph)
    noChildren 64 key.instruction key.arguments debug before
  publish := Publication.publish ops.probe ops.arguments 7 source
  insert := fun _ _ _ before => (.error (.language .unsupported), before)
def childPrimitives (safety : Bool) (source : View) (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue) :=
  callerPrimitives ops failing safety 7 6 source address Insertion.Tests.model native (childSeed source) (some growth)
def childInner (safety : Bool) := operation (Publication.external ops.arguments) 160 7 (childPrimitives safety childSource)
  Interner.Queries.queries childSource 21 [0] debug (child safety).before
def childFull (safety : Bool) := Arguments.operation (Publication.external ops.arguments) 160 7 (childPrimitives safety)
  Interner.Queries.queries 21 [0] debug (parent safety).taken.2.world
def childReturned (safety : Bool) (after : Native.Frame Nat) :=
  let world := (child safety).returnedWorld (failedWorld safety after)
  let memory := Compiler.ZigAir.Memory.cleanup (parent safety).taken.2.world.memory.memory.nextId world.memory.memory
  { world with memory := { world.memory with memory } }

theorem iszero_miss (reads : Nested.Reads)
    (constructors : Associative.Constructors AssemblyItem.Fields.Values (GraphAction (Publication.Effects Nat)))
    (before : World (Publication.Effects Nat))
    (constant : reads.constant 0 = .ok none)
    (iszero : reads.operation 0 21 = .ok none) (xor : reads.operation 0 24 = .ok none) (sub : reads.operation 0 3 = .ok none)
    (input : Nested.OperandRead (GraphAction (Publication.Effects Nat)) := Nested.logicalOperand)
    (address : Nat := 0) :
    (Dispatch.simplifyWithInputs reads constructors 64 21 [0] debug input address) before = (.ok none, before) := by
  have collected : Dispatch.collectConstants reads [0] = .ok none := by
    unfold Dispatch.collectConstants; rw [constant]; rfl
  have first : (Dispatch.constantStage reads constructors 21 [0] debug) before = (.ok none, before) := by
    simp only [Dispatch.constantStage, collected]; rfl
  have unary : (Dispatch.unaryStageWithInputs reads constructors 21 0 debug input) before = (.ok none, before) := by
    simp only [Dispatch.unaryStageWithInputs, Dispatch.opNOT, Dispatch.opISZERO, Dispatch.opXOR, Dispatch.opSUB,
      BitVec.reduceBEq, Bool.false_eq_true, ↓reduceIte, iszero, xor, sub, Nested.readAction]
    rfl
  unfold Dispatch.simplifyWithInputs Dispatch.simplifyOptionsWithInputs
  simp only [Dispatch.orNext, bind, Effect.bind, first]
  exact (Effect.bind_success _ _ _ _ _ unary).trans rfl

theorem child_simplified (safety : Bool) : (childSeed childSource).simplify (child safety).key
    (child safety).normalized (child safety).taken.2.world = (.ok none, (child safety).taken.2.world) :=
  iszero_miss _ _ _ (first_constant safety _ (child_established safety).taken).1
    (first_operation safety _ 21 (child_established safety).taken (by decide)).1
    (first_operation safety _ 24 (child_established safety).taken (by decide)).1
    (first_operation safety _ 3 (child_established safety).taken (by decide)).1

theorem child_result (safety : Bool) (after : Native.Frame Nat)
    (ran : executed safety = ((.ok (some .allocationFailure), closed), after)) :
    childInner safety = (.error (.language .outOfMemory),
      ⟨(child safety).returnedWorld (failedWorld safety after), ⟨none, some (child safety).normalized, true⟩⟩) ∧
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
      childPrimitives, callerPrimitives, graph, established.entry.origin.scope, child_simplified,
      bind, Effect.bind]
    rw [← established.entry.origin.scope]
    rfl
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
  have literal : Arguments.prepare [0] (parent safety).taken.2.world = (.ok childSource, (child safety).before) := by
    simpa only [child, childArguments] using
      (Prod.ext (literals_observed safety).2.2.1 rfl : childArguments safety = (.ok childSource, (childArguments safety).2))
  rw [childFull, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ literal]
  change Arguments.returned [0] _ (childInner safety) = _
  rw [routed]
  rfl

theorem child_literal_stack (safety : Bool) : ∃ cell,
    (child safety).before.memory.memory.heap.lookup childSource.allocation = some cell ∧ cell.stack = true := by
  obtain ⟨cell, found, _, _, stack⟩ := (child_literal safety).1.storage (by decide)
  exact ⟨cell, found, stack⟩

/-- The nonempty child fails during native backing growth, releases its clone,
duplicate and normalized arguments, and returns through its unary literal.
Every parent allocation and registry owner is preserved by that execution. -/
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
    (childReturned safety after).memory.memory.heap.lookup childSource.allocation = none := by
  obtain ⟨after, ran, valid, _, _, keys, native, registry, dead⟩ := child_allocation safety
  have established := child_established safety
  have literal := (child_literal safety).1
  have parentFacts := (parent_established safety).taken
  have nativeBefore : ∀ id cell, (child safety).before.memory.memory.heap.lookup id = some cell →
      (failedWorld safety after).memory.memory.heap.lookup id = some cell := by
    intro id cell found; exact native id cell (established.item.memory id cell found)
  have innerFrame := (child safety).returned_frame (failedWorld safety after) literal.good.1 nativeBefore
  have innerValid := (child safety).returned_valid (failedWorld safety after) valid
  have frame : ∀ id cell, (parent safety).taken.2.world.memory.memory.heap.lookup id = some cell →
      (childReturned safety after).memory.memory.heap.lookup id = some cell := by
    intro id cell found
    exact (Compiler.ZigAir.Memory.cleanup_lookup_older _ _ id
      (Compiler.ZigAir.Memory.valid_lookup _ _ _ parentFacts.valid.memory found).1).trans
      (innerFrame id cell (literal.frame id cell found))
  have registered : ∀ id block, (parent safety).taken.2.world.memory.heap id = some block →
      (childReturned safety after).memory.heap id = some block := by
    intro id block found
    apply registry id block
    rw [established.item.heap]
    change (childArguments safety).2.memory.heap id = _
    rw [literal.heap]; exact found
  have reachedValid : Valid (childReturned safety after).memory := innerValid.cleanup _ _
  have graph : (childReturned safety after).graph = (parent safety).taken.2.world.graph :=
    established.entry.origin.graph.trans (established.item.graph.trans literal.graph)
  have keys := keys.trans ((congrArg Publication.Effects.keys established.item.effects).trans (congrArg Publication.Effects.keys literal.effects))
  refine ⟨after, (child_result safety after ran).2,
    parentFacts.frame (by rw [rows_count]; decide) reachedValid
      ((congrArg Interner.Heap.representatives graph).trans parentFacts.projected) (congrArg Interner.Heap.table graph) keys frame registered,
    graph, keys, frame, registered, ?_, ?_⟩
  · intro id selected
    refine ⟨(dead id selected).1, ?_⟩
    apply RecursiveTests.cleanup_missing _ _ _ innerValid.memory
    apply RecursiveTests.cleanup_missing _ _ _ (valid.cleanup _ ((child safety).before.memory.memory.nextId + 1)).memory
    exact RecursiveTests.cleanup_missing _ _ _ valid.memory (dead id selected).2
  · obtain ⟨cell, found, _⟩ := child_literal_stack safety
    exact literal.retire [0] _ _ childSource (by decide) _ innerValid.memory
      ((innerFrame _ _ found).trans found.symm)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveNonemptyTests
