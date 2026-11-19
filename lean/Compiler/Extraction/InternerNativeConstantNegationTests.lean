/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantNegationDispatchTests
import Compiler.Extraction.InternerRecursiveCallFailureTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.NegateConstantTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)
open RecursiveTests (Call debug)
open ConstantNegationTests
open ConstantTests (children primitives prefix_result)

attribute [local irreducible] ConstantPublicationTests.ready rootArguments Call.constructed Call.stack

theorem child_equivalent (safety : Bool) (depth : Nat) (value : Word) (apart : 0 - value ≠ value) :
    (children safety (depth + 1)).constant (0 - value) debug (parent safety value).taken.2.world =
      ((childFull safety value).1, (childFull safety value).2.world) := by
  have current := child_established safety value apart
  have room : Interner.Queries.queries.atCapacity (child safety value).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected, ConstantPublicationTests.rows_count]; decide
  have continuation :
      (child safety value).continuation (primitives safety depth ⟨0, 0, 0⟩ (child safety value).address (child safety value).native) =
      (child safety value).continuation (childPrimitives safety (child safety value).address (child safety value).native) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (child safety value).request.item.kind = 2 from rfl, BitVec.reduceBEq, Bool.false_eq_true,
      Bool.true_and, ↓reduceIte, handoff, graph, current.entry.origin.scope, bind, Effect.bind, pure, Effect.pure]
    rfl
  have same := NativeRecursion.Tests.same_call (child safety value) (primitives safety depth ⟨0, 0, 0⟩)
    (childPrimitives safety) (child_observed safety value apart) current.item.graph room rfl continuation
  rw [children, constant_succ]
  exact congrArg (fun result => (result.1, result.2.world)) same

theorem parent_simplified (safety : Bool) (depth : Nat) (value : Word) (apart : 0 - value ≠ value) (after : Native.Frame Nat)
    (called : childFull safety value = (.error (.language .outOfMemory),
      ⟨childReturned safety value after, ⟨none, some (child safety value).normalized, true⟩⟩)) :
    (primitives safety (depth + 1) (parent safety value).source (parent safety value).address (parent safety value).native).simplify
      (parent safety value).key (parent safety value).normalized (parent safety value).taken.2.world =
      (.error (.language .outOfMemory), childReturned safety value after) := by
  have current := (established safety value).taken
  have facts := current.native (by rw [ConstantPublicationTests.rows_count]; decide)
  simp only [primitives, NativeRecursion.dispatcher_snapshot]
  rw [facts.reads]
  have nonzero : value ≠ 0 := by intro zero; subst value; exact apart (by decide)
  apply negate_failure (input := NativeRecursion.operand)
    (address := (parent safety value).normalized.address) _ _ value _ _ _ nonzero
    (ConstantPublicationTests.first_read safety value _ current).1
    (ConstantPublicationTests.value_read safety value _ current).1
    (by simp only [Interner.representativeReads, current.projected, Nested.storageReads])
  rw [child_equivalent safety depth value apart]
  exact congrArg (fun result => (result.1, result.2.world)) called

def inner (safety : Bool) (depth : Nat) (value : Word) :=
  (parent safety value).invoked (primitives safety depth (parent safety value).source)
def root (safety : Bool) (depth : Nat) (value : Word) :=
  (children safety depth).operation 3 [0, 4] debug (old safety value)

/-- The native constant child fails growth and returns through the parent's
owned argument and constructor frames. Every pre-parent allocation survives. -/
theorem inner_contract (safety : Bool) (depth : Nat) (value : Word) (apart : 0 - value ≠ value) : ∃ after cleaned,
    childFull safety value = (.error (.language .outOfMemory),
      ⟨childReturned safety value after, ⟨none, some (child safety value).normalized, true⟩⟩) ∧
    Held 7 (parent safety value).source [0, 4] (parent safety value).normalized (childReturned safety value after) ∧
    free (Publication.external ops.arguments) 7 (parent safety value).normalized (childReturned safety value after).memory =
      (.ok (), cleaned.world.memory) ∧
    inner safety (depth + 1) value = (.error (.language .outOfMemory), (parent safety value).returned cleaned) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (inner safety (depth + 1) value).2.world (ConstantPublicationTests.rows safety value) ∧
    (inner safety (depth + 1) value).2.world.graph = (parent safety value).before.graph ∧
    Closed (inner safety (depth + 1) value).2.scope ∧
    Consumed (parent safety value).normalized (inner safety (depth + 1) value).2.world.memory ∧
    (inner safety (depth + 1) value).2.world.memory.effects.allocator =
      (childReturned safety value after).memory.effects.allocator + 102 ∧
    (∀ id cell, (parent safety value).before.memory.memory.heap.lookup id = some cell →
      (inner safety (depth + 1) value).2.world.memory.memory.heap.lookup id = some cell) ∧
    (inner safety (depth + 1) value).2.world.memory.effects.keys = (parent safety value).before.memory.effects.keys ∧
    (∀ id block, (parent safety value).before.memory.heap id = some block →
      (inner safety (depth + 1) value).2.world.memory.heap id = some block) := by
  obtain ⟨after, called, facts, keys, native, registry⟩ := child_contract safety value apart
  have current := established safety value
  have bounded : (ConstantPublicationTests.rows safety value).length ≤ 5 := by rw [ConstantPublicationTests.rows_count]; decide
  have room : Interner.Queries.queries.atCapacity (parent safety value).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected, ConstantPublicationTests.rows_count]; decide
  have graph : (childReturned safety value after).graph = (parent safety value).taken.2.world.graph :=
    (child_established safety value apart).entry.origin.graph.trans (child_established safety value apart).item.graph
  obtain ⟨cleaned, held, freed, result, finalFacts, finalGraph, closed, consumed, effects, frame, finalKeys, registered⟩ :=
    (parent safety value).simplifier_oom (primitives safety (depth + 1) (parent safety value).source)
      safety ReachablePrefixTests.backing 5 (ConstantPublicationTests.rows safety value)
      (literal safety value).2.2.1 bounded current (observed safety value) room rfl rfl _
      (parent_simplified safety depth value apart after called) facts.valid graph keys native registry
  change inner safety (depth + 1) value = _ at result
  refine ⟨after, cleaned, called, held, freed, result, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [result]; exact finalFacts
  · rw [result]; exact finalGraph
  · rw [result]; exact closed
  · rw [result]; exact consumed
  · rw [result]; exact congrArg Publication.Effects.allocator effects
  · rw [result]; exact frame
  · rw [result]; exact finalKeys
  · rw [result]; exact registered

theorem root_route (safety : Bool) (depth : Nat) (value : Word) : root safety (depth + 1) value =
    TemporaryArguments.unwind (old safety value).memory.memory.nextId (inner safety depth value) := by
  have prepared : Arguments.prepare [0, 4] (old safety value) = (.ok (rootSource safety value), (parent safety value).before) := by
    simpa only [rootArguments] using (literal safety value).1
  rw [root, children, operation_succ, Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ prepared]
  exact Arguments.returned_nonempty [0, 4] _ _ rfl

theorem root_contract (safety : Bool) (depth : Nat) (value : Word) (apart : 0 - value ≠ value) :
    (root safety (depth + 2) value).1 = .error (.language .outOfMemory) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (root safety (depth + 2) value).2 (ConstantPublicationTests.rows safety value) ∧
    (root safety (depth + 2) value).2.graph = (old safety value).graph ∧
    (root safety (depth + 2) value).2.memory.memory.heap.lookup (rootSource safety value).allocation = none ∧
    (root safety (depth + 2) value).2.memory.memory.nextId = (inner safety (depth + 1) value).2.world.memory.memory.nextId ∧
    (root safety (depth + 2) value).2.memory.memory.nextAddress = (inner safety (depth + 1) value).2.world.memory.memory.nextAddress ∧
    (∀ id cell, (old safety value).memory.memory.heap.lookup id = some cell →
      (root safety (depth + 2) value).2.memory.memory.heap.lookup id = some cell) := by
  obtain ⟨_, _, _, _, _, result, facts, graph, _, _, _, native, _, _⟩ := inner_contract safety depth value apart
  have prepared := (literal safety value).2.1
  have prior := (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.1
  have failed : (inner safety (depth + 1) value).1 = .error (.language .outOfMemory) := congrArg Prod.fst result
  have ordinary : ordinary (inner safety (depth + 1) value).1 = true := by rw [failed]; rfl
  have returned := BinaryPreludeTests.literal_return_facts safety ReachablePrefixTests.backing 5 _ [0, 4]
    (old safety value) (parent safety value).before (rootSource safety value) (inner safety (depth + 1) value)
    prior prepared (by decide) facts (by rw [ConstantPublicationTests.rows_count]; decide) native ordinary
  have kept := TemporaryArguments.unwind_keeps_reached (old safety value).memory.memory.nextId (inner safety (depth + 1) value)
  rw [show depth + 2 = (depth + 1) + 1 from rfl, root_route]
  exact ⟨failed, returned.1, kept.2.1.trans (graph.trans prepared.graph), returned.2.1,
    kept.2.2.2.1, kept.2.2.2.2, returned.2.2⟩

/-- Use the actual identifier returned by arbitrary-word publication as the
literal operand of the next native constructor in the same family. -/
def program (safety : Bool) (depth : Nat) (value : Word) : Except Fault NodeId × World (Publication.Effects Nat) :=
  (do let _ ← ReachablePrefixTests.sequence (children safety depth) 3
      let id ← (children safety depth).constant value debug
      (children safety depth).operation 3 [0, id] debug) (CallerInputTests.world safety)

theorem program_equivalent (safety : Bool) (depth : Nat) (value : Word) :
    program safety (depth + 1) value = root safety (depth + 1) value :=
  (Effect.bind_success _ _ _ _ _ (prefix_result safety depth 3 (by decide))).trans
    (Effect.bind_success _ _ _ _ _ (WordConstantTests.constant_equivalent safety depth value))

/-- Native initialization, arbitrary-word publication, constant negation,
the actual failing child and every enclosing return form one execution. The
published word survives; this branch does not establish general RC induction. -/
theorem program_contract (safety : Bool) (depth : Nat) (value : Word) (apart : 0 - value ≠ value) :
    (program safety (depth + 2) value).1 = .error (.language .outOfMemory) ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5
      (program safety (depth + 2) value).2 (ConstantPublicationTests.rows safety value) ∧
    Constant.value (program safety (depth + 2) value).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 =
      .ok (.ok (some value)) ∧
    (program safety (depth + 2) value).2.graph = (old safety value).graph ∧
    (program safety (depth + 2) value).2.memory.memory.heap.lookup (rootSource safety value).allocation = none ∧
    (∀ id cell, (old safety value).memory.memory.heap.lookup id = some cell →
      (program safety (depth + 2) value).2.memory.memory.heap.lookup id = some cell) := by
  rw [show depth + 2 = (depth + 1) + 1 from rfl, program_equivalent]
  have result := root_contract safety depth value apart
  exact ⟨result.1, result.2.1.native (by rw [ConstantPublicationTests.rows_count]; decide),
    (ConstantPublicationTests.value_read safety value _ result.2.1).2, result.2.2.1, result.2.2.2.1, result.2.2.2.2.2.2⟩

theorem root_one (safety : Bool) (value : Word) (apart : 0 - value ≠ value) : root safety 1 value =
    (.error (.language .unsupported), (parent safety value).taken.2.world) := by
  have current := established safety value
  have room : Interner.Queries.queries.atCapacity (parent safety value).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected, ConstantPublicationTests.rows_count]; decide
  have simplified : (primitives safety 0 (parent safety value).source (parent safety value).address (parent safety value).native).simplify
      (parent safety value).key (parent safety value).normalized (parent safety value).taken.2.world =
        (.error (.language .unsupported), (parent safety value).taken.2.world) := by
    have facts := current.taken.native (by rw [ConstantPublicationTests.rows_count]; decide)
    simp only [primitives, NativeRecursion.dispatcher_snapshot]
    rw [facts.reads]
    have nonzero : value ≠ 0 := by intro zero; subst value; exact apart (by decide)
    exact negate_failure (input := NativeRecursion.operand) (address := (parent safety value).normalized.address)
      _ _ value _ _ _ nonzero (ConstantPublicationTests.first_read safety value _ current.taken).1
      (ConstantPublicationTests.value_read safety value _ current.taken).1
      (by simp only [Interner.representativeReads, current.taken.projected, Nested.storageReads]) rfl
  have continuation := (parent safety value).simplify_error _ _ _ rfl current.entry.origin.scope simplified
  have routed := (parent safety value).route (primitives safety 0 (parent safety value).source)
    (observed safety value) current.item.graph room rfl
  rw [continuation] at routed
  have result : inner safety 0 value = (.error (.language .unsupported), (parent safety value).taken.2) := routed
  rw [show 1 = 0 + 1 from rfl, root_route, result]
  rfl

theorem program_one (safety : Bool) (value : Word) (apart : 0 - value ≠ value) : program safety 1 value =
    (.error (.language .unsupported), (parent safety value).taken.2.world) :=
  (program_equivalent safety 0 value).trans (root_one safety value apart)

theorem exhaustion_retained (safety : Bool) (value : Word) (apart : 0 - value ≠ value) :
    ordinary (program safety 1 value).1 = false ∧
    Held 7 (parent safety value).source [0, 4] (parent safety value).normalized (program safety 1 value).2 ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5
      (program safety 1 value).2 (ConstantPublicationTests.rows safety value) ∧
    Constant.value (program safety 1 value).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok (some value)) := by
  rw [program_one safety value apart]
  have current := established safety value
  exact ⟨rfl, current.entry.origin.held, current.taken.native (by rw [ConstantPublicationTests.rows_count]; decide),
    (ConstantPublicationTests.value_read safety value _ current.taken).2⟩

theorem program_zero (safety : Bool) (value : Word) : program safety 0 value =
    (.error (.language .unsupported), CallerInputTests.world safety) := rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.NegateConstantTests
