/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeLocalReturnTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (lifetime GraphFacts)
open RecursiveTests (Call debug)
open RecursiveBorrowedTests (childContext)

theorem first_publication (safety : Bool) (depth : Nat) :
    (NativeRecursion.unfold (childContext safety) 6 64 (depth + 1)).operation 22 [0, 1] debug
      (BinaryPreludeTests.initial safety) = (.ok 4, BinaryPreludeTests.ready safety false) :=
  (NativeRecursion.Tests.binary_equivalent safety false depth).trans
    (Prod.ext (BinaryPreludeTests.contract safety false).1 rfl)

theorem observed_route (safety : Bool) : observed safety = rootWith safety NativeRecursion.exhausted :=
  (Effect.bind_success _ _ _ _ _ (NativeRecursion.Tests.prefix_result safety 1 3 (by decide))).trans
    (Effect.bind_success _ _ _ _ _ (first_publication safety 1))

def resultObservations (safety : Bool) (ran : Except Fault NodeId × World (Publication.Effects Nat)) :=
  (ran.1, ran.2.memory.memory.heap.lookup rootSource.allocation,
    ran.2.memory.memory.heap.lookup localSource.allocation, ran.2.graph.read,
    Operation.run ran.2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 22,
    ran.2.memory.effects.keys (parent safety).key)

section
attribute [local irreducible] BinaryPreludeTests.ready rootArguments copied localReturned

/-- Derive the former final observations from the actual child frame, parent
publication and cleanup. The published lifetime follows from root preparation;
native operation reads follow from the reached graph correspondence. -/
theorem result_observed (safety : Bool) :
    resultObservations safety (reduced safety) =
      (.ok 4, none, none, (BinaryPreludeTests.ready safety false).graph.read,
        .ok (.ok (some (Operation.returned BinaryPreludeTests.operands))), some ⟨30, 4⟩) := by
  obtain ⟨facts, rootGone, localGone, words, keys⟩ := reduced_native safety
  have prior := (parent_established safety).taken.native (by rw [BinaryPreludeTests.rows_count]; decide)
  have operation := (facts.operations 4 22).trans ((prior.operations 4 22).symm.trans (local_input safety 0).2.2.2.1)
  have source := congrArg View.allocation (root_prepared safety).address
  change rootSource.allocation = (BinaryPreludeTests.ready safety false).memory.memory.nextId at source
  have mark : (BinaryPreludeTests.ready safety false).memory.memory.nextId = 27 := source.symm
  have address : (parent safety).normalized.address = 30 := by
    change (parent safety).before.memory.memory.nextId + 2 = 30
    rw [(root_prepared safety).counter, mark]; rfl
  have installed : (reduced safety).2.memory.effects.keys (parent safety).key = some ⟨30, 4⟩ := by
    rw [keys, OwnedKeys.store, if_pos rfl, address]
  simp only [resultObservations, Prod.mk.injEq]
  exact ⟨congrArg Prod.fst (reduced_result safety), rootGone, localGone, words, operation, installed⟩

end

theorem completed (safety : Bool) :
    (observed safety).1 = .ok 4 ∧
    (observed safety).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (observed safety).2.memory.memory.heap.lookup localSource.allocation = none ∧
    (observed safety).2.graph.read = (BinaryPreludeTests.ready safety false).graph.read ∧
    Operation.run (observed safety).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 22 =
      .ok (.ok (some (Operation.returned BinaryPreludeTests.operands))) ∧
    (observed safety).2.memory.effects.keys (parent safety).key = some ⟨30, 4⟩ := by
  rw [observed_route, root_route]
  simpa only [resultObservations, Prod.mk.injEq] using result_observed safety

/-- The actual local child is a cache hit, so its lower recursive callbacks are
never visited. This equality quantifies over arbitrary callbacks, not a chosen
observation limit. -/
theorem root_independent (safety : Bool) :
    (fun children => rootWith safety children) = (fun _ => rootWith safety NativeRecursion.exhausted) := by
  funext children
  rw [root_route, root_route]

theorem program_equivalent (safety : Bool) (depth : Nat) : program safety (depth + 2) = observed safety := by
  have current : program safety (depth + 2) =
      (NativeRecursion.unfold (childContext safety) 6 64 (depth + 2)).operation 22 [0, 4] debug
        (BinaryPreludeTests.ready safety false) :=
      (Effect.bind_success _ _ _ _ _ (NativeRecursion.Tests.prefix_result safety (depth + 1) 3 (by decide))).trans
        (Effect.bind_success _ _ _ _ _ (first_publication safety (depth + 1)))
  rw [current, observed_route]
  exact congrFun (root_independent safety) (NativeRecursion.unfold (childContext safety) 6 64 depth)

/-- Publication, the real named-local child, parent publication and both outer
cleanups compose at every sufficient depth. Graph input facts are derived from
the same publication and constructor prefixes. -/
theorem program_contract (safety : Bool) (depth : Nat) :
    (program safety (depth + 2)).1 = .ok 4 ∧
    (program safety (depth + 2)).2.memory.memory.heap.lookup rootSource.allocation = none ∧
    (program safety (depth + 2)).2.memory.memory.heap.lookup localSource.allocation = none ∧
    (program safety (depth + 2)).2.graph.read = (BinaryPreludeTests.ready safety false).graph.read ∧
    Operation.run (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 22 =
      .ok (.ok (some (Operation.returned BinaryPreludeTests.operands))) ∧
    (program safety (depth + 2)).2.memory.effects.keys (parent safety).key = some ⟨30, 4⟩ ∧
    Arguments.Prepared [0, 1] (parent safety).taken.2.world localSource (copied safety).2 ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (copied safety).2 (BinaryPreludeTests.rows safety false) ∧
    ShiftInput.operand (view BinaryPreludeTests.operands) 1 (parent safety).taken.2.world = (.ok 1, (parent safety).taken.2.world) ∧
    ShiftInput.operand (view BinaryPreludeTests.operands) 0 (parent safety).taken.2.world = (.ok 0, (parent safety).taken.2.world) ∧
    (∀ id opcode, Operation.run (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode =
      .ok (((parentReads safety).operation id opcode).map (Option.map Operation.returned))) ∧
    (∀ id, id = 0 ∨ id = 4 → Constant.value (parent safety).taken.2.world.memory.memory
      (Owner.headerAddress ⟨6, 0⟩) id = .ok (.ok none)) ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (program safety (depth + 2)).2 (BinaryPreludeTests.rows safety false) := by
  rw [program_equivalent]
  obtain ⟨result, rootGone, localGone, words, operation, published⟩ := completed safety
  have input := local_input safety depth
  refine ⟨result, rootGone, localGone, words, operation, published, input.1, input.2.1,
    input.2.2.2.2.1, input.2.2.2.2.2, operation_agreement safety,
    fun id selected => (constant_guards safety id selected).2, ?_⟩
  rw [observed_route, root_route]
  exact (reduced_native safety).1

theorem root_one (safety : Bool) :
    (NativeRecursion.unfold (childContext safety) 6 64 1).operation 22 [0, 4] debug
      (BinaryPreludeTests.ready safety false) =
        (.error (.language .unsupported), (parent safety).taken.2.world) := by
  have scope := (parent_established safety).entry.origin.scope
  have guards := operation_guards safety
  have simplified : (parentPrimitives safety NativeRecursion.exhausted (parent safety).address (parent safety).native).simplify
      (parent safety).key (parent safety).normalized (parent safety).taken.2.world =
        (.error (.language .unsupported), (parent safety).taken.2.world) := by
    have facts := (parent_established safety).taken.native (by rw [BinaryPreludeTests.rows_count]; decide)
    simp only [parentPrimitives, NativeRecursion.dispatcher_snapshot]
    rw [facts.reads]
    exact dispatch_route (input := NativeRecursion.operand) (address := (parent safety).normalized.address) (parentReads safety) NativeRecursion.exhausted (parent safety).taken.2.world
      (constant_guards safety 0 (Or.inl rfl)).1 (constant_guards safety 4 (Or.inr rfl)).1
      guards.1 guards.2.1 guards.2.2.1 guards.2.2.2.1 guards.2.2.2.2 (source_query safety).1
      (by simp only [parentReads, Interner.representativeReads, (parent_established safety).taken.projected, Nested.storageReads])
      (.error (.language .unsupported)) (parent safety).taken.2.world rfl
  have continuation : (parent safety).continuation
      (parentPrimitives safety NativeRecursion.exhausted (parent safety).address (parent safety).native) =
        (.error (.language .unsupported), (parent safety).taken.2) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (parent safety).request.item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte,
      graph, scope, simplified, bind, Effect.bind]
    rw [← scope]
  have routed := (parent safety).route (parentPrimitives safety NativeRecursion.exhausted)
    (parent_observed safety).2.1 (parent_established safety).item.graph (parent_room safety) rfl
  rw [continuation] at routed
  have result : (parent safety).invoked (parentPrimitives safety NativeRecursion.exhausted) =
      (.error (.language .unsupported), (parent safety).taken.2) := routed
  rw [show 1 = 0 + 1 from rfl, NativeRecursion.operation_succ,
    Arguments.operation_prepared _ _ _ _ _ _ _ _ _ _ _ (root_literal safety)]
  change Arguments.returned [0, 4] _ ((parent safety).invoked (parentPrimitives safety NativeRecursion.exhausted)) = _
  rw [result]; rfl

theorem program_one (safety : Bool) : program safety 1 =
    (.error (.language .unsupported), (parent safety).taken.2.world) := by
  have first : program safety 1 =
      (NativeRecursion.unfold (childContext safety) 6 64 1).operation 22 [0, 4] debug
        (BinaryPreludeTests.ready safety false) :=
      (Effect.bind_success _ _ _ _ _ (NativeRecursion.Tests.prefix_result safety 0 3 (by decide))).trans
        (Effect.bind_success _ _ _ _ _ (first_publication safety 0))
  exact first.trans (root_one safety)

theorem exhaustion_retained (safety : Bool) :
    ordinary (program safety 1).1 = false ∧
    Held 7 rootSource [0, 4] (parent safety).normalized (program safety 1).2 ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (program safety 1).2 (BinaryPreludeTests.rows safety false) := by
  rw [program_one]
  exact ⟨rfl, (parent_established safety).entry.origin.held, (parent_established safety).taken⟩

theorem program_zero (safety : Bool) : program safety 0 =
    (.error (.language .unsupported), CallerInputTests.world safety) := by rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests
