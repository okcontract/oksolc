/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveNonemptyTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.AlgebraicInput.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime GraphFacts)
open RecursiveTests (debug)
open RecursiveNonemptyTests

attribute [local irreducible] ready rootArguments childArguments Arguments.operation ConstructorItem.constant

/-- Both boolean source branches execute the established nonempty child. Its
ordinary OOM stops the second literal before allocation; no abstract callback
result or live-parent conclusion is supplied to this endpoint. -/
theorem actual_boolean_failure (safety right : Bool) : ∃ after,
    run (childContext safety) (if right then .bool_right else .bool_left)
      (if right then 4 else 0) (if right then 0 else 4) debug (parent safety).taken.2.world =
        (.error (.language .outOfMemory), childReturned safety after) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (childReturned safety after) (rows safety) ∧
    Held 7 rootSource [0, 4] (parent safety).normalized (childReturned safety after) ∧
    (childReturned safety after).memory.memory.heap.lookup childSource.allocation = none ∧
    (∀ id native, (parent safety).taken.2.world.memory.memory.heap.lookup id = some native →
      (childReturned safety after).memory.memory.heap.lookup id = some native) := by
  obtain ⟨after, called, facts, _, _, native, registry, _, dead⟩ := child_contract safety
  refine ⟨after, ?_, facts, held_after_child safety _ facts.valid native registry, dead, native⟩
  apply boolean_error _ _ _ _ _ (by cases right <;> simp) _ _ _
  cases right <;> exact called

/-- The constant call below is the same complete successful publication used
to establish the fifth row of the recursive fixture. The other constructors
are still full native calls; this scoped check stops at their input boundary. -/
def publishing (safety : Bool) : Context (Publication.Effects Nat) :=
  ⟨Publication.external ops.arguments, 160, 7,
    fun source address native => callerPrimitives ops ReachablePrefixTests.allocate safety 7 6 source address
      Insertion.Tests.model native RecursiveTests.childSeed,
    Interner.Queries.queries⟩

theorem published_child (safety : Bool) :
    (builder (publishing safety)).makeConstant 0 debug (initial safety) = (.ok 4, ready safety) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (ready safety) (rows safety) := by
  refine ⟨?_, (zero_contract safety).2.1⟩
  rw [constant_forwarded]
  change ((zeroFull safety).1, (zeroFull safety).2.world) = (.ok 4, ready safety)
  exact Prod.ext (zero_contract safety).1 (by unfold ready; rfl)

def afterPublication (safety right : Bool) := Arguments.prepare [4, if right then 1 else 0] (ready safety)

theorem publication_literal (safety right : Bool) :
    afterPublication safety right = (.ok rootSource, (afterPublication safety right).2) := by
  apply Prod.ext
  · cases safety <;> cases right <;> insertion_kernel_rfl
  · rfl

/-- A successful real child publication feeds both negation branches. The
outer literal is prepared in its reached world, with the returned ID first.
Its graph, contents and key separation come from that execution. This does not
claim the still-unproved complete outer SUB outcome or recursive induction. -/
theorem actual_negation_input (safety right : Bool) :
    Arguments.Prepared [4, if right then 1 else 0] (ready safety) rootSource (afterPublication safety right).2 ∧
    run (publishing safety) (if right then .neg_right else .neg_left) 0 1 debug (initial safety) =
      Arguments.returned [4, if right then 1 else 0] (ready safety).memory.memory.nextId
        (ConstructorItem.operation (Publication.external ops.arguments) 160 7 ((publishing safety).primitives rootSource)
          Interner.Queries.queries rootSource (Interner.buildOpcode .SUB) [4, if right then 1 else 0] debug
          (afterPublication safety right).2) ∧
    (afterPublication safety right).2.graph = (ready safety).graph := by
  have child := published_child safety
  have literal := publication_literal safety right
  have input := negation_input (publishing safety) (if right then .neg_right else .neg_left) 0 1 debug
    (by cases right <;> simp) (initial safety) (ready safety) (afterPublication safety right).2 4 rootSource
    child.1 child.2.valid (by cases right <;> exact literal)
  have selected : (if (if right then Replacement.neg_right else .neg_left) == .neg_left then (0 : NodeId) else 1) =
      (if right then 1 else 0) := by cases right <;> rfl
  simp only [selected] at input
  exact ⟨input.1, input.2, input.1.graph⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.AlgebraicInput.Tests
