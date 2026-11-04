/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantFoldGrowthParentTests
import Compiler.Extraction.InternerConstantFoldGrowthInputTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)
open RecursiveTests (Call debug)
open ConstantFoldTests

attribute [local irreducible] ConstantPublicationTests.ready rootArguments Call.constructed Call.stack

/-- Use the actual ID returned by arbitrary-word publication as the parent's
native literal operand, within the existing recursive growth family. -/
def program (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) : Except Fault NodeId × World (Publication.Effects Nat) :=
  (do let _ ← ReachablePrefixTests.sequence (RecursiveGrowthTests.children safety depth publishOK) 3
      let id ← (RecursiveGrowthTests.children safety depth publishOK).constant value debug
      (RecursiveGrowthTests.children safety depth publishOK).operation 21 [id] debug) (CallerInputTests.world safety)

theorem program_equivalent (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) :
    program safety (depth + 1) value publishOK = root safety (depth + 1) value publishOK :=
  (Effect.bind_success _ _ _ _ _ (RecursiveGrowthTests.prefix_result safety depth 3 (by decide) publishOK)).trans
    (Effect.bind_success _ _ _ _ _ (constant_equivalent safety depth value publishOK))

/-- Full initialization, arbitrary-word publication, successful folded child,
parent publication success/OOM and all returns are one actual execution.
This scoped branch does not establish general constructor induction. -/
theorem program_contract (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) :
    (program safety (depth + 2) value publishOK).1 = (if publishOK then .ok 5 else .error (.language .outOfMemory)) ∧
    NativeGraph.Facts safety 7 6 ⟨backing safety value, 0⟩ 13 (program safety (depth + 2) value publishOK).2 (rows safety value) ∧
    Constant.value (program safety (depth + 2) value publishOK).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok (some value)) ∧
    Constant.value (program safety (depth + 2) value publishOK).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 5 =
      .ok (.ok (some (Unary.iszero.eval value))) ∧
    (program safety (depth + 2) value publishOK).2.memory.effects.keys = resultKeys safety value publishOK ∧
    (program safety (depth + 2) value publishOK).2.memory.memory.heap.lookup (rootSource safety value).allocation = none ∧
    (program safety (depth + 2) value publishOK).2.memory.heap ReachablePrefixTests.backing = none ∧
    (program safety (depth + 2) value publishOK).2.memory.memory.heap.lookup ReachablePrefixTests.backing = none ∧
    (if publishOK then SliceValid 7 (program safety (depth + 2) value publishOK).2.memory.heap (parent safety value).normalized
     else Consumed (parent safety value).normalized (program safety (depth + 2) value publishOK).2.memory) ∧
    (program safety (depth + 2) value publishOK).2.graph.read = Storage.readValue (rows safety value) := by
  rw [show depth + 2 = (depth + 1) + 1 from rfl, program_equivalent]
  obtain ⟨result, facts, dead, _, owned, oldDead, nativeDead, reads⟩ := root_contract safety depth value publishOK
  have words := native_words safety value _ facts
  exact ⟨result, facts, words.1, words.2, root_keys safety depth value publishOK, dead, oldDead, nativeDead, owned, reads⟩

theorem root_one (safety : Bool) (value : Word) (publishOK : Bool) : root safety 1 value publishOK =
    (.error (.language .unsupported), (parent safety value).taken.2.world) := by
  have current := established safety value
  have room : Interner.Queries.queries.atCapacity (parent safety value).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected, ConstantPublicationTests.rows_count]; decide
  have simplified : (RecursiveGrowthTests.primitives safety 0 (parent safety value).source publishOK
      (parent safety value).address (parent safety value).native).simplify
      (parent safety value).key (parent safety value).normalized (parent safety value).taken.2.world =
        (.error (.language .unsupported), (parent safety value).taken.2.world) := by
    have facts := current.taken.native (by rw [ConstantPublicationTests.rows_count]; decide)
    simp only [RecursiveGrowthTests.primitives, NativeRecursion.dispatcher_snapshot]
    rw [facts.reads]
    exact iszero_failure (input := NativeRecursion.operand) (address := (parent safety value).normalized.address)
      _ _ value _ _ _ (ConstantPublicationTests.value_read safety value _ current.taken).1 rfl
  have continuation := (parent safety value).simplify_error _ _ _ rfl current.entry.origin.scope simplified
  have routed := (parent safety value).route (RecursiveGrowthTests.primitives safety 0 (parent safety value).source publishOK)
    (observed safety value) current.item.graph room rfl
  rw [continuation] at routed
  have result : inner safety 0 value publishOK = (.error (.language .unsupported), (parent safety value).taken.2) := routed
  rw [show 1 = 0 + 1 from rfl, root_route, result]
  rfl

theorem program_one (safety : Bool) (value : Word) (publishOK : Bool) : program safety 1 value publishOK =
    (.error (.language .unsupported), (parent safety value).taken.2.world) :=
  (program_equivalent safety 0 value publishOK).trans (root_one safety value publishOK)

theorem exhaustion_retained (safety : Bool) (value : Word) (publishOK : Bool) :
    ordinary (program safety 1 value publishOK).1 = false ∧
    Held 7 (parent safety value).source [4] (parent safety value).normalized (program safety 1 value publishOK).2 ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5
      (program safety 1 value publishOK).2 (ConstantPublicationTests.rows safety value) ∧
    Constant.value (program safety 1 value publishOK).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok (some value)) := by
  rw [program_one]
  have current := established safety value
  exact ⟨rfl, current.entry.origin.held, current.taken.native (by rw [ConstantPublicationTests.rows_count]; decide),
    (ConstantPublicationTests.value_read safety value _ current.taken).2⟩

theorem program_zero (safety : Bool) (value : Word) (publishOK : Bool) : program safety 0 value publishOK =
    (.error (.language .unsupported), CallerInputTests.world safety) := rfl

/-- Retain every previously read graph word through the successful child and
both parent outcomes, using the actual reached row extension. -/
theorem program_preserves_words (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool)
    (id : NodeId) (word : Word) (known : (old safety value).graph.read id = some word) :
    (program safety (depth + 2) value publishOK).2.graph.read id = some word := by
  obtain ⟨_, _, _, _, _, _, _, _, _, reads⟩ := program_contract safety depth value publishOK
  have prior := (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.2.2.1
  change (old safety value).graph.read = _ at prior
  rw [prior] at known
  have inside : id.toNat < (ConstantPublicationTests.rows safety value).length := by
    by_cases bounded : id.toNat < (ConstantPublicationTests.rows safety value).length
    · exact bounded
    · simp only [Storage.readValue, List.getElem?_eq_none (Nat.le_of_not_gt bounded), Option.map_none] at known
      contradiction
  rw [reads]
  simpa only [Storage.readValue, rows, List.getElem?_append, inside, ↓reduceIte] using known

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldGrowthTests
