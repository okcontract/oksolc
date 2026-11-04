/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeConstantTests
import Compiler.Extraction.InternerConstantCacheTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.WordConstantTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth)
open RecursiveTests (Call debug)
open ConstantInputTests (call initial observed established)
open ConstantTests (children primitives prefix_result)

def ready (safety : Bool) (value : Word) := ConstantPublicationTests.ready safety value RecursiveNonemptyTests.failing (some growth)

theorem constant_equivalent (safety : Bool) (depth : Nat) (value : Word) :
    (children safety (depth + 1)).constant value debug (initial safety) = (.ok 4, ready safety value) := by
  have current := established safety value
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have room : Interner.Queries.queries.atCapacity (call safety value).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected, prior.count]; decide
  have continuation :
      (call safety value).continuation (primitives safety depth ⟨0, 0, 0⟩ (call safety value).address (call safety value).native) =
      (call safety value).continuation (ConstantPublicationTests.primitives RecursiveNonemptyTests.failing (some growth) safety
        (call safety value).address (call safety value).native) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (call safety value).request.item.kind = 2 from rfl, BitVec.reduceBEq, Bool.false_eq_true,
      Bool.true_and, ↓reduceIte, handoff, graph, current.entry.origin.scope,
      bind, Effect.bind, pure, Effect.pure]
    rfl
  have same := NativeRecursion.Tests.same_call (call safety value) (primitives safety depth ⟨0, 0, 0⟩)
    (ConstantPublicationTests.primitives RecursiveNonemptyTests.failing (some growth) safety)
    (observed safety value) current.item.graph room rfl continuation
  have called : (call safety value).invoked (ConstantPublicationTests.primitives RecursiveNonemptyTests.failing (some growth) safety) =
      ConstantPublicationTests.full safety value RecursiveNonemptyTests.failing (some growth) := rfl
  rw [called] at same
  have result : ((ConstantPublicationTests.full safety value RecursiveNonemptyTests.failing (some growth)).1,
      (ConstantPublicationTests.full safety value RecursiveNonemptyTests.failing (some growth)).2.world) =
      (.ok 4, ready safety value) :=
    Prod.ext (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).1 rfl
  rw [children, constant_succ]
  exact (congrArg (fun ran => (ran.1, ran.2.world)) same).trans result

/-- The returned identifier is passed to the source materializer, whose
constant call finds the key published by the preceding constructor. -/
theorem materialize_equivalent (safety : Bool) (depth : Nat) (value : Word) :
    (children safety (depth + 1)).materialize 4 value debug (ready safety value) =
      (.ok 4, ConstantCacheTests.returned safety value) := by
  have called := ConstantCacheTests.invoked safety value (primitives safety depth ⟨0, 0, 0⟩)
  rw [children, materialize_succ, constant_succ]
  exact congrArg (fun result => (result.1, result.2.world)) called

/-- One native constructor family supplies initialization, arbitrary-word
publication and the complete materializer cache-hit continuation. -/
def program (safety materialized : Bool) (depth : Nat) (value : Word) :
    Except Fault NodeId × World (Publication.Effects Nat) :=
  (do let _ ← ReachablePrefixTests.sequence (children safety depth) 3
      let id ← if materialized then (children safety depth).materialize 99 value debug
        else (children safety depth).constant value debug
      (children safety depth).materialize id value debug) (CallerInputTests.world safety)

attribute [local irreducible] ConstantCacheTests.returned ConstantPublicationTests.ready

theorem program_equivalent (safety materialized : Bool) (depth : Nat) (value : Word) :
    program safety materialized (depth + 1) value = (.ok 4, ConstantCacheTests.returned safety value) := by
  have first : (if materialized then (children safety (depth + 1)).materialize 99 value debug
      else (children safety (depth + 1)).constant value debug) (initial safety) = (.ok 4, ready safety value) := by
    cases materialized
    · exact constant_equivalent safety depth value
    · rw [children, materialize_succ]; exact constant_equivalent safety depth value
  cases materialized <;>
    exact (Effect.bind_success _ _ _ _ _ (prefix_result safety depth 3 (by decide))).trans
      ((Effect.bind_success _ (fun id => (children safety (depth + 1)).materialize id value debug) _ _ _ first).trans
        (materialize_equivalent safety depth value))

theorem program_contract (safety materialized : Bool) (depth : Nat) (value : Word) :
    (program safety materialized (depth + 1) value).1 = .ok 4 ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5
      (program safety materialized (depth + 1) value).2 (ConstantPublicationTests.rows safety value) ∧
    Constant.value (program safety materialized (depth + 1) value).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 =
      .ok (.ok (some value)) ∧
    (∀ id cell, (ready safety value).memory.memory.heap.lookup id = some cell →
      (program safety materialized (depth + 1) value).2.memory.memory.heap.lookup id = some cell) ∧
    (program safety materialized (depth + 1) value).2.graph = (ready safety value).graph ∧
    (program safety materialized (depth + 1) value).2.memory.effects = (ready safety value).memory.effects ∧
    (program safety materialized (depth + 1) value).2.memory.heap = (ready safety value).memory.heap ∧
    (program safety materialized (depth + 1) value).2.memory.memory.heap.lookup (ready safety value).memory.memory.nextId = none ∧
    (program safety materialized (depth + 1) value).2.memory.memory.heap.lookup ((ready safety value).memory.memory.nextId + 1) = none := by
  rw [program_equivalent]
  have facts := ConstantCacheTests.returned_facts safety value
  exact ⟨rfl, facts.1.native (by rw [ConstantPublicationTests.rows_count]; decide),
    (ConstantPublicationTests.value_read safety value _ facts.1).2, facts.2.1,
    facts.2.2.1, facts.2.2.2.1, facts.2.2.2.2, ConstantCacheTests.locals_retired safety value⟩

theorem program_zero (safety materialized : Bool) (value : Word) : program safety materialized 0 value =
    (.error (.language .unsupported), CallerInputTests.world safety) := rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.WordConstantTests
