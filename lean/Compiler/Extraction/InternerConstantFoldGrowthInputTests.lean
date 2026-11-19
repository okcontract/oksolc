/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveSpareAllocationTests
import Compiler.Extraction.InternerRecursiveGrowthTests
import Compiler.Extraction.InternerConstantFoldInputTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth)
open RecursiveTests (Call debug)
open ConstantInputTests (call initial observed established)

/-- Initial Push publication has spare capacity, so both allocator contexts
produce the same complete native result and effects. -/
theorem constant_insertion (safety : Bool) (value : Word) :
    Native.insert ops ReachablePrefixTests.allocate safety 7 6 ⟨0, 0, 0⟩ (call safety value).address Insertion.Tests.model
      (call safety value).native (call safety value).key (call safety value).normalized true (some growth) (call safety value).taken.2.world =
    Native.insert ops RecursiveNonemptyTests.failing safety 7 6 ⟨0, 0, 0⟩ (call safety value).address Insertion.Tests.model
      (call safety value).native (call safety value).key (call safety value).normalized true (some growth) (call safety value).taken.2.world := by
  have current := established safety value
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have duplicated := congrArg Prod.fst (ConstantPublicationTests.duplicate_result safety value)
  have cloned := congrArg Prod.fst (ConstantPublicationTests.cloned safety value)
  exact (call safety value).spare_insertion_same ReachablePrefixTests.allocate RecursiveNonemptyTests.failing
    (some growth) safety ReachablePrefixTests.backing 5 (ConstantPublicationTests.object safety value)
    (ReachablePrefixTests.cells safety 3) (call safety value).normalized (call safety value).constructed (call safety value).taken.2
    (call safety value).duplicate.2 (call safety value).create.2 (call safety value).clone.2 current.entry current.constructed current.taken
    (by rw [prior.count]; decide) (by rw [prior.count]; decide) (Prod.ext duplicated rfl)
    (Prod.ext (ConstantPublicationTests.created safety value).1 rfl) (Prod.ext cloned rfl)

/-- Reuse the actual arbitrary-word input in the existing recursive growth
family, before its later successful child and parent publication outcome. -/
theorem constant_equivalent (safety : Bool) (depth : Nat) (value : Word) (publishOK : Bool) :
    (RecursiveGrowthTests.children safety (depth + 1) publishOK).constant value debug (initial safety) =
      (.ok 4, ConstantFoldTests.old safety value) := by
  have current := established safety value
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have room : Interner.Queries.queries.atCapacity (call safety value).constructed.graph = false := by
    rw [Interner.Queries.capacity_exact _ _ current.constructed.projected, prior.count]; decide
  have continuation :
      (call safety value).continuation (RecursiveGrowthTests.primitives safety depth ⟨0, 0, 0⟩ publishOK
        (call safety value).address (call safety value).native) =
      (call safety value).continuation (ConstantPublicationTests.primitives RecursiveNonemptyTests.failing (some growth) safety
        (call safety value).address (call safety value).native) := by
    simp only [Call.continuation, Interner.FindCode.controlMiss, Caller.execution, OwnedCall.execution,
      show (call safety value).request.item.kind = 2 from rfl, BitVec.reduceBEq, Bool.false_eq_true,
      Bool.true_and, ↓reduceIte, handoff, graph, current.entry.origin.scope, bind, Effect.bind, pure, Effect.pure]
    exact congrArg (fun ran =>
      (ran.1, { (call safety value).taken.2 with
        world := ran.2
        scope := ⟨some (call safety value).lookup, some (call safety value).normalized, true⟩ }))
      (constant_insertion safety value)
  have same := NativeRecursion.Tests.same_call (call safety value)
    (RecursiveGrowthTests.primitives safety depth ⟨0, 0, 0⟩ publishOK)
    (ConstantPublicationTests.primitives RecursiveNonemptyTests.failing (some growth) safety)
    (observed safety value) current.item.graph room rfl continuation
  have called : (call safety value).invoked (ConstantPublicationTests.primitives RecursiveNonemptyTests.failing (some growth) safety) =
      ConstantPublicationTests.full safety value RecursiveNonemptyTests.failing (some growth) := rfl
  rw [called] at same
  have result : ((ConstantPublicationTests.full safety value RecursiveNonemptyTests.failing (some growth)).1,
      (ConstantPublicationTests.full safety value RecursiveNonemptyTests.failing (some growth)).2.world) =
      (.ok 4, ConstantFoldTests.old safety value) :=
    Prod.ext (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).1 rfl
  rw [RecursiveGrowthTests.children, NativeRecursion.constant_succ]
  exact (congrArg (fun ran => (ran.1, ran.2.world)) same).trans result

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldGrowthTests
