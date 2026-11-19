/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantFoldInputTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)
open RecursiveTests (Call debug)

attribute [local irreducible] ConstantPublicationTests.ready rootArguments Call.constructed Call.stack

theorem folded_apart (value : Word) : Unary.iszero.eval value ≠ value := by
  by_cases zero : value = 0
  · subst value; decide
  · simp only [Unary.eval, boolWord, beq_eq_false_iff_ne.mpr zero, Bool.false_eq_true, ↓reduceIte]
    exact Ne.symm zero

def child (safety : Bool) (value : Word) : Call :=
  ⟨Interner.constructorCode.constantRequest (Unary.iszero.eval value), ⟨0, 0, 0⟩, (parent safety value).taken.2.world⟩
def childReference (safety : Bool) : Compiler.ZigAir.Memory.State := ⟨[], 0, takenAddress safety⟩
def childItemReference (safety : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (childReference safety) AssemblyItem.viewType).toOption.map Prod.snd).getD (childReference safety)
def childScratchReference (safety : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (childItemReference safety) (.array 2 word)).toOption.map Prod.snd).getD (childItemReference safety)

theorem child_allocations (safety : Bool) :
    (childReference safety).valid = true ∧
    Compiler.ZigAir.Memory.allocate (childReference safety) AssemblyItem.viewType =
      .ok (.pointer (.pointer true false AssemblyItem.viewType) ⟨0, 0⟩, childItemReference safety) ∧
    Compiler.ZigAir.Memory.allocate (childItemReference safety) (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨1, 0⟩, childScratchReference safety) := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem child_prepared (safety : Bool) (value : Word) :
    prepare (child safety value).request.item debug (child safety value).before =
      (.ok (child safety value).address, (child safety value).constructed) ∧
    Prepared (child safety value).request.item debug (child safety value).before (child safety value).constructed ∧
    Compiler.ZigAir.Memory.allocate (child safety value).constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨(child safety value).before.memory.memory.nextId + 1, 0⟩,
        (child safety value).stack) ∧
    (child safety value).stack.nextAddress = (childScratchReference safety).nextAddress :=
  (child safety value).prepared_allocations _ _ _ _ _ (established safety value).taken.valid
    (child_allocations safety).1 (taken safety value).2.2.2
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide)
    (child_allocations safety).2.1 (child_allocations safety).2.2

theorem child_normalized (safety : Bool) (value : Word) :
    (child safety value).prepared.1 = .ok [] ∧
    (child safety value).taken.1 = .ok () ∧
    (child safety value).taken.2.scope = ⟨some (child safety value).lookup, some (child safety value).normalized, false⟩ ∧
    (child safety value).taken.2.world = { (child safety value).constructed with memory :=
      { (child safety value).constructed.memory with memory := (child safety value).stack } } :=
  (child safety value).normalized_empty rfl rfl rfl (child_prepared safety value).2.1 (child_prepared safety value).2.2.1

theorem child_missed (safety : Bool) (value : Word) :
    (child safety value).before.graph.table (child safety value).key = none := by
  change (parent safety value).taken.2.world.graph.table (child safety value).key = none
  rw [(established safety value).entry.origin.graph, (established safety value).item.graph,
    (literal safety value).2.1.graph]
  exact ConstantPublicationTests.other_missed safety value (Unary.iszero.eval value) (folded_apart value)
    RecursiveNonemptyTests.failing (some growth)

theorem child_observed (safety : Bool) (value : Word) :
    (child safety value).observations = (child safety value).expected := by
  have current := child_prepared safety value
  have normalized := child_normalized safety value
  simp only [Call.observations, Call.expected, Prod.mk.injEq]
  exact ⟨congrArg Prod.fst current.1, current.2.1.nextId, current.2.2.1,
    normalized.1, normalized.2.1, normalized.2.2.1, child_missed safety value, rfl⟩

theorem child_established (safety : Bool) (value : Word) :
    (child safety value).Established safety ReachablePrefixTests.backing 5 (ConstantPublicationTests.rows safety value) :=
  (child safety value).establish safety ReachablePrefixTests.backing 5 _ (established safety value).taken
    (by rw [ConstantPublicationTests.rows_count]; decide)
    (RecursiveTests.empty_good _ (established safety value).taken.valid)
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) (child_observed safety value)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldTests
