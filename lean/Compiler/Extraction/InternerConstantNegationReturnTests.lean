/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantNegationAllocationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantNegationTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)
open RecursiveTests (Call debug)

attribute [local irreducible] ConstantPublicationTests.ready rootArguments Call.constructed Call.stack

def childFailedWorld (safety : Bool) (value : Word) (after : Native.Frame Nat) :=
  { (child safety value).taken.2.world with memory := memory after }
def childReturned (safety : Bool) (value : Word) (after : Native.Frame Nat) :=
  (child safety value).returnedWorld (childFailedWorld safety value after)
def childPrimitives (safety : Bool) :=
  ConstantPublicationTests.primitives RecursiveNonemptyTests.failing (some growth) safety
def childFull (safety : Bool) (value : Word) := (child safety value).invoked (childPrimitives safety)

theorem child_reads (safety : Bool) (value : Word) (apart : 0 - value ≠ value) :
    (child safety value).taken.2.world.graph.read = Storage.readValue (ConstantPublicationTests.rows safety value) := by
  rw [(child_established safety value apart).entry.origin.graph, (child_established safety value apart).item.graph]
  change (parent safety value).taken.2.world.graph.read = _
  rw [(established safety value).entry.origin.graph, (established safety value).item.graph,
    (literal safety value).2.1.graph]
  exact (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.2.2.1

theorem child_contract (safety : Bool) (value : Word) (apart : 0 - value ≠ value) : ∃ after,
    childFull safety value = (.error (.language .outOfMemory),
      ⟨childReturned safety value after, ⟨none, some (child safety value).normalized, true⟩⟩) ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (childReturned safety value after) (ConstantPublicationTests.rows safety value) ∧
    (childReturned safety value after).memory.effects.keys = (child safety value).before.memory.effects.keys ∧
    (∀ id native, (child safety value).before.memory.memory.heap.lookup id = some native →
      (childReturned safety value after).memory.memory.heap.lookup id = some native) ∧
    (∀ id block, (child safety value).before.memory.heap id = some block →
      (childReturned safety value after).memory.heap id = some block) := by
  apply (child safety value).constant_growth_contract RecursiveNonemptyTests.failing safety
    ReachablePrefixTests.backing 5 13 (ConstantPublicationTests.rows safety value)
    (established safety value).taken (by rw [ConstantPublicationTests.rows_count]; decide)
    (child_reads safety value apart) (child_established safety value apart) (child_observed safety value apart)
    rfl rfl rfl (by decide) (by rw [ConstantPublicationTests.rows_count]; decide)
    (by rw [ConstantPublicationTests.rows_count]; decide) (by decide) (by rw [ConstantPublicationTests.rows_count]; decide)
    _ (fun _ => rfl) (child_unlocked safety value)
  have fits := child_creation_fits safety value apart
  rw [child_duplicate] at fits
  exact fits

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantNegationTests
