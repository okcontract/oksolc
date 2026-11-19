/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerBinaryPreludeTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveBorrowedTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)
open RecursiveTests (Call debug)

-- Preserve existing XOR clients while sharing the complete native publication
-- with the named-local AND recursion case.
def initial := BinaryPreludeTests.initial
def xorArguments := BinaryPreludeTests.arguments
def xorSource := BinaryPreludeTests.source
def xorCall (safety : Bool) := BinaryPreludeTests.call safety true
def xorOperands := BinaryPreludeTests.operands
def xorSeed := BinaryPreludeTests.seed
def xorPrimitives (safety : Bool) := BinaryPreludeTests.primitives safety true
def xorInner (safety : Bool) := BinaryPreludeTests.inner safety true
def xorFull (safety : Bool) := BinaryPreludeTests.full safety true
def xorRow (safety : Bool) := BinaryPreludeTests.row safety true
def rows (safety : Bool) := BinaryPreludeTests.rows safety true
def ready (safety : Bool) := BinaryPreludeTests.ready safety true

attribute [local irreducible] BinaryPreludeTests.inner BinaryPreludeTests.full BinaryPreludeTests.ready

theorem prefix_observed (safety : Bool) :
    (xorArguments safety).1 = .ok xorSource ∧
    (xorCall safety).observations = (xorCall safety).expected ∧
    (xorCall safety).duplicate.1 = .ok (xorOperands, ⟨view (xorCall safety).normalized, [0, 1], none⟩) ∧
    (xorCall safety).create.1 = .ok 26 ∧ (xorCall safety).clone.1 = .ok (xorCall safety).native :=
  BinaryPreludeTests.prefix_observed safety true

theorem literal_facts (safety : Bool) (capacity : Nat) (rows : List Storage.Cell)
    (values : List NodeId) (before after : World (Publication.Effects Nat)) (source : View)
    (facts : GraphFacts safety ReachablePrefixTests.backing capacity before rows) (bounded : rows.length ≤ capacity)
    (ran : Arguments.prepare values before = (.ok source, after)) :
    Arguments.Prepared values before source after ∧ GraphFacts safety ReachablePrefixTests.backing capacity after rows :=
  BinaryPreludeTests.literal_facts safety capacity rows values before after source facts bounded ran

theorem xor_literal (safety : Bool) :
    Arguments.Prepared [0, 1] (initial safety) xorSource (xorCall safety).before ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (xorCall safety).before (ReachablePrefixTests.cells safety 3) :=
  BinaryPreludeTests.literal safety true

theorem xor_established (safety : Bool) : (xorCall safety).Established safety ReachablePrefixTests.backing 5 (ReachablePrefixTests.cells safety 3) :=
  BinaryPreludeTests.established safety true

theorem xor_simplified (safety : Bool) : (xorSeed xorSource).simplify (xorCall safety).key
    (xorCall safety).normalized (xorCall safety).taken.2.world = (.ok none, (xorCall safety).taken.2.world) :=
  BinaryPreludeTests.simplified safety true

theorem xor_inner_contract (safety : Bool) :
    (xorInner safety).1 = .ok 4 ∧ GraphFacts safety ReachablePrefixTests.backing 5 (xorInner safety).2.world (rows safety) ∧
    AssemblyClone.NativeFields.Represents (xorInner safety).2.world.memory.memory ⟨26, 0⟩ (xorCall safety).native ∧
    (xorInner safety).2.world.graph.read = Storage.readValue (rows safety) :=
  BinaryPreludeTests.inner_contract safety true

theorem xor_route (safety : Bool) : xorFull safety =
    TemporaryArguments.unwind (initial safety).memory.memory.nextId (xorInner safety) :=
  BinaryPreludeTests.route safety true

theorem rows_count (safety : Bool) : (rows safety).length = 5 :=
  BinaryPreludeTests.rows_count safety true

theorem xor_contract (safety : Bool) :
    (xorFull safety).1 = .ok 4 ∧ GraphFacts safety ReachablePrefixTests.backing 5 (ready safety) (rows safety) ∧
    (ready safety).graph.read = Storage.readValue (rows safety) :=
  BinaryPreludeTests.contract safety true

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveBorrowedTests
