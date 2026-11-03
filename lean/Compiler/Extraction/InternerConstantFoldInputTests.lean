/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeWordConstantTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)
open RecursiveTests (Call debug)

abbrev old := NativeRecursion.WordConstantTests.ready
def rootArguments (safety : Bool) (value : Word) := Arguments.prepare [4] (old safety value)
def rootSource (safety : Bool) (value : Word) : View := ⟨(old safety value).memory.memory.nextId, 0, 1⟩
def parent (safety : Bool) (value : Word) : Call :=
  ⟨Interner.constructorCode.operationRequest 21 [4], rootSource safety value, (rootArguments safety value).2⟩
def reference (safety : Bool) : Compiler.ZigAir.Memory.State := ⟨[], 0, ConstantPublicationTests.publishedAddress safety⟩
def literalReference (safety : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (reference safety) (.array 1 word)).toOption.map Prod.snd).getD (reference safety)
def itemReference (safety : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (literalReference safety) AssemblyItem.viewType).toOption.map Prod.snd).getD (literalReference safety)
def scratchReference (safety : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (itemReference safety) (.array 2 word)).toOption.map Prod.snd).getD (itemReference safety)

theorem allocations (safety : Bool) :
    (reference safety).valid = true ∧
    Compiler.ZigAir.Memory.allocate (reference safety) (.array 1 word) =
      .ok (.pointer (.pointer true false (.array 1 word)) ⟨0, 0⟩, literalReference safety) ∧
    Compiler.ZigAir.Memory.allocate (literalReference safety) AssemblyItem.viewType =
      .ok (.pointer (.pointer true false AssemblyItem.viewType) ⟨1, 0⟩, itemReference safety) ∧
    Compiler.ZigAir.Memory.allocate (itemReference safety) (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨2, 0⟩, scratchReference safety) := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

attribute [local irreducible] ConstantPublicationTests.ready rootArguments

theorem literal (safety : Bool) (value : Word) :
    rootArguments safety value = (.ok (rootSource safety value), (parent safety value).before) ∧
    Arguments.Prepared [4] (old safety value) (rootSource safety value) (parent safety value).before ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (parent safety value).before (ConstantPublicationTests.rows safety value) ∧
    (parent safety value).before.memory.memory.nextAddress = (literalReference safety).nextAddress := by
  have prior := ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)
  have address : (old safety value).memory.memory.nextAddress = (reference safety).nextAddress := prior.2.2.2.2.2.2.1
  have valid : Valid (old safety value).memory := prior.2.1.valid
  obtain ⟨pointer, allocated, allocation, counter⟩ := Compiler.ZigAir.Memory.allocate_at_same_address _ _ _
    valid.memory (allocations safety).1 address _ _ (allocations safety).2.1
  obtain ⟨after, ran, _⟩ := TemporaryUnary.prepare_verified 4 (old safety value) pointer allocated valid allocation
  have same : after = (parent safety value).before := by
    simpa only [parent, rootArguments, Arguments.prepare] using (congrArg Prod.snd ran).symm
  rw [same] at ran
  have complete := BinaryPreludeTests.literal_facts safety 5 (ConstantPublicationTests.rows safety value) [4]
    (old safety value) (parent safety value).before (rootSource safety value) prior.2.1
    (by rw [ConstantPublicationTests.rows_count]; decide) ran
  exact ⟨by simpa only [rootArguments, Arguments.prepare, rootSource] using ran, complete.1, complete.2, (TemporaryUnary.prepare_address _ _ _ _ _ _ valid allocation ran).trans counter⟩

theorem prepared (safety : Bool) (value : Word) :
    prepare (parent safety value).request.item debug (parent safety value).before =
      (.ok (parent safety value).address, (parent safety value).constructed) ∧
    Prepared (parent safety value).request.item debug (parent safety value).before (parent safety value).constructed ∧
    Compiler.ZigAir.Memory.allocate (parent safety value).constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨(parent safety value).before.memory.memory.nextId + 1, 0⟩,
        (parent safety value).stack) ∧
    (parent safety value).stack.nextAddress = (scratchReference safety).nextAddress :=
  (parent safety value).prepared_allocations _ _ _ _ _ (literal safety value).2.2.1.valid
    (Compiler.ZigAir.Memory.allocate_preserves_valid _ _ _ _ (allocations safety).2.1)
    (literal safety value).2.2.2 (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide)
    (allocations safety).2.2.1 (allocations safety).2.2.2

attribute [local irreducible] Call.constructed Call.stack

def entered (safety : Bool) (value : Word) := { (parent safety value).constructed with memory :=
  { (parent safety value).constructed.memory with memory := (parent safety value).stack } }

theorem initialized (safety : Bool) (value : Word) :
    (parent safety value).prepared =
      (.ok [4], ⟨entered safety value, { lookup := some (parent safety value).lookup }⟩) := by
  have commutative : Interner.Scoped.commutative (parent safety value).request.item = .ok false := rfl
  simp only [Call.prepared, Caller.initLookup, commutative, init, Bool.not_false, Bool.true_or, ↓reduceIte]
  rfl

def duplicateBase (safety : Bool) := ((scratchReference safety).nextAddress / 4 + 1) * 4

def takenAddress (safety : Bool) := max (scratchReference safety).nextAddress (duplicateBase safety + 4)

theorem taken (safety : Bool) (value : Word) :
    (parent safety value).taken.1 = .ok () ∧
    (parent safety value).taken.2.scope =
      ⟨some (parent safety value).lookup, some (parent safety value).normalized, false⟩ ∧
    (parent safety value).taken.2.world.memory.memory.nextId = (parent safety value).before.memory.memory.nextId + 3 ∧
    (parent safety value).taken.2.world.memory.memory.nextAddress = takenAddress safety := by
  have complete := (parent safety value).borrowed_taken (literal safety value).2.1.good
    (prepared safety value).2.1 (prepared safety value).2.2.1 rfl (by change [4] ≠ ([] : List NodeId); decide) (by
      rw [(prepared safety value).2.2.2]
      change ((scratchReference safety).nextAddress / 4 + 1) * 4 + 4 ≤ Compiler.ZigAir.Memory.addressLimit
      cases safety <;> apply of_decide_eq_true <;> insertion_kernel_rfl)
  simpa only [(prepared safety value).2.2.2] using complete.2

theorem parent_missed (safety : Bool) (value : Word) :
    (parent safety value).before.graph.table (parent safety value).key = none := by
  rw [(literal safety value).2.1.graph]
  have table := (ConstantPublicationTests.contract safety value RecursiveNonemptyTests.failing (some growth)).2.2.2.2.2.2.2.2.1
  change (old safety value).graph.table = _ at table
  rw [table]
  have different : Cache.equal equalityFields (parent safety value).key (ConstantInputTests.call safety value).key = false := rfl
  simp only [Cache.put, different, Bool.false_eq_true, ↓reduceIte]
  change (ConstantInputTests.initial safety).graph.table ⟨1, 21, 0, [4], Interner.constructorCode.sequence⟩ = none
  cases safety <;> insertion_kernel_rfl

theorem observed (safety : Bool) (value : Word) :
    (parent safety value).observations = (parent safety value).expected := by
  have current := prepared safety value
  have taken := taken safety value
  simp only [Call.observations, Call.expected, Prod.mk.injEq]
  exact ⟨congrArg Prod.fst current.1, current.2.1.nextId, current.2.2.1,
    congrArg Prod.fst (initialized safety value), taken.1, taken.2.1, parent_missed safety value, rfl⟩

theorem established (safety : Bool) (value : Word) :
    (parent safety value).Established safety ReachablePrefixTests.backing 5 (ConstantPublicationTests.rows safety value) :=
  (parent safety value).establish safety ReachablePrefixTests.backing 5 _ (literal safety value).2.2.1
    (by rw [ConstantPublicationTests.rows_count]; decide) (literal safety value).2.1.good
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (observed safety value)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldTests
