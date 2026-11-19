/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveZeroTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveNonemptyTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)
open RecursiveTests (Call debug)

def rootArguments (safety : Bool) := Arguments.prepare [0, 4] (ready safety)
def rootSource : View := ⟨24, 0, 2⟩
def parent (safety : Bool) : Call := ⟨Interner.constructorCode.operationRequest 20 [0, 4], rootSource, (rootArguments safety).2⟩
def childArguments (safety : Bool) := Arguments.prepare [0] (parent safety).taken.2.world
def childSource : View := ⟨28, 0, 1⟩
def child (safety : Bool) : Call := ⟨Interner.constructorCode.operationRequest 21 [0], childSource, (childArguments safety).2⟩

-- Keep reached worlds opaque during elaboration; their equations are proved
-- below by the kernel and their invariants by the production contracts.
attribute [local irreducible] ready rootArguments childArguments

theorem rows_count (safety : Bool) : (rows safety).length = 5 := by
  simp only [rows, List.length_append, List.length_singleton,
    (ReachablePrefixTests.initialized_prefix safety 3 (by decide)).count]

theorem literals_observed (safety : Bool) :
    (rootArguments safety).1 = .ok rootSource ∧ (ready safety).memory.memory.nextId = 24 ∧
    (childArguments safety).1 = .ok childSource ∧ (parent safety).taken.2.world.memory.memory.nextId = 28 := by
  cases safety <;> refine ⟨?_, ?_, ?_, ?_⟩ <;> insertion_kernel_rfl

theorem calls_observed (safety isChild : Bool) :
    (if isChild then child safety else parent safety).observations =
      (if isChild then child safety else parent safety).expected := by
  cases safety <;> cases isChild <;> insertion_kernel_rfl

theorem literal_facts (safety : Bool) (values : List NodeId) (before after : World (Publication.Effects Nat)) (source : View)
    (facts : GraphFacts safety ReachablePrefixTests.backing 5 before (rows safety))
    (ran : Arguments.prepare values before = (.ok source, after)) :
    Arguments.Prepared values before source after ∧ GraphFacts safety ReachablePrefixTests.backing 5 after (rows safety) := by
  have prepared := Arguments.prepare_success values before after source facts.valid ran
  refine ⟨prepared, facts.frame (by rw [rows_count]; decide) prepared.good.1 ?_ ?_ ?_ prepared.frame ?_⟩
  · exact (congrArg Interner.Heap.representatives prepared.graph).trans facts.projected
  · exact congrArg Interner.Heap.table prepared.graph
  · exact congrArg Publication.Effects.keys prepared.effects
  · intro id block found; rw [prepared.heap]; exact found

theorem parent_literal (safety : Bool) :
    Arguments.Prepared [0, 4] (ready safety) rootSource (rootArguments safety).2 ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (parent safety).before (rows safety) :=
  literal_facts safety [0, 4] (ready safety) (rootArguments safety).2 rootSource (zero_contract safety).2.1
    (by simpa only [rootArguments] using
      (Prod.ext (literals_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2)))

theorem parent_established (safety : Bool) : (parent safety).Established safety ReachablePrefixTests.backing 5 (rows safety) :=
  (parent safety).establish safety ReachablePrefixTests.backing 5 (rows safety) (parent_literal safety).2
    (by rw [rows_count]; decide) (parent_literal safety).1.good
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (calls_observed safety false)

theorem child_literal (safety : Bool) :
    Arguments.Prepared [0] (parent safety).taken.2.world childSource (childArguments safety).2 ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (child safety).before (rows safety) :=
  literal_facts safety [0] (parent safety).taken.2.world (childArguments safety).2 childSource (parent_established safety).taken
    (by simpa only [childArguments] using
      (Prod.ext (literals_observed safety).2.2.1 rfl : childArguments safety = (.ok childSource, (childArguments safety).2)))

theorem child_established (safety : Bool) : (child safety).Established safety ReachablePrefixTests.backing 5 (rows safety) :=
  (child safety).establish safety ReachablePrefixTests.backing 5 (rows safety) (child_literal safety).2
    (by rw [rows_count]; decide) (child_literal safety).1.good
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (calls_observed safety true)

theorem graph_reads (safety : Bool) :
    (parent safety).taken.2.world.graph.read = Storage.readValue (rows safety) ∧
    (child safety).taken.2.world.graph.read = Storage.readValue (rows safety) := by
  have parentFacts := parent_established safety
  have childFacts := child_established safety
  have first : (parent safety).taken.2.world.graph = (ready safety).graph :=
    parentFacts.entry.origin.graph.trans (parentFacts.item.graph.trans (parent_literal safety).1.graph)
  have second : (child safety).taken.2.world.graph = (parent safety).taken.2.world.graph :=
    childFacts.entry.origin.graph.trans (childFacts.item.graph.trans (child_literal safety).1.graph)
  exact ⟨(congrArg Interner.Heap.read first).trans (zero_contract safety).2.2.2.1,
    (congrArg Interner.Heap.read (second.trans first)).trans (zero_contract safety).2.2.2.1⟩

theorem first_row (safety : Bool) : (rows safety)[(0 : NodeId).toNat]'(by rw [rows_count]; decide) = ReachablePrefixTests.row safety 0 := by
  change (ReachablePrefixTests.cells safety 3 ++ [zeroRow safety])[0] = _
  rfl

theorem first_constant (safety : Bool) (world : World (Publication.Effects Nat))
    (facts : GraphFacts safety ReachablePrefixTests.backing 5 world (rows safety)) :
    (Interner.representativeReads world.graph).constant 0 = .ok none ∧
    Constant.value world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 = .ok (.ok none) := by
  have inside : (0 : NodeId).toNat < (rows safety).length := by rw [rows_count]; decide
  have logical : Storage.representativeProgram.run (rows safety) 0 = .ok (ReachablePrefixTests.row safety 0) := by
    rw [Storage.representative_correct, List.getElem?_eq_getElem inside, first_row]
  obtain ⟨_, _, backing, found, typed, writable, _⟩ := facts.owned
  have native := Constant.nonpush world.memory.memory (Owner.headerAddress ⟨6, 0⟩) ReachablePrefixTests.backing 5 backing (rows safety) 0
    facts.valid.memory (readHeader_items _ _ _ _ facts.header) found typed writable (by rw [rows_count]; decide)
    facts.descriptors inside (facts.items _ (List.getElem_mem inside)).choose_spec.2.2
    (by rw [first_row]; change (1 : Int) ≠ 2; decide)
  refine ⟨?_, native.2⟩
  simp only [Interner.representativeReads, facts.projected, Nested.storageReads, Storage.constantProgram, Storage.ConstantRead.run, logical]
  rfl

theorem first_operation (safety : Bool) (world : World (Publication.Effects Nat)) (opcode : Opcode)
    (facts : GraphFacts safety ReachablePrefixTests.backing 5 world (rows safety)) (different : opcode ≠ 48) :
    (Interner.representativeReads world.graph).operation 0 opcode = .ok none ∧
    Operation.run world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 opcode = .ok (.ok none) := by
  have logical : Storage.representativeProgram.run (rows safety) 0 = .ok (ReachablePrefixTests.row safety 0) := by
    rw [Storage.representative_correct, List.getElem?_eq_getElem (by rw [rows_count]; decide), first_row]
  have missed : Storage.operationProgram.run (rows safety) 0 opcode = .ok none := by
    simp only [Storage.OperationRead.run, Storage.operationProgram, logical]
    have kind : (ReachablePrefixTests.row safety 0).item.kind = 1 := rfl
    have instruction : (ReachablePrefixTests.row safety 0).item.instruction = some 48 := rfl
    simp [kind, instruction]
    exact Ne.symm different
  have native := facts.accepted.1 0 opcode
  rw [missed] at native
  refine ⟨?_, native⟩
  simp only [Interner.representativeReads, facts.projected, Nested.storageReads, missed]

/-- Any reached frame of the published rows supplies the native Push-zero
read. Literal and constructor frames transport the fact to their query sites. -/
theorem zero_constant (safety : Bool) (world : World (Publication.Effects Nat))
    (facts : GraphFacts safety ReachablePrefixTests.backing 5 world (rows safety)) :
    (Interner.representativeReads world.graph).constant 4 = .ok (some 0) ∧
    Constant.value world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok (some 0)) :=
  ConstantPublicationTests.value_read safety 0 world facts

/-- The parent's zero test reads the data written by the full constant call.
All intervening literal, item and normalization operations supply the frame. -/
theorem parent_zero (safety : Bool) :
    (Interner.representativeReads (parent safety).taken.2.world.graph).constant 4 = .ok (some 0) ∧
    Constant.value (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 = .ok (.ok (some 0)) :=
  zero_constant safety _ (parent_established safety).taken

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveNonemptyTests
