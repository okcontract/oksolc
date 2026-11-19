/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveBorrowedSetupTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveBorrowedTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)
open RecursiveTests (Call debug)

def rootArguments (safety : Bool) := Arguments.prepare [4] (ready safety)
def rootSource : View := ⟨27, 0, 1⟩
def parent (safety : Bool) : Call := ⟨Interner.constructorCode.operationRequest 21 [4], rootSource, (rootArguments safety).2⟩
def childSource : View := view xorOperands
def child (safety : Bool) : Call := ⟨Interner.constructorCode.operationRequest 20 [0, 1], childSource, (parent safety).taken.2.world⟩

attribute [local irreducible] ready rootArguments

theorem literals_observed (safety : Bool) :
    (rootArguments safety).1 = .ok rootSource ∧ (ready safety).memory.memory.nextId = 27 ∧
    (parent safety).taken.2.world.memory.memory.nextId = 31 := by
  have checked : ((rootArguments safety).1, (ready safety).memory.memory.nextId,
      (parent safety).taken.2.world.memory.memory.nextId) = (.ok rootSource, 27, 31) := by
    cases safety <;> insertion_kernel_rfl
  have first := Prod.mk.inj checked
  have second := Prod.mk.inj first.2
  exact ⟨first.1, second.1, second.2⟩

theorem calls_observed (safety isChild : Bool) :
    (if isChild then child safety else parent safety).observations =
      (if isChild then child safety else parent safety).expected := by
  have checked : ((parent safety).observations, (child safety).observations) =
      ((parent safety).expected, (child safety).expected) := by
    cases safety <;> insertion_kernel_rfl
  cases isChild
  · exact (Prod.mk.inj checked).1
  · exact (Prod.mk.inj checked).2

theorem parent_literal (safety : Bool) :
    Arguments.Prepared [4] (ready safety) rootSource (parent safety).before ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (parent safety).before (rows safety) :=
  literal_facts safety 5 (rows safety) [4] (ready safety) (parent safety).before rootSource (xor_contract safety).2.1
    (by rw [rows_count]; decide) (by simpa only [parent, rootArguments] using
      (Prod.ext (literals_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2)))

theorem parent_established (safety : Bool) : (parent safety).Established safety ReachablePrefixTests.backing 5 (rows safety) :=
  (parent safety).establish safety ReachablePrefixTests.backing 5 (rows safety) (parent_literal safety).2
    (by rw [rows_count]; decide) (parent_literal safety).1.good
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (calls_observed safety false)

theorem xor_query_at (safety : Bool) (world : World (Publication.Effects Nat))
    (facts : GraphFacts safety ReachablePrefixTests.backing 5 world (rows safety)) :
    (Interner.representativeReads world.graph).operation 4 24 = .ok (some xorOperands) ∧
    Operation.run world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 24 =
      .ok (.ok (some (Operation.returned xorOperands))) := by
  have logical : Storage.operationProgram.run (rows safety) 4 24 = .ok (some xorOperands) := by
    cases safety <;> insertion_kernel_rfl
  have native := (facts.native (by rw [rows_count]; decide)).operations 4 24
  rw [logical] at native
  exact ⟨by simp only [Interner.representativeReads, facts.projected, Nested.storageReads, logical], native⟩

/-- The actual XOR query obtains the published graph allocation. Its native
descriptor, contents and map-key separation come from that same reached graph. -/
theorem xor_input_at (safety : Bool) (world : World (Publication.Effects Nat))
    (facts : GraphFacts safety ReachablePrefixTests.backing 5 world (rows safety)) :
    BorrowedQuery.observe 7 4 24 world = .ok (some xorOperands) ∧
    Good childSource [0, 1] world ∧
    ∀ key old, world.memory.effects.keys key = some old → key.arguments ≠ [] →
      childSource.allocation ≠ old.address := by
  obtain ⟨slice, _, observed, good, apart⟩ := (facts.native (by rw [rows_count]; decide)).queried_input 4 24
    (Operation.returned xorOperands) (xor_query_at safety world facts).2
  have same := (BorrowedQuery.accepted 7 4 24 _ slice observed).1
  rw [(xor_query_at safety world facts).1] at same
  cases Option.some.inj (Except.ok.inj same)
  exact ⟨observed, good, fun key old found nonempty => apart key old found nonempty (by decide)⟩

theorem xor_query (safety : Bool) :
    (Interner.representativeReads (parent safety).taken.2.world.graph).operation 4 24 = .ok (some xorOperands) ∧
    Operation.run (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 24 =
      .ok (.ok (some (Operation.returned xorOperands))) := xor_query_at safety _ (parent_established safety).taken

theorem child_input (safety : Bool) :
    BorrowedQuery.observe 7 4 24 (parent safety).taken.2.world = .ok (some xorOperands) ∧
    Good childSource [0, 1] (child safety).before ∧
    ∀ key old, (child safety).before.memory.effects.keys key = some old → key.arguments ≠ [] →
      childSource.allocation ≠ old.address := xor_input_at safety _ (parent_established safety).taken

theorem child_established (safety : Bool) : (child safety).Established safety ReachablePrefixTests.backing 5 (rows safety) :=
  (child safety).establish safety ReachablePrefixTests.backing 5 (rows safety) (parent_established safety).taken
    (by rw [rows_count]; decide) (child_input safety).2.1
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (calls_observed safety true)

theorem graph_reads (safety : Bool) :
    (parent safety).taken.2.world.graph.read = Storage.readValue (rows safety) ∧
    (child safety).taken.2.world.graph.read = Storage.readValue (rows safety) := by
  have parentFacts := parent_established safety
  have childFacts := child_established safety
  have first : (parent safety).taken.2.world.graph = (ready safety).graph :=
    parentFacts.entry.origin.graph.trans (parentFacts.item.graph.trans (parent_literal safety).1.graph)
  have second : (child safety).taken.2.world.graph = (parent safety).taken.2.world.graph :=
    childFacts.entry.origin.graph.trans childFacts.item.graph
  exact ⟨(congrArg Interner.Heap.read first).trans (xor_contract safety).2.2,
    (congrArg Interner.Heap.read (second.trans first)).trans (xor_contract safety).2.2⟩

theorem constant_nonpush (safety : Bool) (capacity : Nat) (rows : List Storage.Cell)
    (world : World (Publication.Effects Nat)) (facts : GraphFacts safety ReachablePrefixTests.backing capacity world rows)
    (bounded : rows.length ≤ capacity) (id : NodeId) (inside : id.toNat < rows.length)
    (kind : rows[id.toNat].item.kind = 1) :
    (Interner.representativeReads world.graph).constant id = .ok none ∧
    Constant.value world.memory.memory (Owner.headerAddress ⟨6, 0⟩) id = .ok (.ok none) := by
  exact (facts.native bounded).nonpush id inside (by rw [kind]; decide)

theorem constants (safety : Bool) (world : World (Publication.Effects Nat))
    (facts : GraphFacts safety ReachablePrefixTests.backing 5 world (rows safety)) (id : NodeId)
    (selected : id = 0 ∨ id = 1 ∨ id = 4) :
    (Interner.representativeReads world.graph).constant id = .ok none ∧
    Constant.value world.memory.memory (Owner.headerAddress ⟨6, 0⟩) id = .ok (.ok none) := by
  have inside : id.toNat < (rows safety).length := by rcases selected with rfl | rfl | rfl <;> rw [rows_count] <;> decide
  have kinds : (rows safety).map (fun cell => cell.item.kind) = [1, 1, 1, 1, 1] := by
    cases safety <;> insertion_kernel_rfl
  have kind : (rows safety)[id.toNat].item.kind = 1 := by
    have selectedKind := congrArg (fun values => values[id.toNat]?) kinds
    simp only [List.getElem?_map, List.getElem?_eq_getElem inside, Option.map_some] at selectedKind
    rcases selected with rfl | rfl | rfl <;> exact Option.some.inj selectedKind
  exact constant_nonpush safety 5 (rows safety) world facts (by rw [rows_count]; decide) id inside
    kind

theorem parent_iszero (safety : Bool) :
    (Interner.representativeReads (parent safety).taken.2.world.graph).operation 4 21 = .ok none ∧
    Operation.run (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 21 = .ok (.ok none) := by
  have logical : Storage.operationProgram.run (rows safety) 4 21 = .ok none := by cases safety <;> insertion_kernel_rfl
  have facts := (parent_established safety).taken
  have native := (facts.native (by rw [rows_count]; decide)).operations 4 21
  rw [logical] at native
  exact ⟨by simp only [Interner.representativeReads, facts.projected, Nested.storageReads, logical], native⟩

/-- Native reads used by the full XOR prefix, before it publishes the row
borrowed by the parent. Constants and nested-XOR queries both miss. -/
theorem xor_native_reads (safety : Bool) (id : NodeId) (selected : id = 0 ∨ id = 1) :
    (Interner.representativeReads (xorCall safety).taken.2.world.graph).constant id = .ok none ∧
    Constant.value (xorCall safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) id = .ok (.ok none) ∧
    Operation.run (xorCall safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) id 24 = .ok (.ok none) := by
  have prior := ReachablePrefixTests.initialized_prefix safety 3 (by decide)
  have facts := (xor_established safety).taken
  have inside : id.toNat < (ReachablePrefixTests.cells safety 3).length := by
    rcases selected with rfl | rfl <;> rw [prior.count] <;> decide
  have kinds : (ReachablePrefixTests.cells safety 3).map (fun cell => cell.item.kind) = [1, 1, 1, 1] := by
    cases safety <;> insertion_kernel_rfl
  have kind : (ReachablePrefixTests.cells safety 3)[id.toNat].item.kind = 1 := by
    have selectedKind := congrArg (fun values => values[id.toNat]?) kinds
    simp only [List.getElem?_map, List.getElem?_eq_getElem inside, Option.map_some] at selectedKind
    rcases selected with rfl | rfl <;> exact Option.some.inj selectedKind
  have constant := constant_nonpush safety 5 (ReachablePrefixTests.cells safety 3) _ facts
    (by rw [prior.count]; decide) id inside kind
  have logical : Storage.operationProgram.run (ReachablePrefixTests.cells safety 3) id 24 = .ok none := by
    rcases selected with rfl | rfl <;> cases safety <;> insertion_kernel_rfl
  have native := (facts.native (by rw [prior.count]; decide)).operations id 24
  rw [logical] at native
  exact ⟨constant.1, constant.2, native⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveBorrowedTests
