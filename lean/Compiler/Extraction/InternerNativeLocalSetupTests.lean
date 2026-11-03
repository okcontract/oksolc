/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeLocal
import Compiler.Extraction.InternerNativeRecursionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (lifetime GraphFacts)
open RecursiveTests (Call debug)
open RecursiveBorrowedTests (childContext)

def program (safety : Bool) (depth : Nat) : Except Fault NodeId × World (Publication.Effects Nat) :=
  (do let _ ← ReachablePrefixTests.sequence (NativeRecursion.unfold (childContext safety) 6 64 depth) 3
      let id ← (NativeRecursion.unfold (childContext safety) 6 64 depth).operation 22 [0, 1] debug
      (NativeRecursion.unfold (childContext safety) 6 64 depth).operation 22 [0, id] debug)
    (CallerInputTests.world safety)

/-- Two constructor layers suffice: AND publication, then the actual named
copy/overwrite branch and a complete cache-hit child. Deeper callbacks are not
visited. This is a specialization of the existing recursive family. -/
def observed (safety : Bool) := program safety 2

def rootArguments (safety : Bool) := Arguments.prepare [0, 4] (BinaryPreludeTests.ready safety false)
def rootSource : View := ⟨27, 0, 2⟩
def parent (safety : Bool) : Call :=
  ⟨Interner.constructorCode.operationRequest 22 [0, 4], rootSource, (rootArguments safety).2⟩
def localSource : View := ⟨31, 0, 2⟩
def copied (safety : Bool) := LocalArguments.zigLocal (view BinaryPreludeTests.operands) 0 0 true (parent safety).taken.2.world

attribute [local irreducible] BinaryPreludeTests.ready rootArguments copied

theorem parent_observed (safety : Bool) :
    (rootArguments safety).1 = .ok rootSource ∧
    (parent safety).observations = (parent safety).expected ∧
    (copied safety).1 = .ok localSource := by
  cases safety <;> refine ⟨?_, ?_, ?_⟩ <;> insertion_kernel_rfl

theorem parent_established (safety : Bool) :
    (parent safety).Established safety ReachablePrefixTests.backing 5 (BinaryPreludeTests.rows safety false) := by
  have prior := BinaryPreludeTests.contract safety false
  have literal : Arguments.prepare [0, 4] (BinaryPreludeTests.ready safety false) =
      (.ok rootSource, (parent safety).before) := by
    simpa only [parent, rootArguments] using
      (Prod.ext (parent_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2))
  have ready := BinaryPreludeTests.literal_facts safety 5 _ _ _ _ _ prior.2.1
    (by rw [BinaryPreludeTests.rows_count]; decide) literal
  exact (parent safety).establish safety ReachablePrefixTests.backing 5 _ ready.2
    (by rw [BinaryPreludeTests.rows_count]; decide) ready.1.good
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (parent_observed safety).2.1

theorem source_query (safety : Bool) :
    (Interner.representativeReads (parent safety).taken.2.world.graph).operation 4 22 =
      .ok (some BinaryPreludeTests.operands) ∧
    Nested.repeatedIndex (Interner.representativeReads (parent safety).taken.2.world.graph) 0 1 0 = some 0 := by
  have facts := (parent_established safety).taken
  simp only [Interner.representativeReads, facts.projected, Nested.storageReads]
  cases safety <;> constructor <;> insertion_kernel_rfl

theorem local_input (safety : Bool) (depth : Nat) :
    Arguments.Prepared [0, 1] (parent safety).taken.2.world localSource (copied safety).2 ∧
    NativeGraph.Facts safety 7 6 ⟨ReachablePrefixTests.backing, 0⟩ 5 (copied safety).2 (BinaryPreludeTests.rows safety false) ∧
    run (childContext safety) 6 64 (depth + 1) 22 4 0 true debug (parent safety).taken.2.world =
      (let called := TemporaryArguments.unwind (parent safety).taken.2.world.memory.memory.nextId
        (operation (childContext safety).external (childContext safety).budget 7
          ((NativeRecursion.context (childContext safety) 6 64
            (NativeRecursion.unfold (childContext safety) 6 64 depth) debug).primitives localSource)
          (childContext safety).queries localSource 22 [0, 1] debug (copied safety).2)
       (called.1.map some, called.2)) ∧
    Operation.run (parent safety).taken.2.world.memory.memory (Owner.headerAddress ⟨6, 0⟩) 4 22 =
      .ok (.ok (some (Operation.returned BinaryPreludeTests.operands))) ∧
    ShiftInput.operand (view BinaryPreludeTests.operands) 1 (parent safety).taken.2.world = (.ok 1, (parent safety).taken.2.world) ∧
    ShiftInput.operand (view BinaryPreludeTests.operands) 0 (parent safety).taken.2.world = (.ok 0, (parent safety).taken.2.world) := by
  have connected := input_contract (childContext safety) 64 depth 22 4 0 0 1 true debug (parent safety).taken.2.world
    BinaryPreludeTests.operands 0 safety 6 5 ⟨ReachablePrefixTests.backing, 0⟩ (BinaryPreludeTests.rows safety false)
    ((parent_established safety).taken.native (by rw [BinaryPreludeTests.rows_count]; decide))
    (source_query safety).1 rfl (source_query safety).2
  have prepared : LocalArguments.zigLocal (view BinaryPreludeTests.operands) 0 0 true (parent safety).taken.2.world =
      (.ok localSource, (copied safety).2) := by
    simpa only [copied] using
      (Prod.ext (parent_observed safety).2.2 rfl : copied safety = (.ok localSource, (copied safety).2))
  rw [prepared] at connected
  exact ⟨connected.2.2.2.2.2.1, connected.2.2.2.2.2.2.1, connected.2.2.2.2.2.2.2.2, connected.1, connected.2.2.1, connected.2.2.2.1⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeLocal.Tests
