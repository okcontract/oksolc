/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveCallTests
import Compiler.Extraction.InternerRecursiveNonemptySetupTests
import Compiler.Extraction.InternerTemporaryArguments
import Compiler.Extraction.RepresentativeConstant

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion.Native
open CallerGrowingChainTests (ops cells lifetime GraphFacts)

abbrev old (safety : Bool) := RecursiveNonemptyTests.ready safety
def rootArguments (safety : Bool) := TemporaryArguments.prepare 0 0 (old safety)
def rootSource : View := ⟨24, 0, 2⟩
def rootMemory (safety : Bool) :=
  ((Compiler.ZigAir.Memory.allocate (old safety).memory.memory (.array 2 word)).toOption.map Prod.snd).getD (old safety).memory.memory

def parent (safety : Bool) : Call := ⟨Interner.constructorCode.operationRequest 20 [0, 0], rootSource, (rootArguments safety).2⟩
def child (safety : Bool) : Call := ⟨Interner.constructorCode.constantRequest 1, ⟨0, 0, 0⟩, (parent safety).taken.2.world⟩
def selected (safety isChild : Bool) := if isChild then child safety else parent safety

attribute [local irreducible] rootArguments RecursiveNonemptyTests.ready

theorem observed (safety isChild : Bool) : (selected safety isChild).observations = (selected safety isChild).expected := by
  cases safety <;> cases isChild <;> insertion_kernel_rfl

theorem root_observed (safety : Bool) :
    (rootArguments safety).1 = .ok rootSource ∧
    (old safety).memory.memory.nextId = 24 ∧
    Compiler.ZigAir.Memory.allocate (old safety).memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨24, 0⟩, rootMemory safety) := by
  cases safety <;> exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem root_literal (safety : Bool) :
    Arguments.Prepared [0, 0] (old safety) rootSource (parent safety).before ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (parent safety).before (RecursiveNonemptyTests.rows safety) :=
  RecursiveNonemptyTests.literal_facts safety [0, 0] (old safety) (parent safety).before rootSource
    (RecursiveNonemptyTests.zero_contract safety).2.1 (by
      change TemporaryArguments.prepare 0 0 (old safety) = (.ok rootSource, (rootArguments safety).2)
      simpa only [rootArguments] using
        (Prod.ext (root_observed safety).1 rfl : rootArguments safety = (.ok rootSource, (rootArguments safety).2)))

theorem root_facts (safety : Bool) :
    Good rootSource [0, 0] (rootArguments safety).2 ∧
    GraphFacts safety ReachablePrefixTests.backing 5 (rootArguments safety).2 (RecursiveNonemptyTests.rows safety) ∧
    Good (CallerInputTests.argumentView false) [0] (rootArguments safety).2 := by
  have literal := (root_literal safety).1
  exact ⟨literal.good, (root_literal safety).2,
    good_frame _ _ _ _ (RecursiveNonemptyTests.caller_source safety) literal.good.1 literal.frame⟩

theorem parent_established (safety : Bool) : (parent safety).Established safety ReachablePrefixTests.backing 5 (RecursiveNonemptyTests.rows safety) :=
  (parent safety).establish safety ReachablePrefixTests.backing 5 (RecursiveNonemptyTests.rows safety) (root_facts safety).2.1
    (by rw [RecursiveNonemptyTests.rows_count]; decide)
    (root_facts safety).1 (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) (observed safety false)

theorem child_good (safety : Bool) : Good (child safety).source (child safety).request.arguments (child safety).before :=
  empty_good (parent safety).taken.2.world (parent_established safety).taken.valid

theorem child_established (safety : Bool) : (child safety).Established safety ReachablePrefixTests.backing 5 (RecursiveNonemptyTests.rows safety) :=
  (child safety).establish safety ReachablePrefixTests.backing 5 (RecursiveNonemptyTests.rows safety) (parent_established safety).taken
    (by rw [RecursiveNonemptyTests.rows_count]; decide)
    (child_good safety)
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) (observed safety true)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
