/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeConstantTests
import Compiler.Extraction.InternerRecursiveGrowingPublicationTests
import Compiler.Extraction.InternerNativePublishedCompletion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops lifetime growth releaseBacking GraphFacts)
open RecursiveTests (Call debug)
open RecursiveNonemptyTests

attribute [local irreducible] ready rootArguments childArguments

def backing (safety : Bool) := (childCloned safety).2.memory.nextId
def row (safety : Bool) := (child safety).publicationRow (childObject safety) (childOperands safety) (child safety).taken.2.world
def appendedRows (safety : Bool) := rows safety ++ [row safety]
def appendedWorld (safety : Bool) (after : Native.Frame Nat) :=
  (child safety).publicationWorld (rows safety) (childObject safety) (childOperands safety) (child safety).taken.2.world after

/-- Allocation fit is established from the actual duplicate/create/clone
execution and its high-water mark, rather than assumed from the host response. -/
theorem installed_valid (safety : Bool) : Valid (childInstalled safety) := by
  have calls := preparation_results safety
  have result := (child safety).installed_facts ReachablePrefixTests.allocate safety (childObject safety)
    (rows safety) (childOperands safety) (child safety).constructed (child safety).taken.2
    (childDuplicated safety).2 (childCreated safety).2 (childCloned safety).2
    (child_established safety).entry calls.1 calls.2.1 calls.2.2
  exact result.1

theorem backing_fits (safety : Bool) : Compiler.ZigAir.Memory.RegionAllocation.Fits (childInstalled safety).memory ⟨416, 8⟩ 8192 := by
  have valid := (installed_valid safety).memory
  have observed : decide ((childInstalled safety).memory.nextAddress ≤ 8192) = true := by
    cases safety <;> insertion_kernel_rfl
  have bound := of_decide_eq_true observed
  exact Compiler.ZigAir.Memory.RegionAllocation.fits_above _ _ _ valid (by decide) (by decide) (by decide) bound

/-- Feed the existing duplicate/create/clone observations to the general
source-selected completion. No final graph or parent frame is observed here. -/
theorem child_published (safety : Bool) :
    Native.RelocatedPublished ops ReachablePrefixTests.allocate safety 7 6 Insertion.Tests.model
      (child safety).native (child safety).key (child safety).normalized (some growth) (child safety).taken.2.world := by
  have calls := preparation_results safety
  have facts := (child_established safety).taken
  let probeEffects := (memory (append safety ReachablePrefixTests.allocate 7 6 (rows safety)
    (child safety).native (child safety).key (child safety).normalized
    (((child safety).key.eval Insertion.Tests.model (child safety).taken.2.world.graph.read).getD 0)
    preparationOwnership (preparedFrame (childObject safety) (child safety).native (childOperands safety)
      (childInstalled safety)) (some growth)).2).effects.allocator * 10 + 8
  refine ⟨(by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide), 5, 13,
    facts.capacity_read, (by decide), ?_, ?_, (by decide), 17, 23, releaseBacking, rfl,
    childOperands safety, ⟨view (child safety).normalized, (child safety).normalized.items, none⟩,
    (childDuplicated safety).2, childObject safety, (childCreated safety).2, (child safety).native,
    (childCloned safety).2, 8192, (childInstalled safety).effects.allocator * 10 + 7,
    probeEffects, calls.1, calls.2.1, calls.2.2, ?_, ?_, ?_⟩
  · rw [facts.projected]; simp only [Option.getD_some, rows_count]; decide
  · rw [facts.projected]; simp only [Option.getD_some, rows_count]; decide
  · intro installed assigned
    have same : childInstalled safety = installed := by simp only [childInstalled, assigned, Except.toOption, Option.getD_some]
    rw [← same]; exact ⟨rfl, backing_fits safety⟩
  · intro installed assigned
    have same : childInstalled safety = installed := by simp only [childInstalled, assigned, Except.toOption, Option.getD_some]
    rw [← same, facts.projected]
    rfl
  · cases safety <;> insertion_kernel_rfl

/-- The child publishes a sixth representative after real nonempty relocation.
Graph facts, retirement, key ownership and the selective native/registry frame
are all conclusions of the production growth and publication execution. -/
theorem child_native (safety : Bool) : ∃ after,
    Native.insert ops ReachablePrefixTests.allocate safety 7 6 childSource (child safety).address Insertion.Tests.model
      (child safety).native (child safety).key (child safety).normalized true (some growth) (child safety).taken.2.world =
        (.ok 5, appendedWorld safety after) ∧
    GraphFacts safety (backing safety) 13 (appendedWorld safety after) (appendedRows safety) ∧
    (memory after).heap ReachablePrefixTests.backing = none ∧ (memory after).memory.heap.lookup ReachablePrefixTests.backing = none ∧
    (memory after).effects.keys = OwnedKeys.store (child safety).constructed.memory.effects.keys (child safety).key
      ⟨(child safety).normalized.address, 5⟩ ∧
    (∀ id native, (child safety).constructed.memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ ReachablePrefixTests.backing →
      (∀ old, (child safety).constructed.memory.effects.keys (child safety).key = some old →
        (child safety).key.arguments ≠ [] → id ≠ old.address) → (memory after).memory.heap.lookup id = some native) ∧
    (∀ id block, (child safety).constructed.memory.heap id = some block → id ≠ ReachablePrefixTests.backing →
      (∀ old, (child safety).constructed.memory.effects.keys (child safety).key = some old →
        (child safety).key.arguments ≠ [] → id ≠ old.address) → (memory after).heap id = some block) ∧
    (∀ parent, Caller.GraphCustody 7 parent (rows safety) (child safety).constructed.memory →
      Caller.GraphCustody 7 parent (appendedRows safety) (memory after)) ∧
    (∀ source values, Good source values (child safety).constructed →
      Caller.SourcePrivate source (child safety).constructed.memory.effects.keys →
      Caller.SourcePrivate source (memory after).effects.keys) := by
  have established := child_established safety
  have calls := preparation_results safety
  obtain ⟨after, inserted, facts, oldDead, nativeDead, keys, frame, registry, custody, privateSource, _⟩ :=
    (child safety).growing_native ReachablePrefixTests.allocate safety ReachablePrefixTests.backing 5 13
      (childObject safety) 8192 (rows safety) (childOperands safety) (child safety).constructed (child safety).taken.2
      (childDuplicated safety).2 (childCreated safety).2 (childCloned safety).2
      established.entry established.constructed established.taken
      (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide)
      (by decide) (by rw [rows_count]; decide) (by rw [rows_count]; decide) (by decide) (by rw [rows_count]; decide)
      calls.1 calls.2.1 calls.2.2 ((childInstalled safety).effects.allocator * 10 + 7) (by
        intro installed assigned
        have same : childInstalled safety = installed := by simp only [childInstalled, assigned, Except.toOption, Option.getD_some]
        rw [← same]; exact ⟨rfl, backing_fits safety⟩)
      (by cases safety <;> insertion_kernel_rfl)
  refine ⟨after, ?_, facts, oldDead, nativeDead, ?_, frame, registry, custody, privateSource⟩
  · simpa only [Storage.idFor, rows_count] using inserted
  · simpa only [Storage.idFor, rows_count] using keys

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveGrowthTests
