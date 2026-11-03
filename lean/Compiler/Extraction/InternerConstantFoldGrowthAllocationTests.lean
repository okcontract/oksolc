/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstantFoldAllocationTests
import Compiler.Extraction.InternerRecursiveGrowingPublicationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldGrowthTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops growth GraphFacts)
open RecursiveTests (Call debug)
open ConstantFoldTests

attribute [local irreducible] ConstantPublicationTests.ready rootArguments Call.constructed Call.stack

def installed (safety : Bool) (value : Word) :=
  (child safety value).installed (childObject safety value) (child safety value).clone.2

theorem installed_facts (safety : Bool) (value : Word) :
    Valid (installed safety value) ∧
    (installed safety value).memory.nextAddress = (child safety value).clone.2.memory.nextAddress := by
  have duplicated := congrArg Prod.fst (child_duplicate safety value)
  have cloned := congrArg Prod.fst (child_cloned safety value)
  have result := (child safety value).installed_facts ReachablePrefixTests.allocate safety (childObject safety value)
    (ConstantPublicationTests.rows safety value) (child safety value).normalized
    (child safety value).constructed (child safety value).taken.2
    (child safety value).duplicate.2 (child safety value).create.2 (child safety value).clone.2
    (child_established safety value).entry (Prod.ext duplicated rfl)
    (Prod.ext (child_created safety value) rfl) (Prod.ext cloned rfl)
  simpa only [installed] using result

def createdAddress (safety : Bool) := max (childScratchReference safety).nextAddress
  (((childScratchReference safety).nextAddress / AssemblyItem.Creation.layout.alignment + 1) *
    AssemblyItem.Creation.layout.alignment + AssemblyItem.Creation.layout.bytes)

theorem created_address (safety : Bool) (value : Word) :
    (child safety value).create.2.memory.nextAddress = createdAddress safety := by
  have executed : (child safety value).create = (.ok (childObject safety value), (child safety value).create.2) :=
    Prod.ext (child_created safety value) rfl
  obtain ⟨base, effects, requested, _, shape, _⟩ := AssemblyItem.Creation.create_shape (observe ops.create) 7
    (childObject safety value) (child safety value).native.item (child safety value).duplicate.2 (child safety value).create.2 executed
  have selected : base = ((child safety value).duplicate.2.memory.nextAddress / AssemblyItem.Creation.layout.alignment + 1) *
      AssemblyItem.Creation.layout.alignment := by
    exact (Option.some.inj (congrArg Prod.fst requested)).symm
  have address : (child safety value).duplicate.2.memory.nextAddress = (childScratchReference safety).nextAddress := by
    rw [child_duplicate, (child_normalized safety value).2.2.2]
    exact (child_prepared safety value).2.2.2
  rw [shape]
  change max (child safety value).duplicate.2.memory.nextAddress (base + AssemblyItem.Creation.layout.bytes) = _
  rw [selected, address]
  rfl

theorem backing_fits (safety : Bool) (value : Word) :
    Compiler.ZigAir.Memory.RegionAllocation.Fits (installed safety value).memory ⟨416, 8⟩ 8192 := by
  have current := installed_facts safety value
  have address : (installed safety value).memory.nextAddress = createdAddress safety := by
    rw [current.2, child_cloned]
    exact created_address safety value
  apply Compiler.ZigAir.Memory.RegionAllocation.fits_above _ _ _ current.1.memory (by decide) (by decide) (by decide)
  rw [address]
  cases safety <;> apply of_decide_eq_true <;> insertion_kernel_rfl

def backing (safety : Bool) (value : Word) := (child safety value).clone.2.memory.nextId
def row (safety : Bool) (value : Word) := (child safety value).publicationRow (childObject safety value)
  (child safety value).normalized (child safety value).taken.2.world
def rows (safety : Bool) (value : Word) := ConstantPublicationTests.rows safety value ++ [row safety value]
def appended (safety : Bool) (value : Word) (after : Native.Frame Nat) :=
  (child safety value).publicationWorld (ConstantPublicationTests.rows safety value) (childObject safety value)
    (child safety value).normalized (child safety value).taken.2.world after

theorem child_native (safety : Bool) (value : Word) : ∃ after,
    Native.insert ops ReachablePrefixTests.allocate safety 7 6 (child safety value).source (child safety value).address
      Insertion.Tests.model (child safety value).native (child safety value).key (child safety value).normalized true
      (some growth) (child safety value).taken.2.world = (.ok 5, appended safety value after) ∧
    GraphFacts safety (backing safety value) 13 (appended safety value after) (rows safety value) ∧
    (memory after).heap ReachablePrefixTests.backing = none ∧
    (memory after).memory.heap.lookup ReachablePrefixTests.backing = none ∧
    (memory after).effects.keys = OwnedKeys.store (child safety value).constructed.memory.effects.keys (child safety value).key
      ⟨(child safety value).normalized.address, 5⟩ ∧
    (∀ id native, (child safety value).constructed.memory.memory.heap.lookup id = some native → id ≠ 6 → id ≠ ReachablePrefixTests.backing →
      (memory after).memory.heap.lookup id = some native) ∧
    (∀ id block, (child safety value).constructed.memory.heap id = some block → id ≠ ReachablePrefixTests.backing →
      (memory after).heap id = some block) ∧
    (∀ parent, Caller.GraphCustody 7 parent (ConstantPublicationTests.rows safety value) (child safety value).constructed.memory →
      Caller.GraphCustody 7 parent (rows safety value) (memory after)) ∧
    (∀ source values, Good source values (child safety value).constructed →
      Caller.SourcePrivate source (child safety value).constructed.memory.effects.keys →
      Caller.SourcePrivate source (memory after).effects.keys) ∧
    AssemblyClone.NativeFields.Represents (memory after).memory ⟨childObject safety value, 0⟩ (child safety value).native := by
  have current := child_established safety value
  have duplicated := congrArg Prod.fst (child_duplicate safety value)
  have cloned := congrArg Prod.fst (child_cloned safety value)
  obtain ⟨after, inserted, facts, oldDead, nativeDead, keys, frame, registry, custody, privateSource, itemReads⟩ :=
    (child safety value).growing_native ReachablePrefixTests.allocate safety ReachablePrefixTests.backing 5 13
      (childObject safety value) 8192 (ConstantPublicationTests.rows safety value) (child safety value).normalized
      (child safety value).constructed (child safety value).taken.2
      (child safety value).duplicate.2 (child safety value).create.2 (child safety value).clone.2
      current.entry current.constructed current.taken (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide)
      (by decide) (by rw [ConstantPublicationTests.rows_count]; decide)
      (by rw [ConstantPublicationTests.rows_count]; decide) (by decide) (by rw [ConstantPublicationTests.rows_count]; decide)
      (Prod.ext duplicated rfl) (Prod.ext (child_created safety value) rfl) (Prod.ext cloned rfl)
      ((installed safety value).effects.allocator * 10 + 7) (by
        intro reached assigned
        have same : installed safety value = reached :=
          congrArg (fun result => result.toOption.getD (child safety value).clone.2) assigned
        rw [← same]; exact ⟨rfl, backing_fits safety value⟩)
      (child_unlocked safety value)
  refine ⟨after, ?_, facts, oldDead, nativeDead, ?_, ?_, ?_, custody, privateSource, itemReads⟩
  · simpa only [Storage.idFor, ConstantPublicationTests.rows_count] using inserted
  · simpa only [Storage.idFor, ConstantPublicationTests.rows_count] using keys
  · intro id native found ownerApart backingApart
    exact frame id native found ownerApart backingApart (by intro old _ nonempty; exact False.elim (nonempty rfl))
  · intro id block found apart
    exact registry id block found apart (by intro old _ nonempty; exact False.elim (nonempty rfl))


end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ConstantFoldGrowthTests
