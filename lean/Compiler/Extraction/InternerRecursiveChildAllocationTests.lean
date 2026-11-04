/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveChildSetupTests
import Compiler.Extraction.InternerCallerInsertionGrowthAllocationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime growth releaseBacking GraphFacts)

attribute [local irreducible] rootArguments RecursiveNonemptyTests.ready

def failing : Backing.Registry.Allocate Nat := ReachablePrefixTests.firstOnly
def childObject (safety : Bool) := (child safety).before.memory.memory.nextId + 2
def childHandle (safety : Bool) : Handle := ⟨view (child safety).normalized, [], none⟩
def duplicated (safety : Bool) := takeOwned normalizationOwnershipCode (Publication.external ops.arguments) 7
  (childHandle safety) (child safety).taken.2.world.memory
def created (safety : Bool) := AssemblyItem.Creation.create (observe ops.create) 7 (child safety).native.item (duplicated safety).2
def cloned (safety : Bool) := AssemblyClone.Physical.run (observe ops.copy) 7 (child safety).native (created safety).2
def installed (safety : Bool) :=
  ((AssemblyClone.NativeFields.install (child safety).native (childObject safety) (cloned safety).2).toOption).getD (cloned safety).2
def executed (safety : Bool) := Native.execution ops failing safety 7 6 (child safety).source (child safety).address
  Insertion.Tests.model (child safety).native (child safety).key (child safety).normalized true
  (RecursiveNonemptyTests.rows safety) (child safety).taken.2.world (some growth)

def preparationObservations (safety : Bool) := ((duplicated safety).1, (created safety).1, (cloned safety).1)
def preparationExpected (safety : Bool) :=
  ((Except.ok ((child safety).normalized, childHandle safety) : Except Failure (ArgumentSlice × Handle)),
    (Except.ok (childObject safety) : Except AssemblyItem.Creation.Fault Nat),
    (Except.ok (child safety).native : Except AssemblyClone.Physical.Fault AssemblyClone.NativeFields.ItemValue))

theorem preparation_observed (safety : Bool) : preparationObservations safety = preparationExpected safety := by
  cases safety <;> insertion_kernel_rfl

theorem preparation_results (safety : Bool) :
    duplicated safety = (.ok ((child safety).normalized, childHandle safety), (duplicated safety).2) ∧
    created safety = (.ok (childObject safety), (created safety).2) ∧
    cloned safety = (.ok (child safety).native, (cloned safety).2) := by
  have calls := preparation_observed safety
  simp only [preparationObservations, preparationExpected, Prod.mk.injEq] at calls
  exact ⟨Prod.ext calls.1 rfl, Prod.ext calls.2.1 rfl, Prod.ext calls.2.2 rfl⟩

/-- Initial canonical reads belong to the initialized prefix, before either
recursive frame. Subsequent equalities use proved graph frames. -/
theorem initial_reads (safety : Bool) : (old safety).graph.read = Storage.readValue (RecursiveNonemptyTests.rows safety) :=
  (RecursiveNonemptyTests.zero_contract safety).2.2.2.1

theorem root_graph (safety : Bool) : (rootArguments safety).2.graph = (old safety).graph :=
  (root_literal safety).1.graph

theorem child_reads (safety : Bool) : (child safety).taken.2.world.graph.read = Storage.readValue (RecursiveNonemptyTests.rows safety) := by
  rw [(child_established safety).entry.origin.graph, (child_established safety).item.graph]
  change (parent safety).taken.2.world.graph.read = _
  rw [(parent_established safety).entry.origin.graph, (parent_established safety).item.graph]
  change (rootArguments safety).2.graph.read = _
  rw [root_graph, initial_reads]

/-- All child failure owners and old-allocation frames come from the same
native duplicate/create/clone/growth execution, including the empty slice guard. -/
theorem child_allocation (safety : Bool) : ∃ after,
    executed safety = ((.ok (some .allocationFailure), closed), after) ∧
    Valid (memory after) ∧
    (memory after).memory.nextId = (cloned safety).2.memory.nextId ∧
    (memory after).memory.nextAddress = (cloned safety).2.memory.nextAddress ∧
    (memory after).effects.keys = (child safety).constructed.memory.effects.keys ∧
    (∀ id native, (child safety).constructed.memory.memory.heap.lookup id = some native →
      (memory after).memory.heap.lookup id = some native) ∧
    (∀ id block, (child safety).constructed.memory.heap id = some block → (memory after).heap id = some block) ∧
    (memory after).heap (childObject safety) = none ∧ (memory after).memory.heap.lookup (childObject safety) = none := by
  have established := child_established safety
  have calls := preparation_results safety
  obtain ⟨owner, found, typed, _⟩ := established.constructed.owner
  obtain ⟨after, ran, valid, nextId, nextAddress, keys, _, _, _, _, _, native, registry, released⟩ :=
    established.entry.growing_allocation_oom ops failing releaseBacking safety 7 6 ReachablePrefixTests.backing 5 13 (childObject safety) 17 23 owner
      (child safety).source (child safety).address Insertion.Tests.model (child safety).request (child safety).request.arguments
      (child safety).native (child safety).native (child safety).key (child safety).normalized (child safety).normalized
      (child safety).lookup (childHandle safety) (child safety).constructed (child safety).taken.2
      (RecursiveNonemptyTests.rows safety) (duplicated safety).2 (created safety).2 (cloned safety).2
      (Normalization.Tests.external_admitted _) established.constructed.valid found typed established.constructed.owned
      (readHeader_items _ _ _ _ established.constructed.header) established.constructed.capacity_read established.constructed.live
      (by decide) (by rw [RecursiveNonemptyTests.rows_count]; decide) (by rw [RecursiveNonemptyTests.rows_count]; decide) (by decide) (by rw [RecursiveNonemptyTests.rows_count]; decide)
      calls.1 calls.2.1 calls.2.2 ((installed safety).effects.allocator * 10 + 7) (by
        intro ready assigned
        have same : installed safety = ready := by simp only [installed, assigned, Except.toOption, Option.getD_some]
        rw [← same]; rfl) (by cases safety <;> insertion_kernel_rfl)
  exact ⟨after, ran, valid, nextId, nextAddress, keys, native, registry, released _ (Or.inl rfl)⟩

def failedWorld (safety : Bool) (after : Native.Frame Nat) := { (child safety).taken.2.world with memory := memory after }

/-- Checked native insertion uses the actual initialized container count and
the same execution. Failure cannot publish a row or reset the graph cursor. -/
theorem child_insert (safety : Bool) (after : Native.Frame Nat)
    (ran : executed safety = ((.ok (some .allocationFailure), closed), after)) :
    Native.insert ops failing safety 7 6 (child safety).source (child safety).address Insertion.Tests.model
      (child safety).native (child safety).key (child safety).normalized true (some growth) (child safety).taken.2.world =
        (.error (.language .outOfMemory), failedWorld safety after) := by
  have established := child_established safety
  obtain ⟨owner, found, _, _⟩ := established.constructed.owner
  have checked := established.entry.checked_execution ops failing safety 7 6 (child safety).source (child safety).address Insertion.Tests.model
    (child safety).request (child safety).request.arguments (child safety).native (child safety).key (child safety).normalized
    (child safety).lookup (child safety).constructed (child safety).taken.2 true (RecursiveNonemptyTests.rows safety) (some growth) owner ⟨ReachablePrefixTests.backing, 0⟩
    found (readHeader_items _ _ _ _ established.constructed.header)
  change checkedExecution _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = .ok (executed safety) at checked
  rw [ran] at checked
  have projection := projected_unchanged (RecursiveNonemptyTests.rows safety) (child safety).taken.2.world (child safety).key
    (cell (child safety).native (child safety).key (child safety).normalized
      (((child safety).key.eval Insertion.Tests.model (child safety).taken.2.world.graph.read).getD 0) closed after)
    closed after established.taken.projected (child_reads safety) rfl rfl
  simp only [Native.insert, established.taken.projected, Native.body, checked, projection, Interner.insertionOutcome, Except.mapError]
  rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveTests
