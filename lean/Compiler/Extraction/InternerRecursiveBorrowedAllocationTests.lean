/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveBorrowedInputTests
import Compiler.Extraction.InternerCallerInsertionGrowthAllocationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveBorrowedTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (ops cells lifetime growth releaseBacking GraphFacts)
open RecursiveTests (Call debug)

/-- The same allocator admits initialization, then rejects the required growth. -/
def failing : Backing.Registry.Allocate Nat := ReachablePrefixTests.firstOnly
def childObject (safety : Bool) := (child safety).before.memory.memory.nextId + 4
def childOperands (safety : Bool) : ArgumentSlice := ⟨(child safety).before.memory.memory.nextId + 3, [0, 1]⟩
def childHandle (safety : Bool) : Handle := ⟨view (child safety).normalized, [0, 1], none⟩
def childDuplicated (safety : Bool) := (child safety).duplicate
def childCreated (safety : Bool) := (child safety).create
def childCloned (safety : Bool) := (child safety).clone
def childInstalled (safety : Bool) := (child safety).installed (childObject safety) (childCloned safety).2
def executed (safety : Bool) := Native.execution ops failing safety 7 6 (child safety).source (child safety).address
  Insertion.Tests.model (child safety).native (child safety).key (child safety).normalized true
  (rows safety) (child safety).taken.2.world (some growth)
def closed := (Storage.Cleanup.sequence [.value, .allocation, .arguments, .normalized]).run preparationOwnership

def preparationObservations (safety : Bool) := ((childDuplicated safety).1, (childCreated safety).1, (childCloned safety).1)
def preparationExpected (safety : Bool) :=
  ((Except.ok (childOperands safety, childHandle safety) : Except Failure (ArgumentSlice × Handle)),
    (Except.ok (childObject safety) : Except AssemblyItem.Creation.Fault Nat),
    (Except.ok (child safety).native : Except AssemblyClone.Physical.Fault AssemblyClone.NativeFields.ItemValue))

theorem preparation_observed (safety : Bool) : preparationObservations safety = preparationExpected safety := by
  cases safety <;> insertion_kernel_rfl

theorem preparation_results (safety : Bool) :
    childDuplicated safety = (.ok (childOperands safety, childHandle safety), (childDuplicated safety).2) ∧
    childCreated safety = (.ok (childObject safety), (childCreated safety).2) ∧
    childCloned safety = (.ok (child safety).native, (childCloned safety).2) := by
  have calls := preparation_observed safety
  simp only [preparationObservations, preparationExpected, Prod.mk.injEq] at calls
  exact ⟨Prod.ext calls.1 rfl, Prod.ext calls.2.1 rfl, Prod.ext calls.2.2 rfl⟩

/-- All child failure owners and old-allocation frames come from the same
native duplicate/create/clone/growth execution, including both distinct nonempty argument owners. The borrowed graph input
is an older persistent allocation and is excluded from those owners. -/
theorem child_allocation (safety : Bool) : ∃ after,
    executed safety = ((.ok (some .allocationFailure), closed), after) ∧
    Valid (memory after) ∧
    (memory after).memory.nextId = (childCloned safety).2.memory.nextId ∧
    (memory after).memory.nextAddress = (childCloned safety).2.memory.nextAddress ∧
    (memory after).effects.keys = (child safety).constructed.memory.effects.keys ∧
    (∀ id native, (child safety).constructed.memory.memory.heap.lookup id = some native →
      (memory after).memory.heap.lookup id = some native) ∧
    (∀ id block, (child safety).constructed.memory.heap id = some block → (memory after).heap id = some block) ∧
    (∀ id, id = childObject safety ∨ id = (childOperands safety).address ∨ id = (child safety).normalized.address →
      (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  have established := child_established safety
  have calls := preparation_results safety
  obtain ⟨owner, found, typed, _⟩ := established.constructed.owner
  obtain ⟨after, ran, valid, nextId, nextAddress, keys, _, _, _, _, _, native, registry, released⟩ :=
    established.entry.growing_allocation_oom ops failing releaseBacking safety 7 6 ReachablePrefixTests.backing 5 13 (childObject safety) 17 23 owner
      (child safety).source (child safety).address Insertion.Tests.model (child safety).request (child safety).request.arguments
      (child safety).native (child safety).native (child safety).key (child safety).normalized (childOperands safety)
      (child safety).lookup (childHandle safety) (child safety).constructed (child safety).taken.2
      (rows safety) (childDuplicated safety).2 (childCreated safety).2 (childCloned safety).2
      (Normalization.Tests.external_admitted _) established.constructed.valid found typed established.constructed.owned
      (readHeader_items _ _ _ _ established.constructed.header) established.constructed.capacity_read established.constructed.live
      (by decide) (by rw [rows_count]; decide) (by rw [rows_count]; decide) (by decide) (by rw [rows_count]; decide)
      calls.1 calls.2.1 calls.2.2 ((childInstalled safety).effects.allocator * 10 + 7) (by
        intro ready assigned
        have same : childInstalled safety = ready := congrArg (fun result => result.toOption.getD (childCloned safety).2) assigned
        rw [← same]; rfl) (by cases safety <;> insertion_kernel_rfl)
  refine ⟨after, ran, valid, nextId, nextAddress, keys, native, registry, ?_⟩
  intro id selected
  rcases selected with object | operands | normalized
  · exact released id (Or.inl object)
  · exact released id (Or.inr (Or.inr (Or.inl ⟨by change [0, 1] ≠ []; decide, operands⟩)))
  · exact released id (Or.inr (Or.inr (Or.inr ⟨by change [0, 1] ≠ []; decide, normalized⟩)))

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
    (child safety).lookup (child safety).constructed (child safety).taken.2 true (rows safety) (some growth) owner ⟨ReachablePrefixTests.backing, 0⟩
    found (readHeader_items _ _ _ _ established.constructed.header)
  change checkedExecution _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = .ok (executed safety) at checked
  rw [ran] at checked
  have projection := projected_unchanged (rows safety) (child safety).taken.2.world (child safety).key
    (cell (child safety).native (child safety).key (child safety).normalized
      (((child safety).key.eval Insertion.Tests.model (child safety).taken.2.world.graph.read).getD 0) closed after)
    closed after established.taken.projected (graph_reads safety).2 rfl rfl
  simp only [Native.insert, established.taken.projected, Native.body, checked, projection, Interner.insertionOutcome, Except.mapError]
  rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.RecursiveBorrowedTests
