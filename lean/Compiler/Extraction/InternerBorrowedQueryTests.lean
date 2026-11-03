/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerBorrowedQuery
import Compiler.Extraction.InternerInsertionCallerTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray

def allocation : Compiler.ZigAir.Memory.Allocation :=
  ⟨4, .array 2 word, [(0, number 3), (4, number 1)], true, false⟩
def initial : Session Unit :=
  ⟨fun id => if id = 0 then some ⟨7, .arguments [3, 1]⟩ else none, ⟨[(0, allocation)], 1, 12⟩, ()⟩
def input : ArgumentSlice := ⟨0, [3, 1]⟩
def withCell (cell : Compiler.ZigAir.Memory.Allocation) : Session Unit :=
  { initial with memory := { initial.memory with heap := [(0, cell)] } }

theorem slice_accepted : checkSlice 7 input initial = true := by rfl'
theorem empty_without_sentinel (address : Nat) : checkSlice 7 ⟨address, []⟩ initial = true := rfl
theorem wrong_owner_rejected : checkSlice 8 input initial = false := by rfl'
theorem wrong_address_rejected : checkSlice 7 ⟨999, [3, 1]⟩ initial = false := by rfl'
theorem wrong_block_rejected : checkSlice 7 input { initial with heap := fun _ => some ⟨7, .bytes 8⟩ } = false := by rfl'
theorem missing_storage_rejected : checkSlice 7 input { initial with memory := { initial.memory with heap := [] } } = false := by rfl'
theorem stack_storage_rejected : checkSlice 7 input (withCell { allocation with stack := true }) = false := by rfl'
theorem readonly_storage_rejected : checkSlice 7 input (withCell { allocation with writable := false }) = false := by rfl'
theorem wrong_extent_rejected : checkSlice 7 input (withCell { allocation with type := .array 3 word }) = false := by rfl'
theorem stale_contents_rejected : checkSlice 7 input (withCell { allocation with cells := [(0, number 1), (4, number 3)] }) = false := by rfl'
theorem last_element_rejected : checkSlice 7 input (withCell { allocation with cells := [(0, number 3), (4, number 2)] }) = false := by rfl'
theorem uninitialized_rejected : checkSlice 7 input (withCell { allocation with cells := [] }) = false := by rfl'

def cell : Storage.Cell := { item := ⟨1, some 1, 0⟩, otherValue := 42, itemAddress := 0, arguments := input.items, argumentsAddress := input.address }
def world : World Unit := ⟨Interner.observedHeap [cell] (fun _ => none), initial⟩

theorem query_accepted : observe 7 0 1 world = .ok (some input) := by rfl'
theorem query_misses : observe 7 99 1 world = .ok none ∧ observe 7 0 20 world = .ok none := ⟨by rfl', by rfl'⟩
theorem absent_graph_rejected : observe 7 0 1 { world with graph := { world.graph with representatives := none } } = .error (.query .safetyFault) := rfl
theorem malformed_query_rejected :
    observe 7 0 1 { world with graph := Interner.observedHeap [{ cell with item := ⟨1, none, 0⟩ }] (fun _ => none) } =
      .error (.query .invalidOptional) := by rfl'
theorem unbacked_query_rejected : observe 8 0 1 world = .error .unbacked := by rfl'

/-- The input is the actual reached world of the complete production insertion
fixture, including its argument duplicate, publication and deferred cleanup.
The next call borrows the newly inserted representative's own allocation. -/
def produced : World (Publication.Effects Nat) := Insertion.CallerTests.found.2.world
def producedSlice : ArgumentSlice := ⟨6, [1, 3]⟩

theorem inserted_query_accepted : observe 7 5 1 produced = .ok (some producedSlice) := by rfl'
theorem produced_valid : Valid produced.memory := by
  unfold produced
  obtain ⟨⟨memory, _⟩, _, _, _, _⟩ := Insertion.CallerTests.find_closed
  exact memory
theorem produced_graph : Interner.Invariant Insertion.Tests.model produced.graph := by
  unfold produced
  obtain ⟨_, _, graph, _, _⟩ := Insertion.CallerTests.find_closed
  exact graph
theorem inserted_query_good : Good (view producedSlice) producedSlice.items produced :=
  accepted_good 7 5 1 produced producedSlice produced_valid inserted_query_accepted

def callbacks (failure : Option Storage.Allocation) := Insertion.graphCallbacks (Insertion.CallerTests.ops failure)
  7 (view producedSlice) Insertion.Tests.model Insertion.CallerTests.select Insertion.CallerTests.seed

theorem contracts (failure : Option Storage.Allocation) :
    OwnedCall.Contracts 7 (view producedSlice) producedSlice.items (callbacks failure) ∧
    Semantic.Contracts 7 (view producedSlice) producedSlice.items Insertion.Tests.model (callbacks failure) := by
  have graph := Insertion.graph_contracts (Insertion.CallerTests.ops failure) 7 (view producedSlice) producedSlice.items
    Insertion.Tests.model Insertion.CallerTests.select Insertion.CallerTests.seed (Insertion.Tests.admitted failure)
  refine ⟨⟨graph.1, ?_⟩, ⟨graph.2, ?_⟩⟩
  · intro _ _ _ _ held _; exact held
  · intro _ _ before _ _ _ _ valid _
    exact Semantic.Ensures.pure Insertion.Tests.model before.graph none _ valid (fun _ impossible => by cases impossible)

def temporary : Recursive.Find (Publication.Effects Nat) := fun _ before => (.error (.language .unsupported), before)
def run (failure : Option Storage.Allocation := none) (budget : Nat := 160) (opcode : Opcode := 20) :
    Except Fault NodeId × World (Publication.Effects Nat) :=
  (Recursive.constructors temporary (Recursive.BorrowedConstructor.caller
    (Publication.external (Insertion.CallerTests.ops failure).arguments) budget 7 (callbacks failure) Interner.Queries.queries)).borrowedOperation
    producedSlice.address opcode producedSlice.items () produced

theorem production_contract (failure : Option Storage.Allocation) (budget : Nat) :
    ordinary (run failure budget).1 = true → Good (view producedSlice) producedSlice.items (run failure budget).2 ∧
      Closed (ConstructorFrame.operation (Publication.external (Insertion.CallerTests.ops failure).arguments) budget 7
        (callbacks failure) Interner.Queries.queries (view producedSlice) 20 producedSlice.items produced).2.scope ∧
      Semantic.Ensures Insertion.Tests.model produced.graph (run failure budget).1 (run failure budget).2.graph
        (fun id after => after.read id = some 0) :=
  operation_verified temporary (Publication.external (Insertion.CallerTests.ops failure).arguments) budget 7 (callbacks failure)
    5 1 20 producedSlice () produced Insertion.Tests.base 0 produced_valid inserted_query_accepted
    (Publication.external_admitted _ (Insertion.Tests.admitted failure)) (contracts failure).1 (contracts failure).2
    produced_graph (by rfl')

theorem success_observation : (run).1 = .ok 6 ∧ (run).2.graph.read 6 = some 0 ∧
    observe 7 5 1 (run).2 = .ok (some producedSlice) := ⟨by rfl', by rfl', by rfl'⟩
theorem failure_observation : (run (some .publish)).1 = .error (.language .outOfMemory) ∧
    (run (some .publish)).2.graph.representatives = produced.graph.representatives ∧
    observe 7 5 1 (run (some .publish)).2 = .ok (some producedSlice) := ⟨by rfl', by rfl', by rfl'⟩
theorem zero_budget_without_swaps : (run none 0).1 = .ok 6 ∧
    ((run none 0).2.memory.memory.heap.lookup produced.memory.memory.nextId).isSome = false := ⟨by rfl', by rfl'⟩
def unsorted : World (Publication.Effects Nat) :=
  (Caller.find (Publication.external (Insertion.CallerTests.ops).arguments) 160 7 (Insertion.CallerTests.actual)
    Interner.Queries.queries Insertion.CallerTests.source Insertion.CallerTests.buffer
    { Insertion.CallerTests.request with item := ⟨1, some 3, 0⟩ } Insertion.CallerTests.world).2.world
def unsortedSlice : ArgumentSlice := ⟨5, [3, 1]⟩
def faulted : Except Fault NodeId × World (Publication.Effects Nat) :=
  Recursive.BorrowedConstructor.caller (Publication.external (Insertion.CallerTests.ops).arguments) 0 7
    (Insertion.graphCallbacks (Insertion.CallerTests.ops) 7 (view unsortedSlice) Insertion.Tests.model
      Insertion.CallerTests.select Insertion.CallerTests.seed) Interner.Queries.queries
    (view unsortedSlice) (Interner.constructorCode.operationRequest 1 unsortedSlice.items) unsorted

theorem unsorted_query_accepted : observe 7 5 3 unsorted = .ok (some unsortedSlice) := by rfl'
theorem semantic_fault_retained : faulted.1 = .error (.memory (.preparation .incomplete)) ∧
    (faulted.2.memory.memory.heap.lookup unsorted.memory.memory.nextId).isSome = true := ⟨by rfl', by rfl'⟩
theorem success_verified : Good (view producedSlice) producedSlice.items (run).2 :=
  (production_contract none 160 (by rw [success_observation.1]; rfl)).1
theorem failure_verified : Good (view producedSlice) producedSlice.items (run (some .publish)).2 :=
  (production_contract (some .publish) 160 (by rw [failure_observation.1]; rfl)).1

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Tests
