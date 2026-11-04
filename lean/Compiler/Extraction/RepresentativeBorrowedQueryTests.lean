/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBorrowedQuery
import Compiler.Extraction.RepresentativeOperationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Native.Tests
open Compiler.ZigAir.Memory Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.Extraction.RepresentativeArray
open WordArray

def row := Operation.Tests.cell
def slice := row.argumentSlice
def registry : Memory.Heap := fun id =>
  if id = 0 then some ⟨7, .item row.item⟩
  else if id = 1 then some ⟨7, .arguments slice.items⟩
  else if id = 2 then some ⟨7, .representatives [row]⟩ else none
def session : Session Unit := ⟨registry, Operation.Tests.owned, ()⟩
def world : World Unit := ⟨Interner.observedHeap [row] (fun _ => none), session⟩

theorem session_valid : Valid session := by
  refine ⟨Operation.Tests.owned_valid, ?_, ?_⟩
  · intro allocator id values _ stored
    by_cases zero : id = 0
    · simp [session, registry, zero] at stored
    by_cases one : id = 1
    · subst id
      have same : 7 = allocator ∧ slice.items = values := by simpa [session, registry] using stored
      rcases same with ⟨rfl, rfl⟩
      refine ⟨⟨Expression.Tests.argumentsAllocation, by rfl', rfl, rfl, rfl⟩, rfl, ?_⟩
      intro index inside
      have bound : index < 4 := inside
      have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;> rfl'
    · by_cases two : id = 2 <;> simp [session, registry, zero, one, two] at stored
  · intro id block stored
    by_cases zero : id = 0
    · subst id; exact ⟨Operation.Tests.item, by rfl', rfl⟩
    by_cases one : id = 1
    · subst id; exact ⟨Expression.Tests.argumentsAllocation, by rfl', rfl⟩
    by_cases two : id = 2
    · subst id; exact ⟨Operation.Tests.descriptor (some (.slice Expression.argumentsType ⟨1, 0⟩ 4)), by rfl', rfl⟩
    · simp [session, registry, zero, one, two] at stored

theorem resident : Memory.GraphResident 7 session.heap [row] := by
  intro cell member; cases List.mem_singleton.mp member
  exact ⟨rfl, Or.inr rfl⟩

theorem all_queries : AcceptedQueries 7 ⟨3, 0⟩ [row] session :=
  of_resident 7 ⟨3, 0⟩ [row] session session_valid resident Operation.Tests.all_ids_and_opcodes

theorem unsorted_native_hit : Operation.run session.memory ⟨3, 0⟩ 0 12 =
    .ok (.ok (some (Operation.borrowed ⟨1, 0⟩ 4))) := by
  rw [all_queries.1]; decide +kernel

theorem unsorted_accepted_good : observe 7 0 12 world = .ok (some ⟨1, [777, 99, 1, 5]⟩) ∧
    Good (view slice) slice.items world := by
  have checked : observe 7 0 12 world = .ok (some slice) := by
    exact (all_queries.2 world.graph rfl).1 0 12
  obtain ⟨borrowed, _, found, good⟩ := (all_queries.2 world.graph rfl).2 0 12 _ unsorted_native_hit
  have same := Option.some.inj (Except.ok.inj (found.symm.trans checked))
  exact ⟨checked, same ▸ good⟩

def withArguments (cell : Compiler.ZigAir.Memory.Allocation) : World Unit :=
  { world with memory := { session with memory := { session.memory with heap := session.memory.heap.replace 1 cell } } }
def arguments := Expression.Tests.argumentsAllocation

theorem wrong_owner_rejected : observe 8 0 12 world = .error .unbacked := by decide +kernel
theorem wrong_registry_rejected : observe 7 0 12 { world with memory := { session with heap := Memory.write registry 1 (some ⟨7, .bytes 16⟩) } } =
    .error .unbacked := by decide +kernel
theorem missing_storage_rejected : observe 7 0 12 { world with memory := { session with memory := erase session.memory 1 } } =
    .error .unbacked := by decide +kernel
theorem stack_storage_rejected : observe 7 0 12 (withArguments { arguments with stack := true }) = .error .unbacked := by decide +kernel
theorem readonly_storage_rejected : observe 7 0 12 (withArguments { arguments with writable := false }) = .error .unbacked := by decide +kernel
theorem wrong_extent_rejected : observe 7 0 12 (withArguments { arguments with type := .array 5 word }) = .error .unbacked := by decide +kernel
theorem stale_contents_rejected : observe 7 0 12 (withArguments { arguments with cells := [(0, number 99), (4, number 777), (8, number 1), (12, number 5)] }) =
    .error .unbacked := by decide +kernel
theorem last_element_rejected : observe 7 0 12 (withArguments { arguments with cells := [(0, number 777), (4, number 99), (8, number 1), (12, number 6)] }) =
    .error .unbacked := by decide +kernel
theorem uninitialized_rejected : observe 7 0 12 (withArguments { arguments with cells := [] }) = .error .unbacked := by decide +kernel

/-- The native query only returns the descriptor. Corrupting the operands leaves
that hit intact but invalidates acceptance; a native hit alone proves no borrow. -/
theorem descriptor_does_not_prove_contents :
    Operation.run (withArguments { arguments with cells := [] }).memory.memory ⟨3, 0⟩ 0 12 =
      .ok (.ok (some (Operation.returned slice))) ∧
    observe 7 0 12 (withArguments { arguments with cells := [] }) = .error .unbacked := ⟨by decide +kernel, uninitialized_rejected⟩

theorem faults_and_misses :
    observe 7 99 12 world = .ok none ∧ observe 7 0 13 world = .ok none ∧
    observe 7 0 12 { world with graph := Interner.observedHeap [{ row with item := { row.item with instruction := none } }] (fun _ => none) } =
      .error (.query .invalidOptional) ∧
    Operation.Tests.query (Operation.Tests.state 1 (some none) none) = .ok (.error .invalidOptional) := by
  exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem empty_sentinel (address : Nat) : checkSlice 7 ⟨address, []⟩ session = true := rfl

/-- Interior source views are preserved by the native reader. This owned-row
bridge does not silently rebase that view into a registered full allocation. -/
theorem offset_scope : Operation.Tests.query = .ok (.ok (some (Operation.borrowed ⟨1, 4⟩ 2))) ∧
    Operation.borrowed ⟨1, 4⟩ 2 ≠ Operation.returned ⟨1, [99, 1]⟩ := ⟨Operation.Tests.offset_descriptor, by decide⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.BorrowedQuery.Native.Tests
