/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphFrame
import Compiler.Extraction.InternerGraphInitOwnershipTests
import Compiler.Extraction.InternerNativeRecursionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open GraphInit.OwnerMemory.Tests (before ownerCell sentinel initial_valid)
open GraphInit.Ownership.Tests (owned source_initializer)
open ConstructorItem
open Insertion.Native.CallerGrowingChainTests (lifetime)
open RecursiveBorrowedTests (rows rows_count childSource rootSource parent)
open NativeRecursion.Tests (program program_contract)

attribute [local irreducible] program

theorem initialized_from_execution (safety : Bool) (meaning : Meaning) :
    Facts safety 7 3 sentinel 0 (owned safety) [] := by
  obtain ⟨after, ran, facts, _⟩ := NativeGraph.initialized safety 7 3 (before safety true)
    (ownerCell safety true) sentinel meaning (initial_valid safety true) rfl rfl rfl rfl
  have same := (Prod.mk.inj (Except.ok.inj (ran.symm.trans (source_initializer safety)))).2
  exact same ▸ facts

/-- The same all-ID proof covers the unallocated, offset empty sentinel. -/
theorem initial_queries (safety : Bool) (meaning : Meaning) (id : NodeId) (opcode : Opcode) :
    (owned safety).memory.memory.heap.lookup sentinel.allocation = none ∧
    Operation.run (owned safety).memory.memory (Owner.headerAddress ⟨3, 0⟩) id opcode = .ok (.ok none) := by
  refine ⟨by cases safety <;> rfl, ?_⟩
  have query := (initialized_from_execution safety meaning).operations id opcode
  rw [Storage.operation_correct] at query
  exact query

/-- Initialization and subsequent local cleanup retain an actual offset view
into an older caller allocation, as well as the native empty graph. -/
theorem initial_offset_survives (safety : Bool) (meaning : Meaning) (mark : Nat) (older : 3 < mark) :
    let after : World (Publication.Effects Nat) :=
      { owned safety with memory := { (owned safety).memory with
        memory := Compiler.ZigAir.Memory.cleanup mark (owned safety).memory.memory } }
    Facts safety 7 3 sentinel 0 after [] ∧ Good ⟨0, 1, 2⟩ [1, 2] after := by
  have facts := (initialized_from_execution safety meaning).cleanup mark older
  refine ⟨facts, facts.valid, ?_⟩
  exact represented_frame ⟨0, 1, 2⟩ [1, 2]
    (GraphInit.Ownership.Tests.allocator_effects_registry_and_parent_retained safety meaning).2.2.2
    (Compiler.ZigAir.Memory.cleanup_lookup_older _ mark 0 (by omega))

/-- Persistent facts for the complete recursive program, after native growth
OOM, child return, parent defer and outer literal cleanup. The legacy fixture's
extra immutable-input field and cached query agreement are not needed here. -/
theorem recursive_after (safety : Bool) (depth : Nat) :
    Facts safety 7 6 ⟨ConstructorItem.ReachablePrefixTests.backing, 0⟩ 5 (program safety (depth + 2)).2 (rows safety) :=
  (program_contract safety depth).2.1.native (by rw [rows_count]; decide)

theorem recursive_queries (safety : Bool) (depth : Nat) (id : NodeId) (opcode : Opcode) :
    Operation.run (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩) id opcode =
      .ok (((Interner.representativeReads (program safety (depth + 2)).2.graph).operation id opcode).map
        (Option.map Operation.returned)) := by
  have facts := recursive_after safety depth
  simpa only [Interner.representativeReads, facts.projected, Nested.storageReads] using facts.operations id opcode

/-- Every actual hit in the reached graph supplies the next complete borrowed
constructor's native input and separation contract, with no query-agreement
premise. This is a postcondition of the composed program. -/
theorem recursive_borrowed_input (safety : Bool) (depth : Nat) (id : NodeId) (opcode : Opcode)
    (value : Compiler.ZigAir.Memory.Value)
    (native : Operation.run (program safety (depth + 2)).2.memory.memory (Owner.headerAddress ⟨6, 0⟩)
      id opcode = .ok (.ok (some value))) :
    ∃ slice, value = Operation.returned slice ∧
      BorrowedQuery.observe 7 id opcode (program safety (depth + 2)).2 = .ok (some slice) ∧
      Good (view slice) slice.items (program safety (depth + 2)).2 ∧
      ∀ key old, (program safety (depth + 2)).2.memory.effects.keys key = some old → key.arguments ≠ [] →
        (view slice).length ≠ 0 → (view slice).allocation ≠ old.address :=
  (recursive_after safety depth).queried_input id opcode value native

theorem exhaustion_retained (safety : Bool) :
    ordinary (program safety 1).1 = false ∧
    Facts safety 7 6 ⟨ConstructorItem.ReachablePrefixTests.backing, 0⟩ 5 (program safety 1).2 (rows safety) ∧
    Held 7 rootSource [4] (parent safety).normalized (program safety 1).2 := by
  obtain ⟨rejected, held, facts, _⟩ := NativeRecursion.Tests.incomplete_retains_parent safety
  exact ⟨rejected, facts.native (by rw [rows_count]; decide), held⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph.Tests
