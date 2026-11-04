/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerScopeTests
import Compiler.Extraction.InsertionSortHeapTests
import Compiler.Extraction.InsertionSortNormalization

namespace Compiler.Extraction.Interner.Scoped.PreparationTests
open Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.Extraction.Recursive

/-- Controlled resource observations, not a native allocator or memory
refinement. Distinct effects expose phase order and stale-cursor decisions. -/
def resources (failAt : Nat) : Resources := {
  Tests.resources failAt with
  prepare := fun _ lookup cursor => cursor + if lookup.origin = .allocation then 10 else 20 }

def initial : Session := ⟨{}, FrameTests.initial⟩
def scratch (failAt : Nat) := initScope (resources failAt) FrameTests.request initial
def allocated (failAt : Nat) := initScope (resources failAt) Tests.temporary initial

theorem scratch_prepares_before_duplicate : (scratch 20).2.heap.allocationCursor = 20 ∧
    (take (resources 20) (scratch 20).2).1 = .error .outOfMemory ∧
    (take (resources 20) (scratch 20).2).2.heap.allocationCursor = 21 := ⟨by rfl', by rfl', by rfl'⟩

theorem allocated_prepares_after_allocation : (allocated 99).2.heap.allocationCursor = 11 ∧
    (take (resources 99) (allocated 99).2).2.heap.allocationCursor = 11 := ⟨by rfl', by rfl'⟩

theorem failed_allocation_skips_preparation : allocated 0 =
    (.error .outOfMemory, ⟨{}, { FrameTests.initial with allocationCursor := 1 }⟩) := by rfl'

theorem borrowed_input_skips_preparation :
    initScope (resources 0) Tests.nondeterministic initial = (.ok [1, 2],
      ⟨⟨some {}, [1, 2], .lookup⟩, FrameTests.initial⟩) := by rfl'

theorem singleton_skips_preparation :
    (initScope (resources 0) { FrameTests.request with arguments := [1] } initial).2.heap.allocationCursor = 0 := by rfl'

theorem cleanup_observes_preparation :
    (close (resources 99) (take (resources 99) (scratch 99).2).2).heap.allocationCursor = 22 ∧
    (close (resources 99) (allocated 99).2).heap.allocationCursor = 12 := ⟨by rfl', by rfl'⟩

def recursive := ScopedRecursive.detailed (resources 20) (InsertEffectTests.primitives 20)
  representativeReads 64 1 FrameTests.request FrameTests.initial

theorem recursive_take_fails_at_reached_cursor : recursive.1 = .error .outOfMemory ∧
    recursive.2.heap = { FrameTests.initial with allocationCursor := 21 } ∧
    recursive.2.scope.lookup = some { origin := .scratch, dead := true } := ⟨by rfl', by rfl', by rfl'⟩

theorem recursive_failure_closes_scope : Closed recursive.2.scope :=
  ScopedRecursive.all_scopes_closed _ _ _ _ _ _ _

def hit := findDetailed (resources 99) (InsertEffectTests.primitives 99) Tests.temporary Tests.cachedHeap

theorem lookup_hit_releases_after_preparation : hit.1 = .ok 2 ∧ hit.2.heap.allocationCursor = 12 ∧
    hit.2.scope.lookup = some { origin := .allocation, owner := .released, owned := true, dead := true } :=
  ⟨by rfl', by rfl', by rfl'⟩

end Compiler.Extraction.Interner.Scoped.PreparationTests
