/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.ScopedRecursive
import Compiler.Extraction.InsertionEffectTests

namespace Compiler.Extraction.Interner.Scoped.Tests
open Compiler.Algebraic Compiler.Extraction.Cache
open Compiler.Extraction.Recursive
set_option maxRecDepth 8192

-- Nonempty fallible primitive calls and local frees each advance the stream.
-- Empty dupe/free calls leave it unchanged. These are controlled events, not
-- a claim about the native allocator calls inside hash-map/clone primitives.
def resources (failAt : Nat) : Resources where
  sort := List.reverse
  allocate := fun _ ids cursor => if ids.isEmpty then (true, cursor)
    else InsertEffectTests.attempt failAt cursor
  release := fun ids _ cursor => if ids.isEmpty then cursor else cursor + 1

def recursive (failAt depth : Nat) :=
  ScopedRecursive.detailed (resources failAt) (InsertEffectTests.primitives failAt) representativeReads 64 depth
    FrameTests.request FrameTests.initial
def success := recursive 99 2
def parentFailure := recursive 6 2
def childFailure := recursive 5 2
def cutoff := recursive 99 1

theorem all_depths (failAt depth : Nat) : Closed (recursive failAt depth).2.scope :=
  ScopedRecursive.all_scopes_closed _ _ _ _ _ _ _

theorem recursive_success : success.1 = .ok 3 ∧ success.2.heap.allocationCursor = 7 ∧
    success.2.heap.representatives = some (FrameTests.cells ++ [FrameTests.newCell]) ∧
    success.2.scope.phase = .transfer := by exact ⟨rfl, rfl, rfl, rfl⟩

theorem failed_parent_cleans : parentFailure.1 = .error .outOfMemory ∧
    parentFailure.2.heap.allocationCursor = 8 ∧ parentFailure.2.scope.phase = .cleanup ∧
    parentFailure.2.scope.lookup = some {
      origin := .scratch, owner := .released, owned := false, dead := true, invalid := false } := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem failed_parent_keeps_child :
    parentFailure.2.heap.representatives = some (FrameTests.cells ++ [FrameTests.newCell]) ∧
    parentFailure.2.heap.table ⟨2, 0, 42, [], 0⟩ = some 3 ∧
    parentFailure.2.heap.table ⟨1, 1, 0, [1, 2], 77⟩ = none := by exact ⟨rfl, rfl, rfl⟩

theorem failed_child_cleans_parent : childFailure.1 = .error .outOfMemory ∧
    childFailure.2.heap = { FrameTests.initial with allocationCursor := 7 } ∧
    childFailure.2.scope.phase = .cleanup := by exact ⟨rfl, rfl, rfl⟩

theorem incomplete_unwinds : cutoff.1 = .error .unsupported ∧ cutoff.2.heap.allocationCursor = 2 ∧
    cutoff.2.scope.lookup = some {
      origin := .scratch, owner := .released, owned := false, dead := true, invalid := false } := by
  exact ⟨rfl, rfl, rfl⟩

def nextRequest : Request := { FrameTests.request with sequence := 78 }
def afterFailure := ScopedRecursive.detailed (resources 8) (InsertEffectTests.primitives 8) representativeReads 64 2
  nextRequest parentFailure.2.heap

theorem cleanup_affects_next_call : afterFailure.1 = .error .outOfMemory ∧
    afterFailure.2.heap.allocationCursor = 9 ∧
    afterFailure.2.heap.representatives = parentFailure.2.heap.representatives := by exact ⟨rfl, rfl, rfl⟩

def temporary : Request := ⟨⟨1, some 1, 0⟩, [3, 2, 1], 77⟩
def tempKey : Key := ⟨1, 1, 0, [1, 2, 3], 77⟩
def cachedHeap : Heap := { FrameTests.initial with table := put equalityFields FrameTests.initial.table tempKey 2 }
def hit := findDetailed (resources 99) (InsertEffectTests.primitives 99) temporary cachedHeap
def deterministicError := findDetailed (resources 99)
  { InsertEffectTests.primitives 99 with deterministic := fun _ => .error .unsupported } temporary FrameTests.initial
def simplifyError := findDetailed (resources 99)
  { InsertEffectTests.primitives 99 with simplify := fun _ => Interner.fail .unsupported } temporary FrameTests.initial

theorem temporary_hit_frees : hit.1 = .ok 2 ∧ hit.2.heap.allocationCursor = 2 ∧
    hit.2.scope.lookup = some {
      origin := .allocation, owner := .released, owned := true, dead := true, invalid := false } := by
  exact ⟨rfl, rfl, rfl⟩

theorem deterministic_error_frees : deterministicError.1 = .error .unsupported ∧
    deterministicError.2.heap.allocationCursor = 2 ∧
    deterministicError.2.scope.lookup = hit.2.scope.lookup := by exact ⟨rfl, rfl, rfl⟩

theorem transferred_temporary_freed_once : simplifyError.1 = .error .unsupported ∧
    simplifyError.2.heap.allocationCursor = 2 ∧ simplifyError.2.scope.lookup = some {
      origin := .allocation, owner := .released, owned := false, dead := true, invalid := false } := by
  exact ⟨rfl, rfl, rfl⟩

def initFailure := findDetailed (resources 0) (InsertEffectTests.primitives 0) temporary FrameTests.initial
def capacity := findDetailed (resources 99)
  { InsertEffectTests.primitives 99 with atCapacity := fun _ => true } temporary FrameTests.initial

theorem no_handle_before_initialization : initFailure.1 = .error .outOfMemory ∧
    initFailure.2.heap.allocationCursor = 1 ∧ initFailure.2.scope = {} ∧
    capacity = (.error .capacity, ⟨{}, FrameTests.initial⟩) := by exact ⟨rfl, rfl, rfl, rfl⟩

def nondeterministic : Request := ⟨⟨1, some 3, 0⟩, [1, 2], 0⟩
def insertionFailure := findDetailed (resources 1)
  { InsertEffectTests.primitives 1 with deterministic := fun _ => .ok false } nondeterministic FrameTests.initial

theorem insertion_owns_failure : insertionFailure.1 = .error .outOfMemory ∧
    insertionFailure.2.heap.allocationCursor = 2 ∧ insertionFailure.2.scope.phase = .transfer ∧
    insertionFailure.2.scope.lookup = some {
      origin := .input, owner := .caller, owned := false, dead := true, invalid := false } := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def forceFailure := forceDetailed (resources 1) (InsertEffectTests.primitives 1)
  (fun _ _ => .ok ()) 1 nondeterministic.item nondeterministic.arguments FrameTests.initial
def invalidForce := forceDetailed (resources 0) (InsertEffectTests.primitives 0)
  (fun _ _ => .error .invalidId) 1 temporary.item temporary.arguments FrameTests.initial

theorem force_cleanup : forceFailure.1 = .error .outOfMemory ∧ forceFailure.2.heap.allocationCursor = 3 ∧
    forceFailure.2.scope.phase = .cleanup ∧ invalidForce = (.error .invalidId, ⟨{}, FrameTests.initial⟩) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem force_closed_fixture : Closed forceFailure.2.scope := force_closed _ _ _ _ _ _ _

end Compiler.Extraction.Interner.Scoped.Tests
