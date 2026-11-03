/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProduction
import Compiler.Extraction.InternerOwnedTests
import Compiler.Extraction.InternerScopeTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests OwnedCall.Tests

/-- Query observations exercise control/cleanup; they do not claim a native
implementation of isDeterministic or representative validation. -/
def queries : Queries where
  atCapacity := fun _ => false
  deterministic := fun _ => .ok true
  validate := fun _ _ => .ok ()

def cached : World Nat := { world with graph := { world.graph with table := fun _ => some 42 } }
def found := find success 160 7 (callbacks .fail false false) queries source callerBuffer request cached
def missed := find success 160 7 (callbacks .fail false false) queries source callerBuffer request world
def forceQueries : Queries := { queries with deterministic := fun _ => .error .unsupported }
def forced (publishFails : Bool) := force success 160 7 (callbacks .semantic publishFails false)
  forceQueries source callerBuffer 11 request.item request.arguments world

theorem find_cache_hit_releases_temporary : found.1 = .ok 42 ∧ found.2.world.memory.effects = 120 ∧
    found.2.world.memory.heap 4 = none ∧ found.2.scope = ⟨none, none, false⟩ ∧
    found.2.world.graph.allocationCursor = 0 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem find_nested_failure : missed.1 = .error (.language .outOfMemory) ∧ missed.2.world.memory.effects = 235 ∧
    missed.2.world.graph.allocationCursor = 9 ∧ missed.2.world.memory.heap 4 = none ∧ missed.2.world.memory.heap 7 = none ∧
    missed.2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def full := find success 0 7 (callbacks .fail false false) { queries with atCapacity := fun _ => true }
  source callerBuffer request world

theorem capacity_before_initialization : full.1 = .error (.language .capacity) ∧ full.2.world.memory.effects = 5 ∧
    full.2.world.memory.heap 4 = none ∧ full.2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl', by rfl'⟩

def invalid := force success 0 7 (callbacks .fail false false) { queries with validate := fun _ _ => .error .invalidId }
  source callerBuffer 11 request.item request.arguments world

theorem validation_before_initialization : invalid.1 = .error (.language .invalidId) ∧ invalid.2.world.memory.effects = 5 ∧
    invalid.2.world.memory.heap 4 = none ∧ invalid.2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl', by rfl'⟩

def forcedHit := force success 160 7 (callbacks .semantic true true) queries source callerBuffer 11 request.item request.arguments cached

theorem force_cache_hit_releases_temporary : forcedHit.1 = .ok () ∧ forcedHit.2.world.memory.effects = 120 ∧
    forcedHit.2.world.memory.heap 4 = none ∧ forcedHit.2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem force_publication_failure : (forced true).1 = .error (.language .outOfMemory) ∧
    (forced true).2.world.memory.effects = 120 ∧ (forced true).2.world.memory.heap 4 = none ∧
    (forced true).2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem force_publication_success : (forced false).1 = .ok () ∧ (forced false).2.world.memory.effects = 120 ∧
    (forced false).2.world.memory.heap 4 = none ∧ (forced false).2.scope.lookup = none ∧
    (forced false).2.scope.handedOff = true := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def nondeterministic := find success 160 7 (callbacks .semantic true false)
  { queries with deterministic := fun _ => .ok false } source callerBuffer request cached

theorem nondeterministic_skips_cache_and_simplification : nondeterministic.1 = .ok 11 ∧
    nondeterministic.2.world.memory.effects = 120 ∧ nondeterministic.2.scope.handedOff = true := ⟨by rfl', by rfl', by rfl'⟩

def queryError (error : Interner.Error) := find success 160 7 (callbacks .fail false false)
  { queries with deterministic := fun _ => .error error } source callerBuffer request cached

theorem ordinary_query_error_cleans : (queryError .outOfMemory).1 = .error (.language .outOfMemory) ∧
    (queryError .outOfMemory).2.world.memory.effects = 120 ∧ (queryError .outOfMemory).2.scope = ⟨none, none, false⟩ :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem semantic_query_error_retains : (queryError .unsupported).1 = .error (.language .unsupported) ∧
    (queryError .unsupported).2.world.memory.effects = 17 ∧
    (queryError .unsupported).2.scope.lookup = some ⟨⟨4, 0, 3⟩, [1, 2, 3], some ⟨4, [1, 2, 3]⟩⟩ :=
  ⟨by rfl', by rfl', by rfl'⟩

def scratchHit := find success 160 7 (callbacks .semantic true true) queries ⟨0, 0, 2⟩ callerBuffer
  { request with arguments := [3, 1] } cached

theorem scratch_hit_no_owned_free : scratchHit.1 = .ok 42 ∧ scratchHit.2.world.memory.effects = 5 ∧
    scratchHit.2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl'⟩

def duplicateFailure := find (external (fun site => site == .duplicate)) 160 7 (callbacks .semantic false false)
  queries ⟨0, 0, 2⟩ callerBuffer { request with arguments := [3, 1] } world

theorem duplicate_failure_after_lookup : duplicateFailure.1 = .error (.language .outOfMemory) ∧
    duplicateFailure.2.world.memory.effects = 13 ∧ duplicateFailure.2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl'⟩

def allocationFailure := find (external (fun _ => true)) 160 7 (callbacks .semantic false false)
  queries source callerBuffer request cached

theorem initializer_failure_precedes_cache_hit : allocationFailure.1 = .error (.language .outOfMemory) ∧
    allocationFailure.2.world.memory.effects = 17 ∧ allocationFailure.2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl'⟩

def incomplete := find success 0 7 (callbacks .fail false false) queries source callerBuffer request cached

theorem initialization_fault_retains_provisional : incomplete.1 = .error (.memory (.preparation .incomplete)) ∧
    incomplete.2.world.memory.effects = 17 ∧ incomplete.2.world.memory.heap 4 = some ⟨7, .arguments items⟩ ∧
    incomplete.2.scope.lookup = none := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem caller_contract (p : Primitives Nat) (q : Queries) (contracts : Contracts 7 source items p) :
    Verified success 7 source items (findBody success 160 7 p q source callerBuffer request) world ∧
    Verified success 7 source items (forceBody success 160 7 p q source callerBuffer 11 request.item request.arguments) world := by
  have checked := production_verified success 160 7 p q source request 11 caller before.memory _
    ⟨original_valid, Allocation.Tests.represented⟩ actual_caller_allocation (external_admitted _) contracts
  simpa only [caller, callerBuffer, world, request, ResourceAdapter.TraceBridge.Tests.request] using checked

theorem find_contract (p : Primitives Nat) (q : Queries) (contracts : Contracts 7 source items p) :
    ordinary (find success 160 7 p q source callerBuffer request world).1 = true →
      Good source items (find success 160 7 p q source callerBuffer request world).2.world ∧
      Closed (find success 160 7 p q source callerBuffer request world).2.scope :=
  Verified.closed success 7 source items _ world (caller_contract p q contracts).1

theorem force_contract (p : Primitives Nat) (q : Queries) (contracts : Contracts 7 source items p) :
    ordinary (force success 160 7 p q source callerBuffer 11 request.item request.arguments world).1 = true →
      Good source items (force success 160 7 p q source callerBuffer 11 request.item request.arguments world).2.world ∧
      Closed (force success 160 7 p q source callerBuffer 11 request.item request.arguments world).2.scope :=
  Verified.closed success 7 source items _ world (caller_contract p q contracts).2

theorem production_nested_failure : Good source items missed.2.world ∧ Closed missed.2.scope := by
  dsimp only [missed]
  apply find_contract (callbacks .fail false false) queries (callbacks_contracts .fail false false source items)
  have result := find_nested_failure.1
  dsimp only [missed] at result
  rw [result]
  rfl

theorem production_force_failure : Good source items (forced true).2.world ∧ Closed (forced true).2.scope := by
  dsimp only [forced]
  apply force_contract (callbacks .semantic true false) forceQueries (callbacks_contracts .semantic true false source items)
  have result := force_publication_failure.1
  dsimp only [forced] at result
  rw [result]
  rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Tests
