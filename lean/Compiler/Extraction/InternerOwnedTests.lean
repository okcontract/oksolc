/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerOwnedNested
import Compiler.Extraction.NormalizationTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

inductive Search where
  | fail | found | unchanged | semantic
  deriving DecidableEq, Repr

def releaseSlice (external : External σ) (allocator : Nat) (slice : ArgumentSlice) : GraphAction σ Unit := fun before =>
  let (result, memory) := free external allocator slice before.memory
  (result.mapError memoryFault, { before with memory })

theorem release_good (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (slice : ArgumentSlice) (before : World σ) (held : Held allocator source values slice before) :
    ∃ after, releaseSlice external allocator slice before = (.ok (), after) ∧ Good source values after := by
  obtain ⟨memory, freed, valid, post, _⟩ := free_valid external allocator slice before.memory held.1.1 held.2.1
  exact ⟨{ before with memory }, by simp [releaseSlice, freed, Except.mapError],
    valid, released_source source values held.1.2 post held.2.2⟩

/-- Concrete callback ownership fixtures. Graph insertion/publication meaning
is deliberately outside this test; their actual slice consumption is exercised. -/
def callbacksWith (external : External σ) (search : Search) (publishFails insertFails : Bool) : Primitives σ where
  simplify := fun _ slice before =>
    let (result, after) := nested external 7 slice before
    match result with
    | .error fault => (.error fault, after)
    | .ok () =>
      let after := { after with graph := { after.graph with allocationCursor := after.graph.allocationCursor + 9 } }
      (match search with
        | .fail => .error (.language .outOfMemory)
        | .found => .ok (some 11)
        | .unchanged => .ok none
        | .semantic => .error (.memory (.preparation .incomplete)), after)
  publish := fun _ slice _ before =>
    if publishFails then (.error (.language .outOfMemory), before) else releaseSlice external 7 slice before
  insert := fun _ slice _ before =>
    let (result, after) := releaseSlice external 7 slice before
    (match result with
      | .error fault => .error fault
      | .ok () => if insertFails then .error (.language .outOfMemory) else .ok 11, after)

/-- Retain the original fixture as an application of the shared host-parametric callbacks. -/
def callbacks := callbacksWith success

theorem callbacks_contracts (search : Search) (publishFails insertFails : Bool) (source : View) (values : List NodeId) :
    Contracts 7 source values (callbacks search publishFails insertFails) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro key slice id before _aligned held
    cases publishFails with
    | true => exact fun _ => ⟨held.1, fun _ _ => held.2.1⟩
    | false =>
      obtain ⟨after, released, good⟩ := release_good success 7 source values slice before held
      simp only [callbacks, callbacksWith, Bool.false_eq_true, ↓reduceIte, released]
      exact fun _ => ⟨good, by intro fault impossible; cases impossible⟩
  · intro key slice deterministic before _aligned held
    obtain ⟨after, released, good⟩ := release_good success 7 source values slice before held
    simp only [callbacks, callbacksWith, released]
    exact fun _ => good
  · intro key slice before _aligned held
    have checked := nested_held success 7 source values slice before held (external_admitted _)
    cases ran : nested success 7 slice before with
    | mk result after =>
      rw [ran] at checked
      cases result with
      | error fault => simpa only [callbacks, callbacksWith, ran] using fun (_ : ordinary (.error fault : Except Fault (Option NodeId)) = true) => checked.2
      | ok returned =>
        cases returned
        simp only [callbacks, callbacksWith, ran]
        exact fun _ => checked.2

def request := ResourceAdapter.TraceBridge.Tests.request
def graphHeap := ResourceAdapter.TraceBridge.Tests.graph
def caller : World Nat := ⟨graphHeap, original⟩
def callerBuffer : View := ⟨caller.memory.memory.nextId, 0, 2⟩
def world : World Nat := { caller with memory := { caller.memory with memory := before.memory } }
def observed (search : Search) (publishFails insertFails : Bool) :=
  entry success 160 7 (callbacks search publishFails insertFails) request true true source callerBuffer world

theorem nested_failure_cleanup :
    (observed .fail false false).1 = .error (.language .outOfMemory) ∧
    (observed .fail false false).2.world.memory.effects = 235 ∧
    (observed .fail false false).2.world.graph.allocationCursor = 9 ∧
    (observed .fail false false).2.world.memory.heap 4 = none ∧
    (observed .fail false false).2.world.memory.heap 7 = none ∧
    (observed .fail false false).2.scope = ⟨none, none, false⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem publication_failure_cleanup :
    (observed .found true false).1 = .error (.language .outOfMemory) ∧
    (observed .found true false).2.world.memory.effects = 235 ∧
    (observed .found true false).2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl'⟩

theorem publication_success_detached_alias :
    (observed .found false false).1 = .ok 11 ∧
    (observed .found false false).2.world.memory.effects = 235 ∧
    (observed .found false false).2.world.memory.heap 4 = none ∧
    (observed .found false false).2.scope = ⟨none, some ⟨4, [1, 2, 3]⟩, true⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem insertion_success : (observed .unchanged false false).1 = .ok 11 ∧
    (observed .unchanged false false).2.world.memory.effects = 235 ∧
    (observed .unchanged false false).2.scope.handedOff = true := ⟨by rfl', by rfl', by rfl'⟩

theorem insertion_failure_handoff : (observed .unchanged false true).1 = .error (.language .outOfMemory) ∧
    (observed .unchanged false true).2.world.memory.effects = 235 ∧
    (observed .unchanged false true).2.world.memory.heap 4 = none ∧
    (observed .unchanged false true).2.scope.handedOff = true := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem semantic_callback_retains_parent :
    (observed .semantic false false).1 = .error (.memory (.preparation .incomplete)) ∧
    (observed .semantic false false).2.world.memory.effects = 132 ∧
    (observed .semantic false false).2.world.memory.heap 4 = some ⟨7, .arguments [1, 2, 3]⟩ ∧
    (observed .semantic false false).2.scope.lookup = some ⟨⟨4, 0, 3⟩, [1, 2, 3], none⟩ ∧
    (observed .semantic false false).2.scope.handedOff = false :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def failedDuplicate := entry (external (fun site => site == .duplicate)) 160 7 (callbacks .fail false false)
  { request with arguments := [3, 1] } true true ⟨0, 0, 2⟩ buffer world

theorem duplicate_oom_preserves_effects : failedDuplicate.1 = .error (.language .outOfMemory) ∧
    failedDuplicate.2.world.memory.effects = 13 ∧ failedDuplicate.2.world.graph.allocationCursor = 0 ∧
    failedDuplicate.2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl', by rfl'⟩

def failedTemporary := entry (external (fun _ => true)) 160 7 (callbacks .fail false false) request true true source buffer world

theorem temporary_oom_no_defer : failedTemporary.1 = .error (.language .outOfMemory) ∧
    failedTemporary.2.world.memory.effects = 17 ∧ failedTemporary.2.world.graph.allocationCursor = 0 ∧
    failedTemporary.2.scope.lookup = none := ⟨by rfl', by rfl', by rfl', by rfl'⟩

def stopped := entry success 0 7 (callbacks .fail false false) request true true source buffer world

theorem preparation_fault_no_defer : stopped.1 = .error (.memory (.preparation .incomplete)) ∧
    stopped.2.world.memory.effects = 17 ∧ stopped.2.world.memory.heap 4 = some ⟨7, .arguments items⟩ :=
  ⟨by rfl', by rfl', by rfl'⟩

def empty := entry success 0 7 (callbacks .fail false false) { request with arguments := [] } true true ⟨900, 90, 0⟩ buffer world

theorem empty_nested_no_native_allocation : empty.1 = .error (.language .outOfMemory) ∧
    empty.2.world.memory.effects = 5 ∧ empty.2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl'⟩

/-- The composed theorem has an inhabited callback contract whose child
allocation/copy/free operations were actually checked, followed by caller OOM. -/
theorem caller_contract (p : Primitives Nat) (contracts : Contracts 7 source items p) :
    ordinary (entry success 160 7 p request true true source callerBuffer world).1 = true →
      Good source items (entry success 160 7 p request true true source callerBuffer world).2.world ∧
      Closed (entry success 160 7 p request true true source callerBuffer world).2.scope := by
  have checked := production_verified success 160 7 p request true true source
    caller before.memory _ original_valid Allocation.Tests.represented actual_caller_allocation
    (by rfl') (external_admitted _) contracts
  simpa only [caller, callerBuffer, world, request, ResourceAdapter.TraceBridge.Tests.request] using checked.2

theorem production_nested_contract : ordinary (observed .fail false false).1 = true →
    Good source items (observed .fail false false).2.world ∧ Closed (observed .fail false false).2.scope := by
  simpa only [observed] using caller_contract (callbacks .fail false false) (callbacks_contracts .fail false false source items)

theorem production_nested_failure : Good source items (observed .fail false false).2.world ∧
    Closed (observed .fail false false).2.scope := by
  apply production_nested_contract
  rw [nested_failure_cleanup.1]
  rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Tests
