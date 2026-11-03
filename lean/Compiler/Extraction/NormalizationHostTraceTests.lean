/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerMemoryEffects
import Compiler.Extraction.InternerPhysicalDispatchProductionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.HostTrace.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

def recorded := before.mapEffects (fun effects => (⟨effects, []⟩ : Recorded Nat))
def observed (host : External Nat) (budget : Nat) (commutative : Bool)
    (source : View) (values : List NodeId) (exit : NormalizationOwnership.Exit) :=
  Normalization.run normalizationOwnershipCode (record host) budget 7 commutative source buffer values exit recorded

theorem actual_admitted : Admitted (record success) := admitted success (external_admitted _)

theorem lifecycle_erases (host : External Nat) (budget : Nat) (commutative : Bool)
    (source : View) (values : List NodeId) (exit : NormalizationOwnership.Exit) :
    Normalization.run normalizationOwnershipCode host budget 7 commutative source buffer values exit before =
      Step.mapEffects Recorded.effects (observed host budget commutative source values exit) :=
  run_erases normalizationOwnershipCode host budget 7 commutative source buffer values exit recorded

theorem temporary_transfer :
    (observed success 160 true source items .transfer).2.effects.events = [.allocate .temporary 12 (some 64)] := by rfl'

theorem temporary_cleanup :
    (observed success 160 true source items .cleanup).2.effects.events =
      [.allocate .temporary 12 (some 64), .free ⟨4, [1, 2, 3]⟩] := by rfl'

theorem borrowed_duplicate :
    (observed success 160 false source items .cleanup).2.effects.events =
      [.allocate .duplicate 12 (some 64), .free ⟨4, items⟩] := by rfl'

theorem borrowed_lookup : (observed success 160 false source items .lookup).2.effects.events = [] := by rfl'

theorem empty_transfer : (observed success 160 true ⟨900, 90, 0⟩ [] .transfer).2.effects.events = [] := by rfl'

theorem oom_retained :
    (observed (external (fun _ => true)) 160 true source items .cleanup).1 = .error .outOfMemory ∧
    (observed (external (fun _ => true)) 160 true source items .cleanup).2.effects =
      (⟨17, [.allocate .temporary 12 none]⟩ : Recorded Nat) := ⟨by rfl', by rfl'⟩

theorem incomplete_retains_allocation :
    (observed success 0 true source items .cleanup).1 = .error (.preparation .incomplete) ∧
    (observed success 0 true source items .cleanup).2.effects.events = [.allocate .temporary 12 (some 64)] ∧
    (observed success 0 true source items .cleanup).2.heap 4 = some ⟨7, .arguments items⟩ := ⟨by rfl', by rfl', by rfl'⟩

def invalid : External Nat := { success with allocate := fun _ _ bytes effects => (some 0, effects + bytes) }

theorem invalid_response_retained :
    (observed invalid 160 true source items .cleanup).1 = .error (.allocation (.memory .memoryValidity)) ∧
    (observed invalid 160 true source items .cleanup).2.effects.events = [.allocate .temporary 12 (some 0)] :=
  ⟨by rfl', by rfl'⟩

def partialCopy := Normalization.run normalizationOwnershipCode (record success) 0 7 false source buffer items .cleanup
  { recorded with memory := Duplication.Tests.incomplete }

theorem partial_copy_retained : partialCopy.1 = .error (.allocation (.memory .uninitialized)) ∧
    partialCopy.2.effects.events = [.allocate .duplicate 12 (some 56)] ∧
    Compiler.ZigAir.Memory.load partialCopy.2.memory ((⟨3, 0, 3⟩ : View).pointer 0) = .ok (number 3) ∧
    Compiler.ZigAir.Memory.load partialCopy.2.memory ((⟨3, 0, 3⟩ : View).pointer 1) = .error .uninitialized :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem rejected_release_skips_host :
    (Normalization.free (record success) 8 ⟨0, items⟩ recorded).2.effects.events = [] := by rfl'

theorem existing_history (leading : List Event) :
    Normalization.run normalizationOwnershipCode (record success) 160 7 true source buffer items .cleanup
        (recorded.mapEffects (prepend leading)) =
      Step.mapEffects (prepend leading) (observed success 160 true source items .cleanup) :=
  run_prefix normalizationOwnershipCode success 160 7 true source buffer items .cleanup recorded leading

end Compiler.Extraction.Memory.Arguments.Normalization.HostTrace.Tests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.HostTraceTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests OwnedCall.Tests

theorem nested_transport {physical : External σ} {original : External τ} {project : σ → τ}
    (mapped : External.Transport physical original project) (slice : ArgumentSlice) :
    Effect.Transport (World.mapEffects project) (nested physical 7 slice) (nested original 7 slice) := by
  intro before
  unfold nested
  simp only [World.mapEffects]
  rw [mapped.run]
  dsimp only [Step.mapEffects]
  cases Normalization.run normalizationOwnershipCode physical 0 7 false (view slice) ⟨0, 0, 0⟩ slice.items .cleanup before.memory with
  | mk result reached => cases result <;> rfl

theorem release_transport {physical : External σ} {original : External τ} {project : σ → τ}
    (mapped : External.Transport physical original project) (slice : ArgumentSlice) :
    Effect.Transport (World.mapEffects project) (OwnedCall.Tests.releaseSlice physical 7 slice) (OwnedCall.Tests.releaseSlice original 7 slice) := by
  intro before
  unfold OwnedCall.Tests.releaseSlice
  simp only [World.mapEffects]
  rw [mapped.free]
  rfl

/-- Existing nested execution fixtures instantiate the generic caller theorem;
no callback is replaced with a replay or a post-hoc reconstructed world. -/
theorem callbacks_transport {physical : External σ} {original : External τ} {project : σ → τ}
    (mapped : External.Transport physical original project) (search : Search) (publishFails insertFails : Bool) :
    (callbacksWith physical search publishFails insertFails).Transport
      (callbacksWith original search publishFails insertFails) project := by
  constructor
  · intro key slice before
    dsimp only [callbacksWith]
    rw [nested_transport mapped slice before]
    cases nested physical 7 slice before with
    | mk result reached => cases result <;> rfl
  · intro key slice id before
    cases publishFails with
    | true => rfl
    | false => exact release_transport mapped slice before
  · intro key slice deterministic before
    dsimp only [callbacksWith]
    rw [release_transport mapped slice before]

def recordedWorld := world.mapEffects (fun effects => (⟨effects, []⟩ : HostTrace.Recorded Nat))
def caller (search : Search) (publishFails insertFails : Bool) :=
  Caller.find (HostTrace.record success) 160 7 (callbacksWith (HostTrace.record success) search publishFails insertFails)
    Caller.Tests.queries source callerBuffer request recordedWorld

theorem caller_erases (search : Search) (publishFails insertFails : Bool) :
    Caller.find success 160 7 (callbacks search publishFails insertFails) Caller.Tests.queries source callerBuffer request world =
      ((caller search publishFails insertFails).1, (caller search publishFails insertFails).2.mapEffects HostTrace.Recorded.effects) :=
  Caller.host_trace_erases success 160 7 (callbacks_transport (HostTrace.transport success) search publishFails insertFails)
    Caller.Tests.queries source callerBuffer request recordedWorld

theorem nested_oom_reached_state : (caller .fail false false).1 = .error (.language .outOfMemory) ∧
    (caller .fail false false).2.world.memory.effects.effects = 235 ∧
    (caller .fail false false).2.world.graph.allocationCursor = 9 ∧
    (caller .fail false false).2.scope = ⟨none, none, false⟩ := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem nested_oom_event_order : (caller .fail false false).2.world.memory.effects.events =
    [.allocate .temporary 12 (some 64), .allocate .duplicate 12 (some 100),
     .free ⟨7, [1, 2, 3]⟩, .free ⟨4, [1, 2, 3]⟩] := by rfl'

theorem semantic_fault_event_order : (caller .semantic false false).2.world.memory.effects.events =
    [.allocate .temporary 12 (some 64), .allocate .duplicate 12 (some 100), .free ⟨7, [1, 2, 3]⟩] := by rfl'

theorem semantic_fault_retains_parent :
    (caller .semantic false false).1 = .error (.memory (.preparation .incomplete)) ∧
    (caller .semantic false false).2.world.memory.effects.effects = 132 ∧
    (caller .semantic false false).2.world.memory.heap 4 = some ⟨7, .arguments [1, 2, 3]⟩ := ⟨by rfl', by rfl', by rfl'⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.HostTraceTests
