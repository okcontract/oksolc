/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerCloseTake
import Compiler.Extraction.InternerCallerTakeTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Close.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace Normalization.Tests
open OwnedCall.Tests (request world Search callbacks callbacks_contracts)
open Take.Tests (borrowed borrowed_ready initialized ownedHandle)

def key : Key := ⟨1, 1, 0, items, 0⟩
def taken := OwnedCall.take success 7 ⟨world, { lookup := some borrowed }⟩
def lookup : NormalizationOwnership.State := (Take.capture success 7 .input borrowed world.memory).1.2
def miss (search : Search) (publishFails insertFails : Bool) :=
  Interner.findCode.controlMiss (OwnedCall.execution success 7 (callbacks search publishFails insertFails))
    request key true taken.2
def captured (search : Search) (publishFails insertFails : Bool) :=
  let state := (miss search publishFails insertFails).2
  capture success 7 lookup (if state.scope.handedOff then .transfer else .cleanup) borrowed state

theorem ready_lookup :
    (capture success 7 (token .input borrowed) .lookup borrowed ⟨world, { lookup := some borrowed }⟩).2.events = [] := by rfl'

theorem owned_lookup :
    let execution := capture success 7 (token .allocation ownedHandle) .lookup ownedHandle initialized.2
    execution.2.events = [.release (token .allocation ownedHandle)] ∧ execution.2.effects.session.effects = 120 ∧
      execution.2.effects.session.heap 4 = none := ⟨by rfl', by rfl', by rfl'⟩

theorem reached_failure :
    (miss .fail false false).2.world.graph.allocationCursor = 9 ∧
    (captured .fail false false).2.events = [.release lookup] ∧
    (captured .fail false false).2.effects.session.effects = 235 ∧
    (captured .fail false false).2.effects.session.heap 4 = none := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem handoff_skips_release :
    (miss .found false false).2.scope.handedOff = true ∧
    (captured .found false false).2.events = [] ∧
    (captured .found false false).2.effects.session = (miss .found false false).2.world.memory :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem separate_host_events :
    let state := (miss .fail false false).2.mapEffects (fun effects => (⟨effects, [.itemFree 91]⟩ : HostTrace.Recorded Nat))
    let execution := capture (HostTrace.record success) 7 lookup .cleanup borrowed state
    execution.2.events = [.release lookup] ∧
      execution.2.effects.session.effects.events = [.itemFree 91, .free ⟨4, items⟩] := ⟨by rfl', by rfl'⟩

theorem empty_release :
    let handle : Handle := ⟨⟨900, 90, 0⟩, [], none⟩
    let state : OwnedCall.State (HostTrace.Recorded Nat) :=
      ⟨world.mapEffects (fun effects => ⟨effects, []⟩), ⟨some handle, some ⟨4, []⟩, false⟩⟩
    let execution := capture (HostTrace.record success) 7 lookup .cleanup handle state
    execution.2.events = [.release lookup] ∧ execution.2.effects.session.effects.events = [] := ⟨by rfl', by rfl'⟩

def invalid : OwnedCall.State Nat := ⟨world, ⟨some borrowed, some ⟨900, items⟩, false⟩⟩
theorem invalid_release_rejected :
    let execution := capture success 7 lookup .cleanup borrowed invalid
    checked execution [] [] lookup .cleanup items world.graph = .error (.physical (.memory (.release (.ownership .unallocated)))) ∧
      observe invalid execution.2.effects = some (.error (.memory (.release (.ownership .unallocated))), invalid) :=
  ⟨by rfl', by rfl'⟩

theorem missing_slice_rejected :
    let execution := capture success 7 lookup .cleanup borrowed ⟨world, { lookup := some borrowed }⟩
    checked execution [] [] lookup .cleanup items world.graph = .error (.physical .missingSlice) := by rfl'

theorem wrong_cursor_rejected :
    checked (captured .fail false false) [] [] lookup .cleanup items { world.graph with allocationCursor := 1 } =
      .error (.scope (.mismatch 2)) := by rfl'

theorem missing_event_rejected :
    let execution := captured .fail false false
    checked (execution.1, { execution.2 with events := [] }) [] [] lookup .cleanup items world.graph =
      .error (.scope (.mismatch 1)) := by rfl'

theorem semantic_retains_state :
    let body := miss .semantic false false
    finish success 7 body.1 body.2 = body :=
  finish_semantic success 7 _ _ (by rfl')

theorem take_succeeds : taken.1 = .ok () := by rfl'
theorem ordinary_miss (search : Search) (publishFails insertFails : Bool) (ordinarySearch : search ≠ .semantic) :
    ordinary (miss search publishFails insertFails).1 = true := by
  cases search <;> cases publishFails <;> cases insertFails <;> first | contradiction | rfl'

attribute [local irreducible] Completion Take.capture capture

theorem verified_miss (search : Search) (publishFails insertFails : Bool) (ordinarySearch : search ≠ .semantic)
    (leading suffix : List (Event Failure)) :
    ∃ slice remaining, taken.2.scope = ⟨some remaining, some slice, false⟩ ∧
      Normalization.Taken 7 source items borrowed world.memory slice remaining taken.2.world.memory ∧
      Completion success 7 source items lookup remaining slice (miss search publishFails insertFails) leading suffix :=
  miss_after_take success 7 .input source items borrowed world borrowed_ready (external_admitted _)
    (callbacks search publishFails insertFails) (callbacks_contracts search publishFails insertFails source items)
    request key true rfl take_succeeds (ordinary_miss search publishFails insertFails ordinarySearch) leading suffix

theorem verified_lookup (leading suffix : List (Event Failure)) :
    let native : OwnedCall.State Nat := ⟨world, { lookup := some borrowed }⟩
    let execution := capture success 7 (token .input borrowed) .lookup borrowed native
    ∃ after, cleanup success 7 native = (.ok (), after) ∧ Good source items after.world ∧ Closed after.scope ∧
      after.world.graph = world.graph ∧ after.world.memory = execution.2.effects.session ∧
      checked execution leading suffix (token .input borrowed) .lookup items { world.graph with allocationCursor := leading.length } =
        .ok ⟨⟨some execution.1, items, .lookup⟩, { world.graph with allocationCursor := leading.length + execution.2.events.length }⟩ :=
  lookup_verified success 7 .input source items borrowed world borrowed_ready leading suffix

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Close.Tests
