/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationTraceProduction
import Compiler.Extraction.NormalizationResourcesTests
import Compiler.Extraction.InternerPreparationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open NormalizationOwnership.Trace
open Normalization.Tests

def request : Interner.Request := ⟨⟨1, some 1, 0⟩, items, 0⟩
def binary : Interner.Request := { request with arguments := [3, 1] }
def graph := Compiler.Extraction.Recursive.FrameTests.initial
def temporary := captured success 160 7 true source buffer items .transfer before
def scratch := captured success 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .transfer before

theorem temporary_events : temporary.2.events =
    [.allocate .temporary true, .prepare { origin := .allocation, owner := .lookup, owned := true } (.ok ())] := by rfl'

theorem scratch_events : scratch.2.events =
    [.prepare { origin := .scratch } (.ok ()), .allocate .duplicate true] := by rfl'

theorem borrowed_no_events :
    (captured success 160 7 false source buffer items .lookup before).2.events = [] := by rfl'

theorem scratch_accepted : checked scratch [] [] binary .transfer graph =
    .ok (Scope.run (Scope.resources scratch.2.events (.preparation .incomplete)) binary .transfer graph) := by rfl'

theorem scratch_scope_transfer :
    let scope := Scope.run (Scope.resources scratch.2.events (.preparation .incomplete)) binary .transfer graph
    Scope.observe scope = (some (.transferred, { origin := .scratch, owner := .caller, dead := true }), 2) ∧
      scope.2.scope.items = [1, 3] := ⟨by rfl', by rfl'⟩

/-- Surrounding events are not certified by a local invocation. Its exact
cursor interval is retained, allowing a caller to check those separately. -/
theorem embedded_replay :
    Scope.observe (Scope.run (Scope.resources ([.release {}] ++ scratch.2.events ++ [.allocate .temporary false])
      (.preparation .incomplete)) binary .transfer { graph with allocationCursor := 1 }) =
      (some (.transferred, { origin := .scratch, owner := .caller, dead := true }), 3) := by
  rw [scratch_events]
  rfl'

theorem invalid_entry_rejected : Scope.checked ([] : List (Event Failure)) (.preparation .incomplete)
    { binary with item := ⟨1, none, 0⟩ } .transfer graph = .error (.entry .invalidOptional) := by rfl'

def empty := captured success 160 7 true ⟨900, 90, 0⟩ buffer [] .transfer before

theorem empty_duplicate_skips_native_allocation : empty.2.events = [.allocate .duplicate true] ∧
    empty.2.effects.session.effects = 5 ∧
    checked empty [] [] { request with arguments := [] } .transfer graph =
      .ok (.ok .transferred, ⟨⟨some { owner := .caller, dead := true }, [], .transfer⟩,
        { graph with allocationCursor := 1 }⟩) := ⟨by rfl', by rfl', by rfl'⟩

theorem missing_event_rejected : Scope.checked ([] : List (Event Failure)) (.preparation .incomplete) binary .transfer graph =
    .error (.mismatch 1) := by rfl'

theorem reordered_event_rejected : Scope.checked
    [.allocate .duplicate true, .prepare { origin := .scratch } (.ok ())]
    (.preparation .incomplete : Failure) binary .transfer graph = .error (.mismatch 3) := by rfl'

theorem wrong_allocation_site_rejected : Scope.checked
    [.prepare { origin := .scratch } (.ok ()), .allocate .temporary true]
    (.preparation .incomplete : Failure) binary .transfer graph = .error (.mismatch 3) := by rfl'

theorem wrong_owner_rejected : Scope.checked
    [.prepare { origin := .scratch, owner := .lookup, owned := true } (.ok ())]
    (.preparation .incomplete : Failure) binary .lookup graph = .error (.mismatch 2) := by rfl'

theorem wrong_release_rejected : Scope.checked
    [.prepare { origin := .scratch } (.ok ()), .allocate .duplicate true,
      .release { origin := .scratch, owner := .lookup }]
    (.preparation .incomplete : Failure) binary .cleanup graph = .error (.mismatch 4) := by rfl'

theorem preparation_fault_rejected : Scope.checked
    [.prepare { origin := .scratch } (.error (.preparation .incomplete : Failure))]
    (.preparation .incomplete) binary .cleanup graph =
      .error (.preparation (.preparation .incomplete) { origin := .scratch } 1) := by rfl'

def stopped := captured success 0 7 true source buffer items .cleanup before

theorem physical_suspension_rejected : checked stopped [] [] request .cleanup graph =
    .error (.scope (.preparation (.preparation .incomplete) { origin := .allocation, owner := .lookup, owned := true } 2)) ∧
    stopped.2.effects.session.effects = 17 ∧ stopped.2.effects.session.heap 4 = some ⟨7, .arguments items⟩ :=
  ⟨by rfl', by rfl', by rfl'⟩

def temporaryFailure := captured (external (fun _ => true)) 160 7 true source buffer items .lookup before

theorem temporary_oom_accepted : checked temporaryFailure [] [] request .lookup graph =
    .ok (.error .outOfMemory, ⟨{}, { graph with allocationCursor := 1 }⟩) ∧
    temporaryFailure.2.effects.session.effects = 17 := ⟨by rfl', by rfl'⟩

def duplicateFailure := captured (external (fun _ => true)) 160 7 true ⟨0, 0, 2⟩ buffer [3, 1] .cleanup before

theorem ordinary_oom_accepted : checked duplicateFailure [] [] binary .cleanup graph =
    .ok (.error .outOfMemory, ⟨⟨some { origin := .scratch, dead := true }, [1, 3], .lookup⟩,
      { graph with allocationCursor := 2 }⟩) ∧ duplicateFailure.2.effects.session.effects = 13 := ⟨by rfl', by rfl'⟩

def broken := captured success 160 7 false source buffer items .cleanup ResourceAdapter.Tests.incomplete

theorem partial_copy_rejected : checked broken [] [] { request with item := ⟨0, none, 0⟩ } .cleanup graph =
    .error (.physical (.memory (.allocation (.memory .uninitialized)))) ∧
    broken.2.effects.session.effects = 17 ∧
    load broken.2.effects.session.memory ((⟨3, 0, 3⟩ : View).pointer 0) = .ok (number 3) :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem binary_represented : Represents original.memory ⟨0, 0, 2⟩ [3, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have cases : index = 0 ∨ index = 1 := by simp at inside; omega
  rcases cases with rfl | rfl <;> rfl'

/-- The replay theorem is instantiated with an actual producer, caller stack
allocation and inhabited allocator contract, not with an invented trace. -/
theorem production_add (other : Meaning) (read : Read) (sequence : BitVec 32) :
    binary.item.eval (Folding.wordMeaning other) read [1, 3] sequence =
      binary.item.eval (Folding.wordMeaning other) read [3, 1] sequence := by
  have contract := TraceBridge.production_verified success 160 7 true ⟨0, 0, 2⟩ binary .transfer original
    before.memory _ graph [] [] _ other read sequence original_valid binary_represented actual_caller_allocation
    (by rfl') (external_admitted _) rfl scratch_accepted
  obtain ⟨_, _, _, _, _, _, _, wordPreserved⟩ := contract
  exact (wordPreserved ⟨5, [1, 3]⟩ scratch_duplicate_after_sort.1).2

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge.Tests
