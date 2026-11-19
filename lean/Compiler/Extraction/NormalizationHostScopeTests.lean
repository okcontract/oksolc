/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationHostScope
import Compiler.Extraction.NormalizationTraceTests
import Compiler.Extraction.NormalizationHostTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge.HostScope.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open NormalizationOwnership.Trace Normalization.Tests
open TraceBridge.Tests (request binary graph)

def initial (history : List HostTrace.Event := []) :=
  before.mapEffects (fun effects => (⟨effects, history⟩ : HostTrace.Recorded Nat))

def observed (host : External Nat) (budget : Nat) (commutative : Bool) (source : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) (history : List HostTrace.Event := []) :=
  capture host budget 7 commutative source buffer values exit (initial history)

/-- The combined observation retains exactly the pre-existing host fixture's
execution, for every outcome and budget; no concrete trace is substituted. -/
theorem existing_native_execution (host : External Nat) (budget : Nat) (commutative : Bool) (source : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) :
    let ran := observed host budget commutative source values exit
    (ResourceAdapter.observe ran.1 ran.2.effects, ran.2.effects.session) =
      (some (HostTrace.Tests.observed host budget commutative source values exit).1,
        (HostTrace.Tests.observed host budget commutative source values exit).2) :=
  capture_native (HostTrace.record host) budget 7 commutative source buffer values exit (initial [])

theorem original_native_execution (host : External Nat) (budget : Nat) (commutative : Bool) (source : View)
    (values : List NodeId) (exit : NormalizationOwnership.Exit) :
    let ran := observed host budget commutative source values exit
    let native := Normalization.run normalizationOwnershipCode host budget 7 commutative source buffer values exit before
    (some native.1, native.2) =
      (ResourceAdapter.observe ran.1 ran.2.effects, ran.2.effects.session.mapEffects HostTrace.Recorded.effects) :=
  erases host budget 7 commutative source buffer values exit (initial [])

def empty (history : List HostTrace.Event) := observed success 160 true ⟨900, 90, 0⟩ [] .transfer history

/-- One protocol allocation succeeds without a native host call. Prior host
history is retained and cannot supply the protocol cursor or replay suffix. -/
theorem empty_channels (history : List HostTrace.Event) :
    (empty history).2.events = [.allocate .duplicate true] ∧
    (empty history).2.effects.session.effects.events = history ∧
    (empty history).2.effects.session.effects.effects = 5 := ⟨by rfl', by rfl', by rfl'⟩

theorem empty_scope_cursor :
    checked (empty [.itemFree 77, .itemFree 88]) [.release {}] [.allocate .temporary false]
      { request with arguments := [] } .transfer { graph with allocationCursor := 1 } =
      .ok (.ok .transferred, ⟨⟨some { owner := .caller, dead := true }, [], .transfer⟩,
        { graph with allocationCursor := 2 }⟩) := by rfl'

def scratch := observed success 160 true ⟨0, 0, 2⟩ [3, 1] .transfer

theorem scratch_channels : scratch.2.events = [.prepare { origin := .scratch } (.ok ()), .allocate .duplicate true] ∧
    scratch.2.effects.session.effects.events = [.allocate .duplicate 8 (some 76)] := ⟨by rfl', by rfl'⟩

theorem scratch_accepted : checked scratch [] [] binary .transfer graph =
    .ok (Scope.run (Scope.resources scratch.2.events (.preparation .incomplete)) binary .transfer graph) := by rfl'

def cleanup := observed success 160 true source items .cleanup

theorem cleanup_channels : cleanup.2.events = [.allocate .temporary true,
    .prepare { origin := .allocation, owner := .lookup, owned := true } (.ok ()),
    .release { origin := .allocation, owner := .caller }] ∧
    cleanup.2.effects.session.effects.events = [.allocate .temporary 12 (some 64), .free ⟨4, [1, 2, 3]⟩] :=
  ⟨by rfl', by rfl'⟩

def oom := observed (external (fun _ => true)) 160 true source items .cleanup

theorem ordinary_oom_channels : checked oom [] [] request .cleanup graph =
    .ok (.error .outOfMemory, ⟨{}, { graph with allocationCursor := 1 }⟩) ∧
    oom.2.effects.session.effects = (⟨17, [.allocate .temporary 12 none]⟩ : HostTrace.Recorded Nat) := ⟨by rfl', by rfl'⟩

def invalid := observed HostTrace.Tests.invalid 160 true source items .cleanup

theorem invalid_response_rejected : checked invalid [] [] request .cleanup graph =
    .error (.physical (.memory (.allocation (.memory .memoryValidity)))) ∧
    invalid.2.effects.session.effects.events = [.allocate .temporary 12 (some 0)] := ⟨by rfl', by rfl'⟩

def stopped := observed success 0 true source items .cleanup

theorem incomplete_rejected : checked stopped [] [] request .cleanup graph =
    .error (.scope (.preparation (.preparation .incomplete) { origin := .allocation, owner := .lookup, owned := true } 2)) ∧
    stopped.2.effects.session.effects.events = [.allocate .temporary 12 (some 64)] ∧
    stopped.2.effects.session.heap 4 = some ⟨7, .arguments items⟩ := ⟨by rfl', by rfl', by rfl'⟩

def broken := capture success 160 7 false source buffer items .cleanup
  (ResourceAdapter.Tests.incomplete.mapEffects (fun effects => (⟨effects, []⟩ : HostTrace.Recorded Nat)))

theorem partial_copy_rejected : checked broken [] [] { request with item := ⟨0, none, 0⟩ } .cleanup graph =
    .error (.physical (.memory (.allocation (.memory .uninitialized)))) ∧
    broken.2.effects.session.effects.events = [.allocate .duplicate 12 (some 56)] ∧
    load broken.2.effects.session.memory ((⟨3, 0, 3⟩ : View).pointer 0) = .ok (number 3) := ⟨by rfl', by rfl', by rfl'⟩

/-- The existing ADD normalization meaning proof now follows from the scoped
theorem bound to the original native result and both actual transcripts. -/
theorem production_add (other : Meaning) (read : Read) (sequence : BitVec 32) :
    binary.item.eval (Folding.wordMeaning other) read [1, 3] sequence =
      binary.item.eval (Folding.wordMeaning other) read [3, 1] sequence := by
  have contract := HostScope.production_verified success 160 7 true ⟨0, 0, 2⟩ binary .transfer
    (original.mapEffects (fun effects => (⟨effects, []⟩ : HostTrace.Recorded Nat))) before.memory _ graph [] [] _ other read sequence
    (original_valid.mapEffects _) TraceBridge.Tests.binary_represented actual_caller_allocation (by rfl') (external_admitted _) rfl scratch_accepted
  obtain ⟨_, _, _, _, _, _, _, _, words⟩ := contract
  exact (words ⟨5, [1, 3]⟩ scratch_duplicate_after_sort.1).2

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter.TraceBridge.HostScope.Tests
