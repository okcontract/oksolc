/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerTakeStream
import Compiler.Extraction.InternerCallerInitializationScopeTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace Normalization.Tests
open OwnedCall.Tests (request world)

def initialized := Caller.initLookup success 160 7 source buffer request ⟨world, { lookup := none }⟩
def prefixEvents := (Initialization.capture success 160 7 true source buffer items world.memory).2.events
def ownedHandle := (Initialization.capture success 160 7 true source buffer items world.memory).2.effects.handle
def borrowed : Handle := ⟨source, items, none⟩
def takenScope : Except Interner.Error Unit × Interner.Scoped.Session :=
  (.ok (), ⟨⟨some { origin := .allocation, owner := .caller }, [1, 2, 3], .cleanup⟩,
    { world.graph with allocationCursor := 2 }⟩)

theorem owned_no_events :
    let execution := capture success 7 .allocation ownedHandle initialized.2.world.memory
    execution.2.events = [] ∧ execution.2.effects.session = initialized.2.world.memory ∧
      observeTake execution.1 execution.2.effects = some (.ok (⟨4, [1, 2, 3]⟩, { ownedHandle with owned := none })) := ⟨by rfl', by rfl', by rfl'⟩

theorem allocated_accepted :
    checked (capture success 7 .allocation ownedHandle initialized.2.world.memory) prefixEvents []
      (token .allocation ownedHandle) [1, 2, 3] { world.graph with allocationCursor := 2 } = .ok takenScope := by rfl'

theorem borrowed_duplicate :
    let execution := capture (HostTrace.record success) 7 .input borrowed
      (before.mapEffects (fun effects => (⟨effects, [.itemFree 91]⟩ : HostTrace.Recorded Nat)))
    execution.2.events = [.allocate .duplicate true] ∧ execution.2.effects.session.effects.events.length = 2 ∧
      observeTake execution.1 execution.2.effects = some (.ok (⟨4, items⟩, borrowed)) := ⟨by rfl', by rfl', by rfl'⟩

theorem empty_protocol_event :
    let handle : Handle := ⟨⟨900, 90, 0⟩, [], none⟩
    let execution := capture (HostTrace.record success) 7 .input handle
      (before.mapEffects (fun effects => (⟨effects, []⟩ : HostTrace.Recorded Nat)))
    execution.2.events = [.allocate .duplicate true] ∧ execution.2.effects.session.effects.events = [] ∧
      observeTake execution.1 execution.2.effects = some (.ok (⟨4, []⟩, handle)) := ⟨by rfl', by rfl', by rfl'⟩

theorem scratch_duplicate :
    let handle : Handle := ⟨⟨3, 0, 2⟩, [1, 3], none⟩
    let execution := capture success 7 .scratch handle scratchPrepared
    observeTake execution.1 execution.2.effects = some (.ok (⟨5, [1, 3]⟩, handle)) ∧
      execution.2.effects.session.effects = 13 := ⟨by rfl', by rfl'⟩

def refusedScope : Except Interner.Error Unit × Interner.Scoped.Session :=
  (.error .outOfMemory, ⟨⟨some {}, items, .lookup⟩, { world.graph with allocationCursor := 1 }⟩)

theorem ordinary_oom :
    let execution := capture (external (fun _ => true)) 7 .input borrowed before
    execution.2.effects.session.effects = 17 ∧
      checked execution [] [] (token .input borrowed) items world.graph = .ok refusedScope := ⟨by rfl', by rfl'⟩

theorem invalid_rejected :
    checked (capture HostTrace.Tests.invalid 7 .input borrowed before) [] [] (token .input borrowed) items world.graph =
      .error (.physical (.memory (.allocation (.memory .memoryValidity)))) := by rfl'

theorem partial_copy_rejected :
    let execution := capture success 7 .input borrowed { before with memory := Duplication.Tests.incomplete }
    execution.2.effects.session.effects = 17 ∧
      checked execution [] [] (token .input borrowed) items world.graph =
        .error (.physical (.memory (.allocation (.memory .uninitialized)))) := ⟨by rfl', by rfl'⟩

theorem unbound_cursor_rejected :
    checked (capture success 7 .input borrowed before) [] [] (token .input borrowed) items
      { world.graph with allocationCursor := 1 } = .error (.scope (.mismatch 2)) := by rfl'

theorem missing_event_rejected :
    let execution := capture success 7 .input borrowed before
    checked (execution.1, { execution.2 with events := [] }) [] [] (token .input borrowed) items world.graph =
      .error (.scope (.mismatch 1)) := by rfl'

theorem borrowed_ready : Ready 7 source items borrowed before :=
  ⟨ready_caller.1, ready_caller.2.1, ready_caller.2.1, by intros; contradiction, by intros; contradiction⟩

theorem borrowed_admitted (fail : NormalizationOwnership.Allocation → Bool) (leading suffix : List (Event Failure)) :
    let execution := capture (external fail) 7 .input borrowed before
    let graph := { world.graph with allocationCursor := leading.length }
    checked execution leading suffix (token .input borrowed) items graph =
      .ok (Interner.Scoped.take (Scope.resources (leading ++ (execution.2.events ++ suffix)) (.preparation .incomplete))
        ⟨⟨some (token .input borrowed), items, .lookup⟩, graph⟩) :=
  checked_ready (external fail) 7 .input source items borrowed before leading suffix _ borrowed_ready (external_admitted fail) rfl

theorem initializer_handle : initialized.2.scope.lookup = some ownedHandle := by rfl'
theorem initializer_token : token .allocation ownedHandle = Initialization.Tests.live := by rfl'
theorem initializer_result : initialized.1 = .ok [1, 2, 3] := by rfl'
attribute [local irreducible] Caller.initLookup
theorem initializer_execution : Caller.initLookup success 160 7 source buffer request ⟨world, { lookup := none }⟩ =
    (.ok [1, 2, 3], initialized.2) := by
  apply Prod.ext
  · exact initializer_result
  · rfl
theorem initializer_recorded :
    (Initialization.capture success 160 7 true source buffer request.arguments world.memory).1 =
      .ok (some Initialization.Tests.live) := by rfl'
theorem scope_position : Initialization.ScopeTests.allocatedScope.2.heap.allocationCursor = prefixEvents.length := by rfl'

/-- The same borrowed refusal fixture entered through native initialization. -/
def borrowedRequest : Interner.Request := { request with item := ⟨0, none, 0⟩ }

theorem borrowed_initialized : Caller.initLookup (external (fun _ => true)) 160 7 source buffer borrowedRequest
    ⟨world, { lookup := none }⟩ = (.ok items, ⟨world, { lookup := some borrowed }⟩) := by rfl'

theorem borrowed_recorded : Initialization.capture (external (fun _ => true)) 160 7 false source buffer
    borrowedRequest.arguments world.memory = (.ok (some {}), ⟨⟨before, borrowed, none, none⟩, []⟩) := by rfl'

attribute [local irreducible] Coupled capture Initialization.Coupled Initialization.capture
attribute [local irreducible] Interner.Scoped.initScope Interner.Scoped.take Scope.resources initialized

theorem coupled_oom :
    let execution := capture (external (fun _ => true)) 7 .input borrowed before
    Coupled 7 source items borrowed world (0 + execution.2.events.length) execution.2.effects.session execution.1
      (OwnedCall.take (external (fun _ => true)) 7 ⟨world, { lookup := some borrowed }⟩) refusedScope := by
  have result := initialized_stream (external (fun _ => true)) 160 7 false source borrowedRequest OwnedCall.Tests.caller
    before.memory _ items ⟨world, { lookup := some borrowed }⟩ [] []
    ⟨fun _ _ _ => none, fun _ _ _ _ => none⟩ (fun _ => none) 0
    original_valid Allocation.Tests.represented actual_caller_allocation rfl (external_admitted _) borrowed_initialized
  dsimp only at result
  have recorded : Initialization.capture (external (fun _ => true)) 160 7 false source
      ⟨OwnedCall.Tests.caller.memory.memory.nextId, 0, 2⟩ borrowedRequest.arguments
      { OwnedCall.Tests.caller.memory with memory := before.memory } =
        (.ok (some {}), ⟨⟨before, borrowed, none, none⟩, []⟩) := borrowed_recorded
  simp only [recorded] at result
  obtain ⟨lookup, captured, _, _, _, _, initialKnown, accepted, coupled⟩ := result
  have sameLookup := Option.some.inj (Except.ok.inj captured)
  subst lookup
  unfold Initialization.Coupled at initialKnown
  rw [initialKnown.2.2.2.1] at accepted
  have same := Except.ok.inj (accepted.symm.trans ordinary_oom.2)
  simpa only [same] using coupled

theorem initialized_add (other : Meaning) (read : Read) (sequence : BitVec 32) :
    ∃ handle, ∃ lookup : NormalizationOwnership.State, initialized.2.scope.lookup = some handle ∧
      request.item.eval (Folding.wordMeaning other) read handle.values sequence =
        request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
      let execution := capture success 7 lookup.origin handle initialized.2.world.memory
      Coupled 7 source request.arguments handle initialized.2.world (prefixEvents.length + execution.2.events.length)
        execution.2.effects.session execution.1 (OwnedCall.take success 7 initialized.2) takenScope := by
  obtain ⟨lookup, captured, present, contents, word, _, initialKnown, accepted, coupled⟩ :=
    initialized_stream success 160 7 true source request OwnedCall.Tests.caller before.memory _ [1, 2, 3] initialized.2 [] []
      other read sequence original_valid Allocation.Tests.represented actual_caller_allocation rfl (external_admitted _)
      initializer_execution
  have sameLookup := Option.some.inj (Except.ok.inj (initializer_recorded.symm.trans captured))
  subst lookup
  unfold Initialization.Coupled at initialKnown
  rw [initialKnown.2.2.2.1] at accepted
  have prefixLength : prefixEvents.length = 2 := scope_position.symm
  have expected := allocated_accepted
  rw [initializer_token] at expected
  change checked (capture success 7 .allocation ownedHandle initialized.2.world.memory) ([] ++ prefixEvents) []
    Initialization.Tests.live [1, 2, 3] { world.graph with allocationCursor := [].length + prefixEvents.length } = .ok _ at accepted
  simp only [List.nil_append, List.length_nil, Nat.zero_add, prefixLength] at accepted
  have same := Except.ok.inj (accepted.symm.trans expected)
  change ownedHandle.values = [1, 2, 3] at contents
  refine ⟨ownedHandle, Initialization.Tests.live, present, ?_, ?_⟩
  · simpa only [contents] using word
  · rw [← same]
    simpa only [List.nil_append] using coupled

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Take.Tests
