/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInitializationVerified
import Compiler.Extraction.InternerCallerInitializationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization.ScopeTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open ResourceAdapter NormalizationOwnership.Trace Normalization.Tests
open OwnedCall.Tests (request world)
open Initialization.Tests (observed live)

def allocatedScope : Except Interner.Error (List NodeId) × Interner.Scoped.Session :=
  (.ok [1, 2, 3], ⟨⟨some live, [1, 2, 3], .lookup⟩, { world.graph with allocationCursor := 2 }⟩)

theorem temporary_accepted : checked (observed success 160 true source items) [] [] request world.graph = .ok allocatedScope := by rfl'

theorem scratch_cursor :
    checked (observed success 160 true ⟨0, 0, 2⟩ [3, 1] [.itemFree 77, .itemFree 88])
      [.release {}] [.allocate .duplicate false] { request with arguments := [3, 1] }
      { world.graph with allocationCursor := 1 } =
      .ok (.ok [1, 3], ⟨⟨some { origin := .scratch }, [1, 3], .lookup⟩, { world.graph with allocationCursor := 2 }⟩) := by rfl'

theorem borrowed_no_events :
    checked (observed success 0 true ⟨0, 0, 1⟩ [3]) [] [.allocate .duplicate false]
      { request with arguments := [3] } world.graph =
      .ok (.ok [3], ⟨⟨some {}, [3], .lookup⟩, world.graph⟩) := by rfl'

theorem ordinary_oom : checked (observed (external (fun _ => true)) 160 true source items) [] [] request world.graph =
    .ok (.error .outOfMemory, ⟨{}, { world.graph with allocationCursor := 1 }⟩) := by rfl'

theorem invalid_rejected : checked (observed HostTrace.Tests.invalid 160 true source items) [] [] request world.graph =
    .error (.physical (.memory (.allocation (.memory .memoryValidity)))) := by rfl'

theorem incomplete_rejected : checked (observed success 0 true source items) [] [] request world.graph =
    .error (.scope (.preparation (.preparation .incomplete) live 2)) := by rfl'

theorem partial_copy_rejected :
    let execution := capture (HostTrace.record success) 160 7 true source buffer items
      (({ original with memory := Duplication.Tests.incomplete } : Session Nat).mapEffects
        (fun effects => (⟨effects, []⟩ : HostTrace.Recorded Nat)))
    checked execution [] [] request world.graph =
      .error (.scope (.preparation (.preparation (.memory .uninitialized)) live 2)) := by rfl'

theorem unbound_start_rejected :
    checked (observed success 160 true source items) [] [] request { world.graph with allocationCursor := 1 } =
      .error (.scope (.mismatch 3)) := by rfl'

theorem missing_event_rejected :
    Scope.checkedInit [] (Failure.preparation .incomplete) request world.graph = .error (.mismatch 1) := by rfl'

theorem wrong_owner_rejected :
    Scope.checkedInit [.allocate .temporary true, .prepare {} (.ok ())] (Failure.preparation .incomplete) request world.graph =
      .error (.mismatch 3) := by rfl'

theorem native_accepted :
    checked (capture success 160 7 true source buffer request.arguments world.memory) [] [] request world.graph =
      .ok allocatedScope := by rfl'

theorem native_refused :
    checked (capture (external (fun _ => true)) 160 7 true source buffer request.arguments world.memory) [] [] request world.graph =
      .ok (.error .outOfMemory, ⟨{}, { world.graph with allocationCursor := 1 }⟩) := by rfl'

-- Keep specialization at the proved interfaces; concrete traces are checked above.
attribute [local irreducible] Coupled capture

/-- The existing allocated ADD input exercises the general production theorem;
the stack producer supplies scratch facts, and all word meanings remain free. -/
theorem production_add (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let execution := capture success 160 7 true source buffer request.arguments world.memory
    let called := Caller.initLookup success 160 7 source buffer request ⟨world, { lookup := none }⟩
    Coupled 7 source request world (0 + execution.2.events.length) execution.2.effects.session called allocatedScope other read sequence := by
  have derived := production_ordinary success 160 7 true source request OwnedCall.Tests.caller before.memory _ [] []
    other read sequence original_valid Allocation.Tests.represented actual_caller_allocation rfl (external_admitted _) (by rfl')
  have same := Except.ok.inj (derived.1.symm.trans native_accepted)
  simpa only [same] using derived.2

theorem production_oom (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let host := external (fun _ => true)
    let execution := capture host 160 7 true source buffer request.arguments world.memory
    let called := Caller.initLookup host 160 7 source buffer request ⟨world, { lookup := none }⟩
    Coupled 7 source request world (0 + execution.2.events.length) execution.2.effects.session called
      (.error .outOfMemory, ⟨{}, { world.graph with allocationCursor := 1 }⟩) other read sequence := by
  have derived := production_ordinary (external (fun _ => true)) 160 7 true source request OwnedCall.Tests.caller before.memory _ [] []
    other read sequence original_valid Allocation.Tests.represented actual_caller_allocation rfl (external_admitted _) (by rfl')
  have same := Except.ok.inj (derived.1.symm.trans native_refused)
  simpa only [same] using derived.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization.ScopeTests
