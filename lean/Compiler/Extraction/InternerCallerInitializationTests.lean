/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInitialization
import Compiler.Extraction.InternerCallerTests
import Compiler.Extraction.NormalizationHostScopeTests
import Compiler.Extraction.NormalizationPreparedTests
import Compiler.Extraction.NormalizationPreparedMemoryTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Normalization.Tests
open ResourceAdapter

def observed (host : External Nat) (budget : Nat) (commutative : Bool) (source : View)
    (values : List NodeId) (history : List HostTrace.Event := []) :=
  capture (HostTrace.record host) budget 7 commutative source buffer values
    (before.mapEffects (fun effects => (⟨effects, history⟩ : HostTrace.Recorded Nat)))

def live : NormalizationOwnership.State := { origin := .allocation, owned := true, owner := .lookup }

theorem temporary_live :
    let ran := observed success 160 true source items
    ran.1 = .ok (some live) ∧
    observeInit ran.1 ran.2.effects = some (.ok ⟨⟨4, 0, 3⟩, [1, 2, 3], some ⟨4, [1, 2, 3]⟩⟩) ∧
    ran.2.events = [.allocate .temporary true, .prepare live (.ok ())] ∧
    ran.2.effects.session.effects.events = [.allocate .temporary 12 (some 64)] ∧
    ran.2.effects.session.heap 4 = some ⟨7, .arguments [1, 2, 3]⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem scratch_live :
    let history : List HostTrace.Event := [.itemFree 77, .itemFree 88]
    let ran := observed success 160 true ⟨0, 0, 2⟩ [3, 1] history
    ran.1 = .ok (some { origin := .scratch }) ∧
    observeInit ran.1 ran.2.effects = some (.ok ⟨⟨3, 0, 2⟩, [1, 3], none⟩) ∧
    ran.2.events = [.prepare { origin := .scratch } (.ok ())] ∧
    ran.2.effects.session.effects.events = history := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem borrowed_live :
    let ran := observed success 0 false source items
    ran.1 = .ok (some {}) ∧ ran.2.events = [] ∧
    observeInit ran.1 ran.2.effects = some (.ok ⟨source, items, none⟩) ∧
    ran.2.effects.session.effects.events = [] := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem ordinary_oom :
    let ran := observed (external (fun _ => true)) 160 true source items
    ran.1 = .ok none ∧ observeInit ran.1 ran.2.effects = some (.error .outOfMemory) ∧
    ran.2.events = [.allocate .temporary false] ∧
    ran.2.effects.session.effects = (⟨17, [.allocate .temporary 12 none]⟩ : HostTrace.Recorded Nat) :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem invalid_response :
    let ran := observed HostTrace.Tests.invalid 160 true source items
    ran.1 = .ok none ∧ observeInit ran.1 ran.2.effects = some (.error (.allocation (.memory .memoryValidity))) ∧
    ran.2.effects.session.effects.events = [.allocate .temporary 12 (some 0)] := ⟨by rfl', by rfl', by rfl'⟩

theorem incomplete_keeps_live_allocation :
    let ran := observed success 0 true source items
    ran.1 = .error (.preparation .incomplete, live) ∧
    observeInit ran.1 ran.2.effects = some (.error (.preparation .incomplete)) ∧
    ran.2.events = [.allocate .temporary true, .prepare live (.error (.preparation .incomplete))] ∧
    ran.2.effects.session.effects.events = [.allocate .temporary 12 (some 64)] ∧
    ran.2.effects.session.heap 4 = some ⟨7, .arguments items⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem partial_copy :
    let ran := capture (HostTrace.record success) 160 7 true source buffer items
      (({ original with memory := Duplication.Tests.incomplete } : Session Nat).mapEffects
        (fun effects => (⟨effects, []⟩ : HostTrace.Recorded Nat)))
    observeInit ran.1 ran.2.effects = some (.error (.preparation (.memory .uninitialized))) ∧
    ran.2.effects.session.effects.events = [.allocate .temporary 12 (some 56)] ∧
    load ran.2.effects.session.memory ((⟨3, 0, 3⟩ : View).pointer 0) = .ok (number 3) ∧
    load ran.2.effects.session.memory ((⟨3, 0, 3⟩ : View).pointer 1) = .error .uninitialized :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem caller_observation (host : External σ) (budget allocator : Nat) (before : OwnedCall.State σ) :
    let ran := capture host budget allocator true source buffer OwnedCall.Tests.request.arguments before.world.memory
    (observeInit ran.1 ran.2.effects).map (fun result =>
      let world := { before.world with memory := ran.2.effects.session }
      match result with
      | .error failure => (.error (memoryFault failure), { before with world })
      | .ok handle => (.ok handle.values, ⟨world, { lookup := some handle }⟩)) =
      some (Caller.initLookup host budget allocator source buffer OwnedCall.Tests.request before) :=
  caller host budget allocator true source buffer OwnedCall.Tests.request before rfl

def callerBefore : OwnedCall.State Nat := ⟨OwnedCall.Tests.world, { lookup := none }⟩

theorem caller_retains_temporary :
    let ran := Caller.initLookup success 160 7 source buffer OwnedCall.Tests.request callerBefore
    ran.1 = .ok [1, 2, 3] ∧
    ran.2.scope.lookup = some ⟨⟨4, 0, 3⟩, [1, 2, 3], some ⟨4, [1, 2, 3]⟩⟩ ∧
    ran.2.world.memory.effects = 17 ∧ ran.2.world.graph = callerBefore.world.graph :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem caller_fault_keeps_scope :
    let scope : Local := ⟨some ⟨source, items, none⟩, some ⟨99, [42]⟩, true⟩
    let initial := { callerBefore with scope }
    let ran := Caller.initLookup success 0 7 source buffer OwnedCall.Tests.request initial
    ran.1 = .error (.memory (.preparation .incomplete)) ∧ ran.2.scope = scope ∧
    ran.2.world.memory.heap 4 = some ⟨7, .arguments items⟩ ∧ ran.2.world.memory.effects = 17 :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.Initialization.Tests
