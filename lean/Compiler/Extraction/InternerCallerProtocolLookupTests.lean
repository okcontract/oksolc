/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.LookupTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Interner.InvocationTrace ConstructorItem
open Publication.OriginTests (Case source request key sorted)

/-- Exercise the shared proof through all six existing ownership inputs, with
arbitrary history, suffix, graph observations and ordinary classifier errors.
The cache result is the existing real table entry. Graph callbacks are poisoned.
No new native preparation or allocation fixture is introduced. -/
theorem existing_family (case : Case) (observations : GraphObservations (Publication.Effects Nat))
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (result : Except Interner.Error NodeId) (hit : ∀ id, result = .ok id → id = 17)
    (completed : ordinary (result.mapError Fault.language) = true) :
    let q := { Interner.Queries.queries with deterministic := fun _ => result.map (fun _ => true) }
    let model := { CacheStream.Tests.model with deterministic := fun _ => result.map (fun _ => true) }
    let actual := find CacheStream.Tests.host 160 11 CacheTests.poison q observations (source case)
      ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case)
      ⟨⟨CacheStream.Tests.start case, { lookup := none }⟩, {}, leading⟩
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) model
      (request case) { (CacheTests.constructed case).graph with allocationCursor := leading.length }
    actual.1 = result.mapError Fault.language ∧ Good (source case) (request case).arguments actual.2.native.world ∧
      Closed actual.2.native.scope ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro q model actual logical
  have observed := CacheTests.prefix_observed case
  have good := Publication.OriginTests.initial_good case
  have item := (ConstructorItem.prepare_success (request case).item CacheTests.debug (CacheTests.before case)
    (CacheTests.constructed case) CacheTests.address good.1
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) AssemblyItem.Initializers.Tests.debug_valid observed.1).2
  have ready := good_frame _ _ (source case) (request case).arguments good item.valid item.memory
  have initialized : Caller.initLookup CacheStream.Tests.host 160 11 (source case)
      ⟨(CacheTests.constructed case).memory.memory.nextId, 0, 2⟩ (request case)
      ⟨CacheStream.Tests.start case, { lookup := none }⟩ =
      (.ok (sorted case), (CacheTests.prepared case Normalization.Tests.success 160).2) := by
    rw [observed.2.1]
    exact Prod.ext observed.2.2.2.1 rfl
  exact lookup_projected CacheStream.Tests.host 160 11 (CacheStream.Tests.commutes case) CacheTests.poison q observations model
    (source case) (request case) (CacheTests.constructed case) (CacheTests.stack case) _ (sorted case)
    (CacheTests.prepared case Normalization.Tests.success 160).2 result leading trailing other read sequence
    ready.1 ready.2 observed.2.2.1 (by cases case <;> rfl)
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _)) initialized observed.2.2.2.2.1 rfl
    (by intro id returned; rw [hit id returned]; exact ⟨key case, observed.2.2.2.2.2.2.1, observed.2.2.2.2.2.2.2⟩)
    completed rfl rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.LookupTests
