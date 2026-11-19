/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublicationInvocation
import Compiler.Extraction.InternerCallerPublicationCompletionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.StreamTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Interner.InvocationTrace
open OriginTests (Case source request key before stack sorted initialized taken slice remaining)

attribute [local irreducible] Publication.publish Caller.Close.capture

/-- Reuse the six existing source caller cases and both probe outcomes. Their
incoming ownership and publication admission are derived by `caller_input`.
The scoped token is an arbitrary successful-take token supplied by the caller. -/
theorem force_closed (case : Case) (accepted : Bool) (lookup : NormalizationOwnership.State)
    (leading trailing : List (Event Failure Unit)) (unowned : lookup.owned = false) (owner : lookup.owner = .caller) :
    let host := Normalization.Tests.success
    let body := (do let _ ← graph (fun owned => Publication.publish (CompletionTests.probe accepted) host 11
      (source case) (key case) owned 42); handoff : Action (Effects Nat) Unit) (taken case).2
    let phase : NormalizationOwnership.Exit := if accepted then .transfer else .cleanup
    let close := Caller.Close.capture (external host) 11 lookup phase (remaining case) body.2
    let closeLeading := leading ++ [.publicationProbe (key case) accepted]
    let events := closeLeading ++ close.2.events.map Event.normalization ++ trailing
    let logical := (do let _ ← Interner.Scoped.liftGraph (Interner.InvocationTrace.publish events (key case) 42); Interner.Scoped.handoff)
      ⟨⟨some lookup, (remaining case).values, .cleanup⟩, { (taken case).2.world.graph with allocationCursor := leading.length }⟩
    Interner.forceCode.controlOwned (OwnedCall.execution (external host) 11
      (callbacks (CompletionTests.probe accepted) host 11 (source case) CompletionTests.seed))
      (request case) (sorted case) 42 (initialized case).2 = body ∧
    ∃ after, finish (external host) 11 body.1 body.2 = (body.1, after) ∧
      CleanupPost (external host) 11 (source case) (request case).arguments (slice case) body.2 after ∧
      after.world.memory = close.2.effects.session ∧
      Caller.Close.checked close (normalizations closeLeading) (normalizations trailing) lookup phase (remaining case).values logical.2.heap =
        .ok (Interner.Scoped.close (resources events (.preparation .incomplete)) logical.2) := by
  intro host body phase close closeLeading events logical
  have entry := OriginTests.derived_input case
  have calls := OriginTests.prefix_results case
  have checked := closed_publish_stream (CompletionTests.probe accepted) host 11 (source case) (request case).arguments
    (key case) (slice case) 42 (taken case).2.world (remaining case) lookup leading trailing
    entry.1.held entry.2 entry.1.detached unowned owner
  have shape : (⟨(taken case).2.world, ⟨some (remaining case), some (slice case), false⟩⟩ : State (Effects Nat)) =
      (taken case).2 := by rw [← entry.1.scope]
  dsimp only at checked
  rw [shape] at checked
  refine ⟨?_, checked.2.2.2.2⟩
  exact force_after_take (CompletionTests.probe accepted) host 11 (source case) CompletionTests.seed
    (request case) (sorted case) (key case) 42 (initialized case).2 (taken case).2
    (Prod.ext calls.2.2.1 rfl) calls.2.2.2.2

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication.StreamTests
