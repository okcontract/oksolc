/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublicationCompletion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- The source-bound owned continuation uses the caller's actual take and key
construction, then the same publication/handoff tail as the simplified find
branch. No new interpreter or assumed publication result is introduced. -/
theorem force_after_take (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (p : Primitives (Effects σ)) (request : Interner.Request) (values : List NodeId)
    (key : Key) (id : NodeId) (prepared taken : State (Effects σ))
    (transferred : take (external host) allocator prepared = (.ok (), taken))
    (made : Interner.makeKey request values = .ok key) :
    Interner.forceCode.controlOwned (OwnedCall.execution (external host) allocator (callbacks hostProbe host allocator source p))
      request values id prepared =
      (do let _ ← graph (fun slice => publish hostProbe host allocator source key slice id); handoff : Action (Effects σ) Unit) taken := by
  simp only [Interner.ForceCode.controlOwned, OwnedCall.execution, bind, Effect.bind, transferred,
    made, Except.mapError, callbacks, Interner.forceCode, Interner.ResultId.run]

/-- Complete the actual owned publication continuation and outer defers from
the caller's stack allocation and normalization. All incoming ownership,
freshness, global key liveness/uniqueness after publication, native frames and
cleanup preconditions are derived. Initial graph/key invariants remain explicit;
cache routing and recursive child preservation are outside this endpoint. -/
theorem caller_owned_publication (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (budget allocator : Nat) (source : View) (p : Primitives (Effects σ))
    (request : Interner.Request) (before : World (Effects σ)) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared taken : State (Effects σ))
    (key : Key) (id : NodeId) (accepted : Bool) (effects : σ)
    (good : Good source request.arguments before) (admitted : Admitted host)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup (external host) budget allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : take (external host) allocator prepared = (.ok (), taken))
    (made : Interner.makeKey request values = .ok key)
    (live : OwnedKeys.Live allocator ⟨before.memory.effects.keys, before.memory.heap⟩)
    (unique : OwnedKeys.Unique before.memory.effects.keys)
    (sourceApart : ∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] →
      source.length ≠ 0 → source.allocation ≠ old.address)
    (response : hostProbe key (forget taken.world.memory) = (accepted, effects)) :
    ∃ owned remaining after,
      Caller.Origin allocator source request values before taken owned remaining ∧
      (let (result, reached) := Interner.forceCode.controlOwned
          (OwnedCall.execution (external host) allocator (callbacks hostProbe host allocator source p)) request values id prepared
       finish (external host) allocator result reached) =
          (if accepted then .ok () else .error (.language .outOfMemory), after) ∧
      Completion host allocator source request key owned id before taken.world accepted effects after ∧
      (before.graph.table = OwnedKeys.view before.memory.effects.keys →
        after.world.graph.table = OwnedKeys.view after.world.memory.effects.keys) := by
  obtain ⟨owned, remaining, origin, keys, input⟩ := caller_input host budget allocator source request before memory pointer values prepared taken key
    good admitted allocated initialized transferred made (live key) sourceApart
  obtain ⟨after, finished, completed⟩ := complete_taken hostProbe host allocator source request values key owned remaining id before taken accepted effects
    origin input keys live unique response
  refine ⟨owned, remaining, after, origin, ?_, completed, ?_⟩
  · rw [force_after_take hostProbe host allocator source p request values key id prepared taken transferred made]
    exact finished
  · intro linked
    exact completed.linked host allocator source request key owned id before taken.world accepted effects after
      (by rw [origin.graph, keys]; exact linked)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
