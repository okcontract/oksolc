/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInvocationTrace
import Compiler.Extraction.InternerPublicationSuccess
import Compiler.Extraction.InternerCallerScopedClose

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open Interner.InvocationTrace

-- Compose the existing execution and cleanup interfaces without unfolding
-- complete native calls while diagnosing an incorrect binding.
attribute [local irreducible] Publication.publish Caller.Close.capture

/-- Bind the logical publication slot to the original probe on the actual
reached native memory. Existing publication refinement supplies both results
and the graph; no allocation policy or final graph is assumed. -/
theorem publish_stream (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) (before : World (Effects σ))
    (leading trailing : List (Event Failure ι))
    (valid : Valid before.memory) (input : Input allocator source key owned before)
    (live : SliceValid allocator before.memory.heap owned) :
    let response := hostProbe key (forget before.memory)
    let events := leading ++ [.publicationProbe key response.1] ++ trailing
    let actual := Publication.publish hostProbe host allocator source key owned id before
    let logical := Interner.InvocationTrace.publish events key id { before.graph with allocationCursor := leading.length }
    actual.1 = logical.1.mapError Fault.language ∧
      logical.2 = { actual.2.graph with allocationCursor := leading.length + 1 } ∧
      actual.1 = (if response.1 then .ok () else .error (.language .outOfMemory)) := by
  intro response events actual logical
  have projected := publish_projection hostProbe host allocator source key owned id before response.1 response.2 valid input live rfl
  have result := congrArg Prod.fst projected
  have graph := congrArg Prod.snd projected
  change actual.2.graph = (Interner.publish response.1 key id before.graph).2 at graph
  have replayed := publish_slot leading trailing key id response.1 before.graph
  change logical = _ at replayed
  refine ⟨?_, ?_, ?_⟩
  · rw [replayed]; exact result
  · rw [replayed, graph]
  · rw [result]
    cases accepted : response.1 <;> rfl

/-- The publication tail hands off only on success. Probe refusal keeps caller
ownership until the existing deferred cleanup frees the incoming slice. Both
branches consume close at the cursor derived from the actual publication slot. -/
theorem closed_publish_stream (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (values : List NodeId) (key : Key) (owned : ArgumentSlice) (id : NodeId)
    (before : World (Effects σ)) (handle : Handle) (lookup : NormalizationOwnership.State)
    (leading trailing : List (Event Failure ι))
    (held : Held allocator source values owned before) (input : Input allocator source key owned before)
    (detached : handle.owned = none) (unowned : lookup.owned = false) (owner : lookup.owner = .caller) :
    let response := hostProbe key (forget before.memory)
    let actual := Publication.publish hostProbe host allocator source key owned id before
    let body := (do let _ ← graph (fun slice => Publication.publish hostProbe host allocator source key slice id); handoff : Action (Effects σ) Unit)
      ⟨before, ⟨some handle, some owned, false⟩⟩
    let phase : NormalizationOwnership.Exit := if response.1 then .transfer else .cleanup
    let close := Caller.Close.capture (external host) allocator lookup phase handle body.2
    let closeLeading := leading ++ [.publicationProbe key response.1]
    let events := closeLeading ++ close.2.events.map Event.normalization ++ trailing
    let resources := Interner.InvocationTrace.resources events (.preparation .incomplete)
    let logical := (do let _ ← Interner.Scoped.liftGraph (Interner.InvocationTrace.publish events key id); Interner.Scoped.handoff)
      ⟨⟨some lookup, handle.values, .cleanup⟩, { before.graph with allocationCursor := leading.length }⟩
    body.1 = actual.1 ∧ body.2 = ⟨actual.2, ⟨some handle, some owned, response.1⟩⟩ ∧
    body.1 = logical.1.mapError Fault.language ∧
    logical.2 = ⟨⟨some lookup, handle.values, phase⟩, { body.2.world.graph with allocationCursor := closeLeading.length }⟩ ∧
    ∃ after, finish (external host) allocator body.1 body.2 = (body.1, after) ∧
      CleanupPost (external host) allocator source values owned body.2 after ∧
      after.world.memory = close.2.effects.session ∧
      Caller.Close.checked close (normalizations closeLeading) (normalizations trailing) lookup phase handle.values logical.2.heap =
        .ok (Interner.Scoped.close resources logical.2) := by
  intro response actual body phase close closeLeading events resources logical
  have publication := publish_stream hostProbe host allocator source key owned id before leading
    (close.2.events.map Event.normalization ++ trailing) held.1.1 input held.2.1
  have ordinaryResult : ordinary actual.1 = true := by
    rw [publication.2.2]
    cases response.1 <;> rfl
  have kept := publish_held hostProbe host allocator source values key owned id before held ordinaryResult
  have native : body = (actual.1, ⟨actual.2, ⟨some handle, some owned, response.1⟩⟩) := by
    cases ran : Publication.publish hostProbe host allocator source key owned id before with
    | mk result after =>
      have resultEq : result = (if response.1 then .ok () else .error (.language .outOfMemory)) := by
        simpa only [actual, ran] using publication.2.2
      simp only [body, actual, bind, Effect.bind, graph, ran, handoff, resultEq]
      cases response.1 <;> rfl
  have projected : body.1 = logical.1.mapError Fault.language ∧
      logical.2 = ⟨⟨some lookup, handle.values, phase⟩, { body.2.world.graph with allocationCursor := closeLeading.length }⟩ := by
    have replayed : Interner.InvocationTrace.publish events key id { before.graph with allocationCursor := leading.length } =
        (let ran := Interner.publish response.1 key id before.graph
         (ran.1, { ran.2 with allocationCursor := leading.length + 1 })) := by
      simpa only [events, closeLeading, List.append_assoc] using
        publish_slot leading (close.2.events.map Event.normalization ++ trailing) key id response.1 before.graph
    have graph : (Interner.InvocationTrace.publish events key id { before.graph with allocationCursor := leading.length }).2 =
        { actual.2.graph with allocationCursor := leading.length + 1 } := by
      simpa only [events, closeLeading, List.append_assoc] using publication.2.1
    rw [replayed] at graph
    simp only [logical, Interner.Scoped.liftGraph, bind, Effect.bind, replayed, Interner.Scoped.handoff, native,
      phase, closeLeading, List.length_append, List.length_singleton]
    rw [publication.2.2]
    cases accepted : response.1 <;> simp only [accepted, Interner.publish, Bool.false_eq_true, ↓reduceIte, Except.mapError] at graph ⊢
    all_goals exact ⟨trivial, congrArg (Interner.Scoped.Session.mk _) graph⟩
  have post : Post allocator source values owned handle body := by
    rw [native]
    exact ⟨rfl, rfl, fun _ => ⟨kept.1, fun _ => kept.2.1⟩⟩
  have completed : ordinary body.1 = true := by rw [native]; exact ordinaryResult
  have completion := Caller.Close.of_post (external host) allocator source values lookup handle owned body
    detached unowned owner post held.2.2 completed (normalizations closeLeading) (normalizations trailing)
  have closed := Caller.ScopeProjection.close_completion (external host) allocator source values lookup handle owned body
    (fun _ => closeLeading.length) (normalizations closeLeading) (normalizations trailing) logical.2 completion
    (by simpa only [Caller.ScopeProjection.scopeAt, Recursive.cursorGraph, native, phase, normalizations_length] using projected.2)
    (by simp only [normalizations_length])
  refine ⟨congrArg Prod.fst native, congrArg Prod.snd native, projected.1, projected.2, ?_⟩
  simpa only [close, native, phase, resources, events, Interner.InvocationTrace.resources, normalizations_append,
    normalizations_embed, projected.2, List.append_assoc] using closed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
