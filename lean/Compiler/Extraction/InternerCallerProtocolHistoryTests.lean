/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveProtocolMiss
import Compiler.Extraction.InternerCallerResourceReplay
import Compiler.Extraction.InternerInvocationChildTraceTests
import Compiler.Extraction.InternerCallerProtocolMissTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.HistoryTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

/-- A child may leave its native world unchanged while emitting a nonempty
protocol segment. The nested histories retain their distinct earlier prefixes,
for success, OOM and semantic failure alike. -/
theorem unchanged_native (before : World (Publication.Effects σ)) (result : Except Fault NodeId)
    (inner outer events : List ProtocolEvent) :
    let action : GraphAction (Publication.Effects σ) NodeId := fun world => (result, world)
    let observed := ChildTrace.record (ChildTrace.record action (fun _ => events)) (fun _ => events)
      (ChildTrace.restore outer (ChildTrace.restore inner before))
    observed.1 = result ∧ ChildTrace.erase (ChildTrace.erase observed.2) = before ∧
      ChildTrace.history observed.2 = outer ++ events ∧
      ChildTrace.history (ChildTrace.erase observed.2) = inner ++ events ∧
      observed.2.mapEffects (Publication.Effects.mapAllocator ChildTrace.flatten) = ChildTrace.restore (outer ++ events) before := by
  simp only [ChildTrace.record, ChildTrace.erase_restore]
  exact ⟨trivial, trivial, rfl, rfl, rfl⟩

set_option maxRecDepth 2048 in
/-- The existing effectful dispatcher fixture supplies a real child event in
both success and failure. Earlier history is not recounted; a skipped guard
does not call or observe the child. These markers test routing, not admission. -/
theorem guarded_history (ops : Insertion.Operations (ChildTrace.Recorded Nat ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded Nat ProtocolEvent)) (safety : Bool) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects (ChildTrace.Recorded Nat ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded Nat ProtocolEvent)))
    (failure : Option Fault) (deterministic : Bool) (earlier : List ProtocolEvent) (start : Nat) :
    let children := ChildTrace.Tests.children (failure.map (fun fault => (0, fault)))
    let observations := ChildTrace.Tests.observations
    let before := ChildTrace.restore earlier ChildTrace.Tests.initial
    let request := Interner.constructorCode.operationRequest 24 [1, 1]
    let key : Key := ⟨1, 24, 0, [1, 1], 0⟩
    let slice : ArgumentSlice := ⟨0, [1, 1]⟩
    let p := Native.physical ops allocate safety 3 meaning base growth 64 (ChildTrace.constructors children observations) ConstructorItem.CacheTests.debug
      Publication.Tests.source ⟨0, 0⟩ (ConstructorItem.input Publication.Tests.request.item ConstructorItem.CacheTests.debug)
    let events := Native.middle ops allocate safety 3 meaning base growth 64 (ChildTrace.constructors children observations)
      (ChildTrace.liftObservations observations) ConstructorItem.CacheTests.debug Publication.Tests.source ⟨0, 0⟩
      (ConstructorItem.input Publication.Tests.request.item ConstructorItem.CacheTests.debug) request key slice deterministic before
    events = (if deterministic then [ChildTrace.Tests.marker 0] else []) ∧
      ChildTrace.history (MissStream.selected p request key slice deterministic before).2 = earlier ++ events ∧
      MissStream.childCursor start before (MissStream.selected p request key slice deterministic before).2 = start + events.length ∧
      (MissStream.selected p request key slice deterministic before).1 =
        (if deterministic then match failure with | none => .ok (some 1) | some fault => .error fault else .ok none) := by
  intro children observations before request key slice p events
  have bounds := Native.history_boundaries ops allocate safety 3 meaning base growth 64 children observations ConstructorItem.CacheTests.debug
    Publication.Tests.source ⟨0, 0⟩ (ConstructorItem.input Publication.Tests.request.item ConstructorItem.CacheTests.debug) request key slice deterministic before start
  refine ⟨?_, bounds.1, bounds.2.2, ?_⟩
  · change Native.middle _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _
    rw [Native.middle_history]
    cases deterministic with
    | false => rfl
    | true =>
      change ChildTrace.history (p.simplify key slice (ChildTrace.restore [] (ChildTrace.erase before))).2 = _
      dsimp only [p, Native.physical, MissStream.physical]
      rw [dispatcher_snapshot]
      cases failure <;> rfl'
  · cases deterministic with
    | false => rfl
    | true =>
      change (p.simplify key slice before).1 = _
      dsimp only [p, Native.physical, MissStream.physical]
      rw [dispatcher_snapshot]
      cases failure <;> rfl'

open Insertion.Native CallerSpareSuccessTests
open CallerInputTests (request key)
open AssemblyItem.Creation.NativeFields.Tests (input)

/-- The admitted spare input exercises the history-derived miss with an
inhabited resource-conditional child relation. It uses no supplied boundaries or transcripts;
the complete native suffix remains parameterized by its actual host operations.
This fixture's dispatcher makes no child call. -/
theorem spare_traced (safety empty deterministic : Bool)
    (ops : Insertion.Operations (ChildTrace.Recorded Nat ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded Nat ProtocolEvent))
    (base : ConstructorItem.PairInput.Context (Publication.Effects (ChildTrace.Recorded Nat ProtocolEvent)))
    (allocator : base.allocator = 7) (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded Nat ProtocolEvent)))
    (usizeBits : Nat) (debug : AssemblyItem.Fields.Values) (buffer : View)
    (result : Except Interner.Error NodeId) (seed : Interner.Primitives)
    (lookupToken : NormalizationOwnership.State) (unowned : lookupToken.owned = false) (caller : lookupToken.owner = .caller)
    (earlier leading trailing : List ProtocolEvent) :
    let children := ScopeTests.resultChildren (fun before : World (Publication.Effects Nat) => (result.mapError Fault.language, before))
    let observations : ChildTrace.Observations Nat ProtocolEvent := ScopeTests.resultChildren (fun _ => [])
    let model := ScopeTests.resultChildren (fun before => (result, before))
    Native.MissProjected ops allocate safety 6 Insertion.Tests.model base growth usizeBits (ChildTrace.constructors children observations)
      (ChildTrace.liftObservations observations) debug (argumentView empty) buffer itemSource input (request empty) (key empty)
      (CallerSpareSuccessTests.normalized empty) deterministic (ChildTrace.restore earlier (taken safety empty).2.world)
      (lookup empty) lookupToken model seed leading trailing (.base .missingArguments) := by
  intro children observations model
  have entry := derived_input safety empty
  have frame : InputFrame safety base.allocator 6 [old safety empty] (argumentView empty) (request empty).arguments
      (CallerSpareSuccessTests.normalized empty) (ChildTrace.restore earlier (taken safety empty).2.world) := by
    rw [allocator]
    obtain ⟨⟨added, data, capacity, facts, custody, privateSource⟩, held⟩ := (NativeSpareTests.reached_frame safety empty).1
    exact ⟨⟨added, data, capacity, { facts with valid := facts.valid.mapEffects _ },
      ⟨⟨custody.live, custody.apart⟩, custody.operands⟩, privateSource⟩,
      ⟨⟨held.1.1.mapEffects _, held.1.2⟩, held.2⟩⟩
  have identity : ChildTrace.constructors children observations =
      ScopeTests.resultChildren (fun before : ChildTrace.TracedWorld Nat ProtocolEvent => (result.mapError Fault.language, before)) := by
    have identityAction : ChildTrace.record (fun before : World (Publication.Effects Nat) => (result.mapError Fault.language, before))
        (fun _ => ([] : List ProtocolEvent)) = fun before => (result.mapError Fault.language, before) := by
      funext before
      simp only [ChildTrace.record, List.append_nil, ChildTrace.restore_history]
    simp only [children, observations, ChildTrace.constructors, ScopeTests.resultChildren, identityAction]
  refine Native.miss_resource_traced ops allocate safety 6 Insertion.Tests.model base growth usizeBits children observations debug
    (argumentView empty) itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic
    (ChildTrace.restore earlier (taken safety empty).2.world) buffer (lookup empty) lookupToken leading trailing model seed (fun _ => True)
    (request empty).arguments [old safety empty] trivial frame entry.publication.aligned (.base .missingArguments)
    entry.origin.detached unowned caller ?_
  intro _ rows
  rw [identity]
  have related (stream : List ProtocolEvent) : Resource.Projects ChildTrace.history stream
      (cursorGraph (MissStream.childCursor leading.length (ChildTrace.restore earlier (taken safety empty).2.world)))
      (fun world => True ∧ InputFrame safety base.allocator 6 rows (argumentView empty)
        (request empty).arguments (CallerSpareSuccessTests.normalized empty) world)
      (fun before => (result.mapError Fault.language, before)) (fun before => (result, before)) :=
    ⟨fun _ => List.prefix_refl _, fun _ held _ _ => ⟨held, rfl, rfl⟩⟩
  exact ⟨fun _ _ _ => related _, fun _ _ => related _, fun _ _ _ => related _,
    fun _ _ _ _ _ _ => related _, fun _ _ _ _ _ _ _ _ _ _ => related _⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.HistoryTests
