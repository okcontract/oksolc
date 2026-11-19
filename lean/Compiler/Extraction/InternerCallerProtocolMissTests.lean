/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolMissReplay
import Compiler.Extraction.InternerMissReplayTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.MissTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace
open Insertion.Native CallerSpareSuccessTests
open CallerInputTests (request key)
open AssemblyItem.Creation.NativeFields.Tests (input)

/-- The existing spare request calls no child. Its actual dispatcher history is
empty in both layouts and argument shapes, for either source guard. -/
theorem spare_middle (safety empty deterministic : Bool)
    (base : ConstructorItem.PairInput.Context (Publication.Effects Nat))
    (growth : Option (Growth.Registered.Callbacks Nat)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects Nat)) (observations : ChildTrace.Observations Nat ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) :
    Native.middle ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth usizeBits children observations debug
      (argumentView empty) itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic
      (taken safety empty).2.world = [] := by
  cases deterministic with
  | false => rfl
  | true =>
    simp only [Native.middle, Native.graphObservations, Native.dispatch,
      show (request empty).item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    obtain ⟨added, data, capacity, reached, custody, sourcePrivate⟩ := (NativeSpareTests.reached_frame safety empty).1.1
    rw [reached.reads]
    simp only [Interner.representativeReads, (derived_input safety empty).origin.graph,
      (NativeSpareTests.initial_facts safety empty).projected]
    cases safety <;> cases empty <;> rfl'

/-- Reuse the existing admitted spare input and inhabited proper-child relation.
No transcript, cursor boundary, reached frame or cleanup proof is supplied by
the fixture. This family makes no recursive call; it exercises the general
recorded-miss consumer, for arbitrary surrounding protocol history. -/
theorem spare_verified (safety empty deterministic : Bool)
    (base : ConstructorItem.PairInput.Context (Publication.Effects Nat)) (allocator : base.allocator = 7)
    (growth : Option (Growth.Registered.Callbacks Nat)) (usizeBits : Nat) (debug : AssemblyItem.Fields.Values)
    (result : Except Interner.Error NodeId) (seed : Interner.Primitives)
    (observations : ChildTrace.Observations Nat ProtocolEvent) (buffer : View)
    (lookupToken : NormalizationOwnership.State) (unowned : lookupToken.owned = false) (caller : lookupToken.owner = .caller)
    (leading trailing : List ProtocolEvent) :
    let children := ScopeTests.resultChildren (fun before => (result.mapError Fault.language, before))
    let model := ScopeTests.resultChildren (fun before => (result, before))
    let before := (taken safety empty).2.world
    let p := Native.physical ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth usizeBits children debug
      (argumentView empty) itemSource input
    let ports := Native.graphObservations ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth usizeBits children observations debug
      (argumentView empty) itemSource input
    let observed := MissStream.segment ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth usizeBits children debug
      (argumentView empty) itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic before (lookup empty) lookupToken
    let events := leading ++ observed.body ++ observed.cleanup ++ trailing
    let resources := Interner.InvocationTrace.resources events (.preparation .incomplete)
    let logicalModel := dispatchModel (MissStream.replay seed events observed.candidate (.base .missingArguments)) model usizeBits debug
    let initial : Recorded (Publication.Effects Nat) :=
      ⟨⟨before, ⟨some (lookup empty), some (CallerSpareSuccessTests.normalized empty), false⟩⟩,
        { lookup := some lookupToken, items := (lookup empty).values, phase := .cleanup }, leading⟩
    let body := missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports
      (argumentView empty) buffer (request empty) (key empty) deterministic initial
    let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources logicalModel)
      (request empty) (key empty) deterministic (scopeView initial)
    ordinary body.1 = true →
      let actual := finish (Publication.external ops.arguments) base.allocator body.1 body.2
      (body.1, scopeView body.2) = (logical.1.mapError Fault.language, logical.2) ∧
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, Interner.Scoped.close resources logical.2) ∧
      actual.2.events = leading ++ observed.body ++ observed.cleanup ∧ actual.2.tokens.incomplete = false := by
  intro children model before p ports observed events resources logicalModel initial body logical
  have entry := derived_input safety empty
  have frame : InputFrame safety base.allocator 6 [old safety empty] (argumentView empty) (request empty).arguments
      (CallerSpareSuccessTests.normalized empty) before := by
    simpa only [allocator] using (NativeSpareTests.reached_frame safety empty).1
  have composed := Native.miss_verified ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth usizeBits children observations debug
    (argumentView empty) buffer itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic
    before (lookup empty) lookupToken (fun _ => leading.length) model seed (fun _ => True) (request empty).arguments [old safety empty]
    trivial frame entry.publication.aligned (fun _ _ => (ScopeTests.outcome_children (fun _ => leading.length) _ result).source.at debug)
    leading trailing (.base .missingArguments) entry.origin.detached unowned caller rfl
  dsimp only [before, Native.MissProjected] at composed
  simp only [spare_middle, List.append_nil] at composed
  exact composed trivial

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.MissTests
