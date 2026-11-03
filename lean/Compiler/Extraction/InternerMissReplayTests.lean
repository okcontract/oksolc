/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerMissReplay
import Compiler.Extraction.InternerMissAdmissionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream.ReplayTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace
open Insertion.Native CallerSpareSuccessTests
open CallerInputTests (request key)
open AssemblyItem.Creation.NativeFields.Tests (input)

/-- Reuse the admitted spare invocation and the inhabited child relation. Both
source guards and argument shapes reach the whole logical miss and its checked
close through recorded ports. This fixture makes no recursive child call. -/
theorem spare_projected (safety empty deterministic : Bool)
    (base : ConstructorItem.PairInput.Context (Publication.Effects Nat)) (allocator : base.allocator = 7)
    (growth : Option (Growth.Registered.Callbacks Nat)) (usizeBits : Nat) (debug : AssemblyItem.Fields.Values)
    (result : Except Interner.Error NodeId) (seed : Interner.Primitives)
    (lookupToken : NormalizationOwnership.State) (unowned : lookupToken.owned = false) (caller : lookupToken.owner = .caller)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) :
    let children := ScopeTests.resultChildren (fun before => (result.mapError Fault.language, before))
    let model := ScopeTests.resultChildren (fun before => (result, before))
    Projected ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth usizeBits children debug
      (argumentView empty) itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic
      (taken safety empty).2.world (lookup empty) lookupToken (fun _ => leading.length) model seed leading trailing (.base .missingArguments) := by
  intro children model
  have entry := derived_input safety empty
  have frame : InputFrame safety base.allocator 6 [old safety empty] (argumentView empty) (request empty).arguments
      (CallerSpareSuccessTests.normalized empty) (taken safety empty).2.world := by
    simpa only [allocator] using (NativeSpareTests.reached_frame safety empty).1
  have composed := scoped_from_children ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth usizeBits children debug
    (argumentView empty) itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic
    (taken safety empty).2.world (lookup empty) lookupToken (fun _ => leading.length) model seed (fun _ => True)
    (request empty).arguments [old safety empty] trivial frame entry.publication.aligned
    (fun _ _ => (ScopeTests.outcome_children (fun _ => leading.length) _ result).source.at debug) leading trailing (.base .missingArguments)
    entry.origin.detached unowned caller
  have selection := Tests.spare_selected safety empty deterministic base growth children usizeBits debug
  exact composed.2 (by simp only [selection, ordinary]) rfl

/-- An absent candidate must remain a semantic rejection, never a successful
or recoverable replay of a branch that was not observed. -/
theorem absent_candidate (seed : Interner.Primitives) (events : List (Event Failure Insertion.Native.Fault))
    (mismatch : Insertion.Native.Fault) (key : Key) (deterministic : Bool) (before : Interner.Heap) :
    (replay seed events none mismatch).insert key deterministic before = (.error .safetyFault, before) := rfl

/-- Existing counted control callbacks exercise all dispatcher outcomes and
publication/insertion refusal. The cursor counts callback slots here; these
fixtures are not complete native allocation traces or child certificates. -/
theorem counted_routes (search : OwnedCall.Tests.Search) (publishFails insertFails deterministic : Bool)
    (r : Interner.Scoped.Resources) (heap : Interner.Heap) (token : NormalizationOwnership.State) (items : List NodeId) :
    let model := Caller.ScopeProjection.Tests.model search publishFails insertFails
    let actual := Interner.findCode.controlMiss (Interner.Scoped.execution r model)
      OwnedCall.Tests.request Caller.Close.Tests.key deterministic ⟨⟨some token, items, .cleanup⟩, heap⟩
    let calls := if deterministic then match search with
      | .fail | .semantic => 1 | .found | .unchanged => 2 else 1
    let phase : NormalizationOwnership.Exit := if deterministic then match search with
      | .fail | .semantic => .cleanup
      | .found => if publishFails then .cleanup else .transfer
      | .unchanged => .transfer else .transfer
    actual.2.scope = ⟨some token, items, phase⟩ ∧ actual.2.heap.allocationCursor = heap.allocationCursor + calls := by
  dsimp only
  rw [scoped_routed]
  cases search <;> cases publishFails <;> cases insertFails <;> cases deterministic <;> constructor <;> rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream.ReplayTests
