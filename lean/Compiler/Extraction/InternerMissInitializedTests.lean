/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerMissInitialized
import Compiler.Extraction.InternerMissReplayTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream.InitializedTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace
open Insertion.Native CallerSpareSuccessTests
open CallerInputTests (request key values)
open AssemblyItem.Creation.NativeFields.Tests (input)

attribute [local irreducible] Caller.Initialization.capture Caller.Take.capture segment

/-- The existing spare execution consumes the complete initialized miss proof.
Its dispatcher makes no child call, so both cursor boundaries are derived from
the recorded prefix. The inhabited child model, both guards/layouts and empty
arguments reuse existing fixtures; no graph or cleanup correspondence is assumed. -/
theorem spare_initialized (safety empty deterministic : Bool)
    (base : ConstructorItem.PairInput.Context (Publication.Effects Nat)) (allocator : base.allocator = 7) (budget : base.budget = 160)
    (growth : Option (Growth.Registered.Callbacks Nat)) (usizeBits : Nat) (debug : AssemblyItem.Fields.Values)
    (result : Except Interner.Error NodeId) (seed : Interner.Primitives)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let external := Publication.external ops.arguments
    let start := { before safety empty with memory := { (before safety empty).memory with memory := Publication.GraphTests.stack safety empty } }
    let initialization := Caller.Initialization.capture external base.budget base.allocator false (argumentView empty)
      ⟨(before safety empty).memory.memory.nextId, 0, 2⟩ (request empty).arguments start.memory
    let children := ScopeTests.resultChildren (fun before => (result.mapError Fault.language, before))
    let model := ScopeTests.resultChildren (fun before => (result, before))
    ∃ token, initialization.1 = .ok (some token) ∧
      let handle := initialization.2.effects.handle
      let transfer := Caller.Take.capture external base.allocator token.origin handle (prepared safety empty).2.world.memory
      let missLeading := leading ++ initialization.2.events.map Event.normalization ++ transfer.2.events.map Event.normalization
      let observed := segment ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth usizeBits children debug
        (argumentView empty) itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic
        (taken safety empty).2.world (lookup empty) transfer.1.2
      let events := missLeading ++ observed.body ++ observed.cleanup ++ trailing
      let r := resources events (.preparation .incomplete)
      let initialScope := Interner.Scoped.initScope r (request empty) ⟨{}, { (before safety empty).graph with allocationCursor := leading.length }⟩
      let takeScope := Interner.Scoped.take r initialScope.2
      let p := physical ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth 6 usizeBits children debug
        (argumentView empty) itemSource input
      let actual := Interner.findCode.controlMiss (execution external base.allocator p) (request empty) (key empty) deterministic (taken safety empty).2
      let logical := Interner.findCode.controlMiss
        (Interner.Scoped.execution r (dispatchModel (replay seed events observed.candidate (.base .missingArguments)) model usizeBits debug))
        (request empty) (key empty) deterministic takeScope.2
      let close := Caller.Close.capture external base.allocator transfer.1.2 observed.phase (lookup empty) actual.2
      Caller.Initialization.checked initialization (normalizations leading)
        (transfer.2.events ++ normalizations (observed.body ++ observed.cleanup ++ trailing)) (request empty)
        { (before safety empty).graph with allocationCursor := leading.length } = .ok initialScope ∧
      Caller.Take.checked transfer (normalizations leading ++ initialization.2.events)
        (normalizations (observed.body ++ observed.cleanup ++ trailing)) token (values empty) initialScope.2.heap = .ok takeScope ∧
      takeScope.1 = .ok () ∧ actual.1 = logical.1.mapError Fault.language ∧
      logical.2 = ⟨⟨some transfer.1.2, (lookup empty).values, observed.phase⟩,
        { actual.2.world.graph with allocationCursor := (missLeading ++ observed.body).length }⟩ ∧
      (ordinary actual.1 = true →
        Caller.Close.checked close (normalizations (missLeading ++ observed.body)) (normalizations trailing)
          transfer.1.2 observed.phase (lookup empty).values logical.2.heap = .ok (Interner.Scoped.close r logical.2)) := by
  intro external start initialization children model
  have calls := Publication.GraphTests.prefix_results safety empty
  have good := (CallerFirstSuccessTests.native_borrow_good safety empty).2
  have entry := derived_input safety empty
  have inputFrame : InputFrame safety base.allocator 6 [old safety empty] (argumentView empty) (request empty).arguments
      (CallerSpareSuccessTests.normalized empty) (taken safety empty).2.world := by
    simpa only [allocator] using (NativeSpareTests.reached_frame safety empty).1
  have initialized : Caller.initLookup external base.budget base.allocator (argumentView empty)
      ⟨(before safety empty).memory.memory.nextId, 0, 2⟩ (request empty) ⟨start, { lookup := none }⟩ =
      (.ok (values empty), (prepared safety empty).2) := by
    rw [allocator, budget]
    exact Prod.ext calls.2.1 rfl
  have transferred : OwnedCall.take external base.allocator (prepared safety empty).2 = (.ok (), (taken safety empty).2) := by
    rw [allocator]
    exact Prod.ext calls.2.2.1 rfl
  obtain ⟨token, recorded, composed⟩ := initialized_from_children ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model
    base growth usizeBits children debug (argumentView empty) itemSource input (request empty) (key empty) deterministic false
    (before safety empty) (Publication.GraphTests.stack safety empty) _ (values empty) (prepared safety empty).2 (taken safety empty).2
    leading other read sequence good.1 good.2 calls.1 (by cases empty <;> rfl)
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _)) initialized transferred
  refine ⟨token, recorded, ?_⟩
  intro handle transfer missLeading observed events r initialScope takeScope p actual logical close
  obtain ⟨slice, remaining, locals, _, _, _, composed⟩ := composed
  have sameLocals := locals.symm.trans entry.origin.scope
  have sameSlice := Option.some.inj (congrArg Local.slice sameLocals)
  have sameHandle := Option.some.inj (congrArg Local.lookup sameLocals)
  subst slice
  subst remaining
  have joined := composed (fun _ => missLeading.length) model seed (fun _ => True) [old safety empty] trivial inputFrame
    entry.publication.aligned (fun _ => (ScopeTests.outcome_children (fun _ => missLeading.length) _ result).source.at debug) [] trailing (.base .missingArguments)
  have selected := Tests.spare_selected safety empty deterministic base growth children usizeBits debug
  obtain ⟨initialCheck, takeCheck, succeeded, _, projected⟩ := joined
  have checked := projected (by simp only [selected, ordinary]) rfl (by simp only [List.append_nil]; rfl)
  simpa only [List.append_nil, List.nil_append] using And.intro initialCheck (And.intro takeCheck (And.intro succeeded checked))

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream.InitializedTests
