/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerMissInvocation
import Compiler.Extraction.InternerNativeScopedDispatchTests
import Compiler.Extraction.InternerInsertionInvocationTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Interner.InvocationTrace
open ConstructorItem.NativeRecursion
open Insertion.Native
open CallerSpareSuccessTests
open CallerInputTests (request key values)
open AssemblyItem.Creation.NativeFields.Tests (input)

/-- The existing spare-call request reaches no rewrite, independently of the
proper-child callbacks. Both guard outcomes observe the same native world. -/
theorem spare_selected (safety empty deterministic : Bool) (base : ConstructorItem.PairInput.Context (Publication.Effects Nat))
    (growth : Option (Growth.Registered.Callbacks Nat)) (children : Constructors (Publication.Effects Nat))
    (usizeBits : Nat) (debug : AssemblyItem.Fields.Values) :
    selected (physical ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth 6 usizeBits children debug
      (argumentView empty) itemSource input) (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) deterministic
      (taken safety empty).2.world = (.ok none, (taken safety empty).2.world) := by
  cases deterministic with
  | false => rfl
  | true =>
    simp only [selected, show (request empty).item.kind = 1 from rfl, beq_self_eq_true, Bool.and_self, ↓reduceIte]
    rw [physical, dispatcher_snapshot]
    have facts := (NativeSpareTests.reached_frame safety empty).1
    obtain ⟨added, data, capacity, reached, custody, sourcePrivate⟩ := facts.1
    rw [reached.reads]
    simp only [Interner.representativeReads, (derived_input safety empty).origin.graph,
      (NativeSpareTests.initial_facts safety empty).projected]
    cases safety <;> cases empty <;> rfl'

attribute [local irreducible] Insertion.Native.recordExecution

/-- The actual dispatcher selection now feeds the existing spare insertion
and deferred close. Reuse its source preparation, native header and token. -/
theorem spare_inserted (safety empty : Bool) (base : ConstructorItem.PairInput.Context (Publication.Effects Nat))
    (allocator : base.allocator = 7) (growth : Option (Growth.Registered.Callbacks Nat))
    (children : Constructors (Publication.Effects Nat)) (usizeBits : Nat) (debug : AssemblyItem.Fields.Values)
    (lookupToken : NormalizationOwnership.State) (unowned : lookupToken.owned = false) (caller : lookupToken.owner = .caller)
    (leading trailing : List (Event Failure Insertion.Native.Fault)) :
    let p := physical ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth 6 usizeBits children debug
      (argumentView empty) itemSource input
    let captured := TraceTests.captured safety empty growth
    let candidate := Insertion.cell input (key empty) (CallerSpareSuccessTests.normalized empty)
      (((key empty).eval Insertion.Tests.model (taken safety empty).2.world.graph.read).getD 0) captured.1.2 captured.2.effects
    let closeLeading := leading ++ captured.2.events.map Event.insertion
    let action := Interner.InsertionExecution.action candidate (key empty) true (operations (closeLeading ++ trailing) (.base .missingArguments))
    let logical := (do Interner.Scoped.handoff; Interner.Scoped.liftGraph action)
      ⟨⟨some lookupToken, (lookup empty).values, .cleanup⟩, { (taken safety empty).2.world.graph with allocationCursor := leading.length }⟩
    let actual := Interner.findCode.controlMiss (execution (Publication.external ops.arguments) 7 p)
      (request empty) (key empty) true (taken safety empty).2
    Caller.Close.HandoffCompletion (Publication.external ops.arguments) 7 lookupToken (lookup empty) (CallerSpareSuccessTests.normalized empty)
      closeLeading trailing (actual.1, actual.2.world) logical
      (finish (Publication.external ops.arguments) 7 actual.1 actual.2) := by
  have selection := spare_selected safety empty true base growth children usizeBits debug
  have entry := derived_input safety empty
  have checked := inserted ops CallerSpareSuccessTests.allocate safety 6 Insertion.Tests.model base growth 6 usizeBits children debug
    (argumentView empty) itemSource input (request empty) (key empty) (CallerSpareSuccessTests.normalized empty) true (taken safety empty).2.world
    (lookup empty) lookupToken leading trailing [old safety empty] ⟨lifetime empty, 0⟩ (.base .missingArguments)
    (congrArg Prod.fst selection) (by rw [selection]; exact TraceTests.spare_header safety empty)
    (by rw [selection, entry.origin.graph]; exact (NativeSpareTests.initial_facts safety empty).projected)
    entry.origin.detached unowned caller
  have shape : (⟨(taken safety empty).2.world, ⟨some (lookup empty), some (CallerSpareSuccessTests.normalized empty), false⟩⟩ : State (Publication.Effects Nat)) =
      (taken safety empty).2 := by rw [← entry.origin.scope]
  simpa only [Inserted, selection, allocator, shape, TraceTests.captured] using checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream.Tests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream.CountedTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Interner.InvocationTrace Normalization.Tests
open OwnedCall.Tests (request Search)
open Caller.Close.Tests (taken lookup key)
open Caller.Take.Tests (borrowed)
open Caller.ScopeProjection.Tests (model outerSlice initial)

/-- Reuse the effectful control family. Guard skipping emits no dispatcher
effect; every attempted dispatcher outcome, including errors, retains its effect.
These are control fixtures, not native constructor preservation certificates. -/
theorem selected_effects (search : Search) (publishFails insertFails deterministic : Bool) :
    let p := Caller.ScopeProjection.Tests.physical (model search publishFails insertFails)
    let decision := selected p request key outerSlice deterministic taken.2.world
    decision.2.memory.effects = taken.2.world.memory.effects + (if deterministic then 1 else 0) ∧
      Interner.findCode.controlMiss (execution success 7 p) request key deterministic taken.2 =
        match decision.1 with
        | .error fault => (.error fault, { taken.2 with world := decision.2 })
        | .ok none => (do handoff; graph (fun owned => p.insert key owned deterministic))
            { taken.2 with world := decision.2 }
        | .ok (some id) => (do let _ ← graph (fun owned => p.publish key owned id); handoff; pure id)
            { taken.2 with world := decision.2 } := by
  refine ⟨?_, routed success 7 _ request key outerSlice deterministic taken.2 (by rfl')⟩
  cases search <;> cases deterministic <;> rfl'

attribute [local irreducible] Caller.Close.capture

/-- Ordinary dispatcher OOM closes at its reached effect; semantic rejection
retains the same unhanded-off locals. Both consume the general error suffix. -/
theorem failed_closed (semantic : Bool) (leading trailing : List (Event Failure Unit)) :
    let search : Search := if semantic then .semantic else .fail
    let actual := Caller.ScopeProjection.Tests.native search false false true
    let close := Caller.Close.capture success 7 lookup .cleanup borrowed actual.2
    let events := leading ++ close.2.events.map Event.normalization ++ trailing
    let logical : Interner.Scoped.Session := ⟨⟨some lookup, borrowed.values, .cleanup⟩,
      { actual.2.world.graph with allocationCursor := leading.length }⟩
    actual.2.world.memory.effects = 18 ∧ actual.2.scope.handedOff = false ∧
      (semantic = true → finish success 7 actual.1 actual.2 = actual) ∧
      (semantic = false → ∃ after, finish success 7 actual.1 actual.2 = (actual.1, after) ∧
        CleanupPost success 7 source items outerSlice actual.2 after ∧
        after.world.memory = close.2.effects.session ∧
        Caller.Close.checked close (normalizations leading) (normalizations trailing) lookup .cleanup borrowed.values logical.heap =
          .ok (Interner.Scoped.close (resources events (.preparation .incomplete)) logical)) := by
  intro search actual close events logical
  let p := Caller.ScopeProjection.Tests.physical (model search false false)
  let fault : Fault := .language (if semantic then .unsupported else .outOfMemory)
  have chosen : (selected p request key outerSlice true taken.2.world).1 = .error fault := by
    cases semantic <;> rfl'
  have held : ordinary (.error fault : Except Fault NodeId) = true →
      Held 7 source items outerSlice (selected p request key outerSlice true taken.2.world).2 := by
    intro ordinaryResult
    have completed : ordinary (Recursive.PreservationTests.counted ((model search false false).simplify key) taken.2.world).1 = true := by
      cases semantic <;> first | exact ordinaryResult | rfl'
    exact (Recursive.PreservationTests.counted_projects 7 source items outerSlice ((model search false false).simplify key)
      taken.2.world initial completed).1
  have checked := failed success 7 p request key outerSlice true taken.2.world borrowed lookup source items fault
    leading trailing chosen held (by rfl') (by rfl') (by rfl')
  have shape : (⟨taken.2.world, ⟨some borrowed, some outerSlice, false⟩⟩ : State Nat) = taken.2 := by rfl'
  dsimp only [Failed] at checked
  rw [shape] at checked
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases semantic <;> rfl'
  · cases semantic <;> rfl'
  · intro stopped
    exact checked.2.1 (by subst semantic; rfl')
  · intro completed
    have closed := checked.2.2 (by subst semantic; rfl')
    simpa only [actual, Caller.ScopeProjection.Tests.native, p, logical, close, events, checked.1] using closed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream.CountedTests
