/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionInvocation
import Compiler.Extraction.InternerInvocationTraceTests
import Compiler.Extraction.InternerInsertionNativeTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.TraceTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open AssemblyItem.Creation.NativeFields.Tests (input)
open CallerInputTests (key request values)
open CallerSpareSuccessTests
open Interner.InvocationTrace

attribute [local irreducible] Caller.Initialization.capture Caller.Take.capture recordExecution

/-- Existing spare insertion in both layouts and argument shapes. Its actual
initializer and take select insertion's scope and detached lookup; completion
and checked close use the same stream without any supplied cursor equation. -/
theorem spare_initialized_insert (safety empty : Bool) (growth : Option (Growth.Registered.Callbacks Nat))
    (leading trailing : List (Event Failure Fault)) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let external := Publication.external Publication.GraphTests.host
    let start := { before safety empty with memory := { (before safety empty).memory with memory := Publication.GraphTests.stack safety empty } }
    let initialization := Caller.Initialization.capture external 160 7 false (argumentView empty)
      ⟨(before safety empty).memory.memory.nextId, 0, 2⟩ (request empty).arguments start.memory
    ∃ lookup, initialization.1 = .ok (some lookup) ∧
      let handle := initialization.2.effects.handle
      let transfer := Caller.Take.capture external 7 lookup.origin handle (prepared safety empty).2.world.memory
      let insertionLeading := leading ++ initialization.2.events.map Event.normalization ++ transfer.2.events.map Event.normalization
      let events := insertionLeading ++ (captured safety empty growth).2.events.map Event.insertion ++ trailing
      let resources := Interner.InvocationTrace.resources events (.preparation .incomplete)
      let initialScope := Interner.Scoped.initScope resources (request empty)
        ⟨{}, { (before safety empty).graph with allocationCursor := leading.length }⟩
      let takeScope := Interner.Scoped.take resources initialScope.2
      let candidate := cell input (key empty) (CallerSpareSuccessTests.normalized empty)
        (((key empty).eval Insertion.Tests.model (taken safety empty).2.world.graph.read).getD 0)
        (captured safety empty growth).1.2 (captured safety empty growth).2.effects
      let action := Interner.InsertionExecution.action candidate (key empty) true (operations events (.base .missingArguments))
      let logical := Interner.Scoped.liftGraph action takeScope.2
      let handed := (do Interner.Scoped.handoff; Interner.Scoped.liftGraph action) takeScope.2
      takeScope.1 = .ok () ∧
      Represents (taken safety empty).2.world.memory.memory (view (CallerSpareSuccessTests.normalized empty)) (values empty) ∧
      (request empty).item.eval (Folding.wordMeaning other) read (values empty) sequence =
        (request empty).item.eval (Folding.wordMeaning other) read (request empty).arguments sequence ∧
      (NativeSpareTests.actual safety empty growth).1 = logical.1.mapError OwnedCall.Fault.language ∧
      logical.2 = ⟨takeScope.2.scope, { (NativeSpareTests.actual safety empty growth).2.graph with
        allocationCursor := insertionLeading.length + (captured safety empty growth).2.events.length }⟩ ∧
      (NativeSpareTests.actual safety empty growth).2.memory = memory (captured safety empty growth).2.effects ∧
      ∃ remaining,
        finishInsertion ops CallerSpareSuccessTests.allocate safety 7 6 (argumentView empty) itemSource Insertion.Tests.model
          input (key empty) true (taken safety empty).2 growth =
          (.ok 1, ⟨(NativeSpareTests.actual safety empty growth).2, ⟨none, some (CallerSpareSuccessTests.normalized empty), true⟩⟩) ∧
        let close := Caller.Close.capture (Publication.external ops.arguments) 7 transfer.1.2 .transfer remaining
          ⟨(NativeSpareTests.actual safety empty growth).2, ⟨some remaining, some (CallerSpareSuccessTests.normalized empty), true⟩⟩
        Caller.Close.checked close (normalizations (insertionLeading ++ (captured safety empty growth).2.events.map Event.insertion))
          (normalizations trailing) transfer.1.2 .transfer remaining.values handed.2.heap =
          .ok (Interner.Scoped.close resources handed.2) ∧
        Interner.Scoped.close resources handed.2 =
          ⟨⟨some { transfer.1.2 with dead := true }, remaining.values, .transfer⟩,
            { (NativeSpareTests.actual safety empty growth).2.graph with
              allocationCursor := insertionLeading.length + (captured safety empty growth).2.events.length }⟩ := by
  intro external start initialization
  have calls := Publication.GraphTests.prefix_results safety empty
  have good := (CallerFirstSuccessTests.native_borrow_good safety empty).2
  have entry := derived_input safety empty
  have rows : (taken safety empty).2.world.graph.representatives = some [old safety empty] := by
    rw [entry.origin.graph, (NativeSpareTests.initial_facts safety empty).projected]
  have checked := initialized_insert_stream ops CallerSpareSuccessTests.allocate safety 7 6 (argumentView empty) itemSource
    Insertion.Tests.model input (key empty) (CallerSpareSuccessTests.normalized empty) true [old safety empty]
    external 160 false (request empty) (values empty) (before safety empty) (Publication.GraphTests.stack safety empty) _
    (prepared safety empty).2 (taken safety empty).2 growth (.base .missingArguments) leading trailing ⟨lifetime empty, 0⟩
    good.1 good.2 calls.1 (by cases empty <;> rfl)
    (Publication.external_admitted _ (Normalization.Tests.external_admitted _))
    (Prod.ext calls.2.1 rfl) (Prod.ext calls.2.2.1 rfl) (congrArg Local.slice entry.origin.scope)
    (spare_header safety empty) rows other read sequence
  obtain ⟨lookup, recorded, checked⟩ := checked
  refine ⟨lookup, recorded, ?_⟩
  intro handle transfer insertionLeading events resources initialScope takeScope candidate action logical handed
  obtain ⟨_, _, succeeded, _, _, represents, word, result, graph, memory, remaining, _, _, _, _, _, _, completion⟩ := checked
  change Caller.Close.HandoffCompletion (Publication.external ops.arguments) 7 transfer.1.2 remaining
    (CallerSpareSuccessTests.normalized empty) (insertionLeading ++ (captured safety empty growth).2.events.map Event.insertion)
    trailing (NativeSpareTests.actual safety empty growth) handed
    (finishInsertion ops CallerSpareSuccessTests.allocate safety 7 6 (argumentView empty) itemSource Insertion.Tests.model
      input (key empty) true (taken safety empty).2 growth) at completion
  have success := (NativeSpareTests.completed safety empty growth).1
  have completed : ordinary (NativeSpareTests.actual safety empty growth).1 = true := by rw [success]; rfl
  refine ⟨succeeded, represents, word, result, graph, memory, remaining, ?_, ?_⟩
  · simpa only [completed, ↓reduceIte, success] using completion.native
  · simpa only [List.length_append, List.length_map] using completion.closed completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.TraceTests
