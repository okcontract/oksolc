/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeScopedStream
import Compiler.Extraction.InternerNativeScopedDispatchTests
import Compiler.Extraction.InternerInsertionInvocationTests
import Compiler.Extraction.InternerPublicationInvocationTests
import Compiler.Extraction.InternerMissInitializedTests
import Compiler.Extraction.InternerCallerRecursionTraceTests
import Compiler.Extraction.InternerCallerCacheStreamTests
import Compiler.Extraction.InternerInvocationChildTraceTests
import Compiler.Extraction.InternerConstructorProtocolTraceTests
import Compiler.Extraction.InternerCallerProtocolMissTests
import Compiler.Extraction.InternerCallerProtocolHistoryTests
import Compiler.Extraction.InternerCallerProtocolTakenTests
import Compiler.Extraction.InternerRecursiveProtocolEffectsTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ScopeTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Recursive
open Insertion.Native NormalizationOwnership.Trace

/-- The same spare-call execution supplies the complete native initialization
and take observations. Its actual scoped take now enters miss and close on the
shared stream in both layouts, including empty arguments. Graph and child
contracts, and the bounds of their event segment, remain explicit. -/
theorem spare_initialized_closed (safety empty : Bool) (base : PairInput.Context (Publication.Effects Nat))
    (allocator : base.allocator = 7) (host : base.external = Publication.external Publication.GraphTests.host) (usizeBits : Nat) (debug : AssemblyItem.Fields.Values)
    (cursor : World (Publication.Effects Nat) → Nat) (children : Constructors (Publication.Effects Nat))
    (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (coupled : ∀ rows, (projectionAt (cursorGraph cursor) (fun world => True ∧
      InputFrame safety base.allocator 6 rows (CallerSpareSuccessTests.argumentView empty)
        (CallerInputTests.request empty).arguments (CallerSpareSuccessTests.normalized empty) world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (publishes : ∀ id, ProjectsAt (cursorGraph cursor) (fun _ => True)
      ((base.primitives (CallerSpareSuccessTests.argumentView empty) CallerSpareSuccessTests.itemSource
        AssemblyItem.Creation.NativeFields.Tests.input).publish (CallerInputTests.key empty) (CallerSpareSuccessTests.normalized empty) id)
      (seed.publish (CallerInputTests.key empty) id))
    (inserts : ProjectsAt (cursorGraph cursor) (fun _ => True)
      ((base.primitives (CallerSpareSuccessTests.argumentView empty) CallerSpareSuccessTests.itemSource
        AssemblyItem.Creation.NativeFields.Tests.input).insert (CallerInputTests.key empty) (CallerSpareSuccessTests.normalized empty) true)
      (seed.insert (CallerInputTests.key empty) true))
    (memory : GraphContracts base.allocator (CallerSpareSuccessTests.argumentView empty)
      (CallerInputTests.request empty).arguments (base.primitives (CallerSpareSuccessTests.argumentView empty)
        CallerSpareSuccessTests.itemSource AssemblyItem.Creation.NativeFields.Tests.input))
    (leading middle suffix : List (Event Failure)) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let source := CallerSpareSuccessTests.argumentView empty
    let request := CallerInputTests.request empty
    let values := CallerInputTests.values empty
    let before := CallerSpareSuccessTests.before safety empty
    let memory := Publication.GraphTests.stack safety empty
    let prepared := (CallerSpareSuccessTests.prepared safety empty).2
    let called := (CallerSpareSuccessTests.taken safety empty).2
    let remaining := CallerSpareSuccessTests.lookup empty
    let normalized := CallerSpareSuccessTests.normalized empty
    let address := CallerSpareSuccessTests.itemSource
    let native := AssemblyItem.Creation.NativeFields.Tests.input
    let key := CallerInputTests.key empty
    let deterministic := true
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let start := { before with memory := { before.memory with memory } }
    let initialization := Caller.Initialization.capture base.external 160 base.allocator false source buffer request.arguments start.memory
    ∃ lookup, initialization.1 = .ok (some lookup) ∧
      let handle := initialization.2.effects.handle
      let taken := Caller.Take.capture base.external base.allocator lookup.origin handle prepared.world.memory
      let physical := (context base 6 usizeBits children debug).primitives source address native
      let body := Interner.findCode.controlMiss (OwnedCall.execution base.external base.allocator physical) request key deterministic called
      let phase : NormalizationOwnership.Exit := if body.2.scope.handedOff then .transfer else .cleanup
      let cleanup := Caller.Close.capture base.external base.allocator taken.1.2 phase remaining body.2
      let takeLeading := leading ++ initialization.2.events
      let closeLeading := takeLeading ++ (taken.2.events ++ middle)
      let resources := Scope.resources (closeLeading ++ (cleanup.2.events ++ suffix)) (.preparation .incomplete)
      let initialScope := Interner.Scoped.initScope resources request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
      let takeScope := Interner.Scoped.take resources initialScope.2
      let logical := Interner.findCode.controlMiss (Interner.Scoped.execution resources (dispatchModel seed model usizeBits debug))
        request key deterministic takeScope.2
      ordinary body.1 = true → cursor called.world = takeLeading.length + taken.2.events.length →
      cursor body.2.world = closeLeading.length →
      Caller.Initialization.checked initialization leading (taken.2.events ++ (middle ++ (cleanup.2.events ++ suffix))) request
        { before.graph with allocationCursor := leading.length } = .ok initialScope ∧
      Caller.Take.checked taken takeLeading (middle ++ (cleanup.2.events ++ suffix)) lookup values initialScope.2.heap = .ok takeScope ∧
      takeScope.2 = Caller.ScopeProjection.scopeAt (cursorGraph cursor) taken.1.2 remaining.values called ∧
      request.item.eval (Folding.wordMeaning other) read values sequence =
        request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
      ∃ after, OwnedCall.finish base.external base.allocator body.1 body.2 = (body.1, after) ∧
        CleanupPost base.external base.allocator source request.arguments normalized body.2 after ∧ True ∧
        body.1 = logical.1.mapError Fault.language ∧
        logical.2 = Caller.ScopeProjection.scopeAt (cursorGraph cursor) taken.1.2 remaining.values body.2 ∧
        after.world.memory = cleanup.2.effects.session ∧
        Caller.Close.checked cleanup closeLeading suffix taken.1.2 logical.2.scope.phase logical.2.scope.items logical.2.heap =
          .ok (Interner.Scoped.close resources logical.2) := by
  intro source request values before stack prepared called remaining normalized address native key deterministic
  have calls := Publication.GraphTests.prefix_results safety empty
  have good := (CallerFirstSuccessTests.native_borrow_good safety empty).2
  have entry := CallerSpareSuccessTests.derived_input safety empty
  have input : InputFrame safety base.allocator 6 [CallerSpareSuccessTests.old safety empty]
      source request.arguments normalized called.world := by
    simpa only [allocator] using (NativeSpareTests.reached_frame safety empty).1
  have admitted : Admitted base.external := by
    rw [host]
    exact Publication.external_admitted _ (Normalization.Tests.external_admitted _)
  have initialized : Caller.initLookup base.external 160 base.allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, prepared) := by
    rw [allocator, host]
    apply Prod.ext
    · exact calls.2.1
    · rfl
  have transferred : OwnedCall.take base.external base.allocator prepared = (.ok (), called) := by
    rw [allocator, host]
    apply Prod.ext
    · exact calls.2.2.1
    · rfl
  exact closed_miss_initialized_stream cursor safety 6 base usizeBits 160 false children model seed debug source request values
    address native key normalized [CallerSpareSuccessTests.old safety empty] before stack _ prepared called remaining
    good.1 good.2 calls.1 (by cases empty <;> rfl) admitted initialized transferred (fun _ => True) trivial true
    entry.origin.scope input entry.publication.aligned coupled publishes inserts
    (fun id world _ held => memory.publish _ _ id world entry.publication.aligned held)
    (fun world _ held => memory.insert _ _ true world entry.publication.aligned held) leading middle suffix other read sequence

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ScopeTests
