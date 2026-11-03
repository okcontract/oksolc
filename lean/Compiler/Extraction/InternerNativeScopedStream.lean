/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeScopedTake
import Compiler.Extraction.InternerCallerTakeStream

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray Recursive
open ResourceAdapter NormalizationOwnership.Trace

/-- The actual initialized/taken scope enters native miss and reached cleanup
on one resource stream. Graph-event contents and their observed cursor bounds
remain obligations of the local graph/child contracts; no complete invocation
recording or all-entry preservation is claimed here. -/
theorem closed_miss_initialized_stream (cursor : World (Publication.Effects σ) → Nat) (safety : Bool) (owner : Nat)
    (base : PairInput.Context (Publication.Effects σ)) (usizeBits budget : Nat) (commutative : Bool)
    (children : Constructors (Publication.Effects σ)) (model : Associative.Constructors AssemblyItem.Fields.Values)
    (seed : Interner.Primitives) (debug : AssemblyItem.Fields.Values) (source : View)
    (request : Interner.Request) (values : List NodeId)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (originalRows : List Storage.Cell)
    (before : World (Publication.Effects σ)) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (prepared called : State (Publication.Effects σ)) (remaining : Handle)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative) (admitted : Admitted base.external)
    (initialized : Caller.initLookup base.external budget base.allocator source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : OwnedCall.take base.external base.allocator prepared = (.ok (), called))
    (predicate : World (Publication.Effects σ) → Prop) (initial : predicate called.world) (deterministic : Bool)
    (locals : called.scope = ⟨some remaining, some normalized, false⟩)
    (input : InputFrame safety base.allocator owner originalRows source request.arguments normalized called.world)
    (aligned : key.arguments = values)
    (coupled : ∀ rows, (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
      InputFrame safety base.allocator owner rows source request.arguments normalized world)).SourceConstructorsAt (Nested.storageReads rows) debug children model)
    (publishes : ∀ id, ProjectsAt (cursorGraph cursor) predicate
      ((base.primitives source address native).publish key normalized id) (seed.publish key id))
    (inserts : ProjectsAt (cursorGraph cursor) predicate
      ((base.primitives source address native).insert key normalized deterministic) (seed.insert key deterministic))
    (publishLifetime : ∀ id world, predicate world → Held base.allocator source request.arguments normalized world →
      ordinary ((base.primitives source address native).publish key normalized id world).1 = true →
      Good source request.arguments ((base.primitives source address native).publish key normalized id world).2 ∧
        (∀ fault, ((base.primitives source address native).publish key normalized id world).1 = .error fault →
          SliceValid base.allocator ((base.primitives source address native).publish key normalized id world).2.memory.heap normalized))
    (insertLifetime : ∀ world, predicate world → Held base.allocator source request.arguments normalized world →
      ordinary ((base.primitives source address native).insert key normalized deterministic world).1 = true →
      Good source request.arguments ((base.primitives source address native).insert key normalized deterministic world).2)
    (leading middle suffix : List (Event Failure)) (other : Meaning) (read : Read) (sequence : BitVec 32) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let start := { before with memory := { before.memory with memory } }
    let initialization := Caller.Initialization.capture base.external budget base.allocator commutative source buffer request.arguments start.memory
    ∃ lookup, initialization.1 = .ok (some lookup) ∧
      let handle := initialization.2.effects.handle
      let taken := Caller.Take.capture base.external base.allocator lookup.origin handle prepared.world.memory
      let physical := (context base owner usizeBits children debug).primitives source address native
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
        CleanupPost base.external base.allocator source request.arguments normalized body.2 after ∧ predicate body.2.world ∧
        body.1 = logical.1.mapError Fault.language ∧
        logical.2 = Caller.ScopeProjection.scopeAt (cursorGraph cursor) taken.1.2 remaining.values body.2 ∧
        after.world.memory = cleanup.2.effects.session ∧
        Caller.Close.checked cleanup closeLeading suffix taken.1.2 logical.2.scope.phase logical.2.scope.items logical.2.heap =
          .ok (Interner.Scoped.close resources logical.2) := by
  intro buffer start initialization
  obtain ⟨lookup, captured, state, contents, tokenEq⟩ := Caller.Initialization.capture_success base.external budget base.allocator
    commutative source buffer request start values prepared decoded initialized
  refine ⟨lookup, captured, ?_⟩
  intro handle taken physical body phase cleanup takeLeading closeLeading resources initialScope takeScope logical completed entered ended
  obtain ⟨actualLookup, recorded, present, actualValues, word, initializedScope, initialKnown, accepted, takeKnown⟩ :=
    Caller.Take.initialized_stream base.external budget base.allocator commutative source request before memory pointer values prepared
      leading (middle ++ (cleanup.2.events ++ suffix)) other read sequence valid represented allocated decoded admitted initialized
  have sameLookup := Option.some.inj (Except.ok.inj (captured.symm.trans recorded))
  subst actualLookup
  change lookup = token lookup.origin handle at tokenEq
  change handle.values = values at contents
  have initChecked : Caller.Initialization.checked initialization leading
      (taken.2.events ++ (middle ++ (cleanup.2.events ++ suffix))) request
      { before.graph with allocationCursor := leading.length } = .ok initialScope := by
    simpa only [initialScope, resources, closeLeading, takeLeading, List.append_assoc] using initializedScope
  have initKnown : Caller.Initialization.Coupled base.allocator source request start
      (leading.length + initialization.2.events.length) initialization.2.effects.session (.ok values, prepared)
      initialScope other read sequence := by simpa only [initialScope, resources, closeLeading, takeLeading, List.append_assoc] using initialKnown
  have takeChecked : Caller.Take.checked taken takeLeading (middle ++ (cleanup.2.events ++ suffix)) lookup values
      initialScope.2.heap = .ok takeScope := by simpa only [takeScope, initialScope, resources, closeLeading, takeLeading, List.append_assoc] using accepted
  have takeCoupled : Caller.Take.Coupled base.allocator source request.arguments handle prepared.world
      (takeLeading.length + taken.2.events.length) taken.2.effects.session taken.1 (.ok (), called) takeScope := by
    simpa only [takeScope, initialScope, resources, closeLeading, takeLeading, List.append_assoc, transferred] using takeKnown
  obtain ⟨actualHandle, initialLookup, nativeLookup, _, _, ready, _, _, localShape, _⟩ := initKnown.2.2.2.2.2 values rfl
  have sameHandle := Option.some.inj (present.symm.trans nativeLookup)
  subst actualHandle
  have takeCall : OwnedCall.take base.external base.allocator ⟨prepared.world, { lookup := some handle }⟩ = (.ok (), called) := by
    have sameState : (⟨prepared.world, { lookup := some handle }⟩ : State (Publication.Effects σ)) = prepared := by rw [← localShape]
    rw [sameState]
    exact transferred
  have complete := closed_miss_after_take cursor safety owner base usizeBits children model seed debug source request.arguments
    address native key normalized originalRows prepared.world handle remaining called lookup.origin ready admitted takeCall
    predicate initial request deterministic locals input (aligned.trans contents.symm) coupled publishes inserts
    publishLifetime insertLifetime closeLeading suffix
  have graphStart : initialScope.2.heap.allocationCursor = takeLeading.length := by
    rw [initKnown.2.2.2.1]
    simp only [takeLeading, List.length_append]
  have recordedTake : Caller.Take.checked taken takeLeading (middle ++ (cleanup.2.events ++ suffix)) (token lookup.origin handle)
      handle.values initialScope.2.heap = .ok takeScope := by
    simpa only [← tokenEq, contents] using takeChecked
  have shape := (Caller.Take.checked_scope base.external base.allocator lookup.origin handle prepared.world.memory
    takeLeading (middle ++ (cleanup.2.events ++ suffix)) initialScope.2.heap takeScope graphStart recordedTake).2
  have succeeded : taken.1.1 = true := by
    have status := takeCoupled.1
    rw [shape] at status
    change (.ok () : Except Fault Unit) = (if taken.1.1 then .ok () else .error .outOfMemory : Except Interner.Error Unit).mapError Fault.language at status
    cases result : taken.1.1 <;> simp only [result, Bool.false_eq_true, ↓reduceIte, Except.mapError] at status ⊢
    contradiction
  have graph : called.world.graph = prepared.world.graph := takeCoupled.2.1
  have scopeSame : takeScope.2 = Caller.ScopeProjection.scopeAt (cursorGraph cursor) taken.1.2 remaining.values called := by
    rw [takeCoupled.2.2.2.1]
    change (⟨⟨some taken.1.2, handle.values, if taken.1.1 then .cleanup else .lookup⟩,
      { prepared.world.graph with allocationCursor := takeLeading.length + taken.2.events.length }⟩ : Interner.Scoped.Session) = _
    simp only [succeeded, ↓reduceIte, Caller.ScopeProjection.scopeAt, locals, Bool.false_eq_true, cursorGraph,
      complete.1.sameValues, graph, entered]
  obtain ⟨after, finished, clean, preserved, result, reached, memory, closed⟩ := complete.2 completed ended
  refine ⟨initChecked, takeChecked, scopeSame, word, after, finished, clean, preserved, ?_, ?_, memory, ?_⟩
  · simpa only [logical, scopeSame] using result
  · simpa only [logical, scopeSame] using reached
  · simpa only [logical, scopeSame] using closed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
