/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolComplete
import Compiler.Extraction.InternerCallerProtocolHistory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

attribute [local irreducible] Initialization.capture Take.capture

/-- Shared initialized continuation from the recorded miss endpoint. Actual
initialization/take derives the normalized input, scope token and history; both
child relations reuse this prefix and the same body/close routing proof. -/
theorem initialized_miss_projected
    (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (deterministic commutative : Bool)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (stack : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId)
    (prepared called : OwnedCall.State (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (leading : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, stack))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (admitted : Admitted (Publication.external ops.arguments))
    (initialized : Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source
      ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : OwnedCall.take (Publication.external ops.arguments) base.allocator prepared = (.ok (), called))
    (room : base.queries.atCapacity before.graph = false)
    (classified : base.queries.deterministic request.item = .ok deterministic)
    (made : Interner.makeKey request values = .ok key)
    (absent : deterministic = true → before.graph.table key = none) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let start := { before with memory := { before.memory with memory := stack } }
    let init := Initialization.capture (Publication.external ops.arguments) base.budget base.allocator
      commutative source buffer request.arguments start.memory
    ∃ lookup, init.1 = .ok (some lookup) ∧
      let handle := init.2.effects.handle
      let taken := Take.capture (Publication.external ops.arguments) base.allocator lookup.origin handle prepared.world.memory
      let missLeading := leading ++ init.2.events.map Event.normalization ++ taken.2.events.map Event.normalization
      ∃ slice remaining, called.scope = ⟨some remaining, some slice, false⟩ ∧
        Normalization.Taken base.allocator source request.arguments handle prepared.world.memory slice remaining called.world.memory ∧
        slice.items = values ∧ taken.1.2.owned = false ∧ taken.1.2.owner = .caller ∧
        request.item.eval (Folding.wordMeaning other) read values sequence =
          request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
        record (OwnedCall.take (Publication.external ops.arguments) base.allocator)
          (taking (Publication.external ops.arguments) base.allocator)
          (record (Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source buffer request)
            (initialization (Publication.external ops.arguments) base.budget base.allocator source buffer request)
            ⟨⟨start, { lookup := none }⟩, {}, leading⟩).2 =
          (.ok (), ⟨called, { lookup := some taken.1.2, items := remaining.values, phase := .cleanup }, missLeading⟩) ∧
        ∀ (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
          (trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault),
            let child := ChildTrace.constructors children observations
            let observedChildren := ChildTrace.liftObservations observations
            let p := physical ops allocate safety owner meaning base growth usizeBits child debug source address input
            let ports := graphObservations ops allocate safety owner meaning base growth usizeBits child observedChildren debug source address input
            let middle := Native.middle ops allocate safety owner meaning base growth usizeBits child observedChildren debug source address input
              request key slice deterministic called.world
            let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits child debug source address input
              request key slice deterministic called.world remaining taken.1.2
            let events := missLeading ++ middle ++ observed.body ++ observed.cleanup ++ trailing
            let logicalModel := dispatchModel (MissStream.replay seed events observed.candidate mismatch) model usizeBits debug
            let entry : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) :=
              ⟨⟨start, { lookup := none }⟩, {}, leading⟩
            let body := findBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer request entry
            let actual := find (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer request entry
            MissProjected ops allocate safety owner meaning base growth usizeBits child observedChildren debug source buffer address input
              request key slice deterministic called.world remaining taken.1.2 model seed missLeading trailing mismatch →
            MissContinuation (Publication.external ops.arguments) base.budget base.allocator p base.queries ports
              logicalModel source buffer request entry trailing ∧
              (ordinary body.1 = true → actual.2.events = missLeading ++ middle ++ observed.body ++ observed.cleanup) := by
  intro buffer start init
  obtain ⟨lookup, captured, prefixProof⟩ := initialized_taken_recorded (Publication.external ops.arguments) base.budget base.allocator
    commutative source request before stack pointer values prepared called leading other read sequence
    valid represented allocated decoded admitted initialized transferred
  refine ⟨lookup, captured, ?_⟩
  intro handle taken missLeading
  obtain ⟨slice, remaining, locals, lifetime, contents, unowned, caller, word, normalizedResult, takenRecord, prefixProof⟩ := prefixProof
  refine ⟨slice, remaining, locals, lifetime, contents, unowned, caller, word, takenRecord, ?_⟩
  intro model seed trailing mismatch
  intro child observedChildren p ports middle observed events logicalModel entry body actual
  let r := resources events (.preparation .incomplete)
  let missEntry : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) :=
    ⟨called, { lookup := some taken.1.2, items := remaining.values, phase := .cleanup }, missLeading⟩
  have shape : (⟨called.world, ⟨some remaining, some slice, false⟩⟩ : OwnedCall.State _) = called := by rw [← locals]
  intro projected
  have routed := findBody_taken (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
    request key deterministic values entry _ missEntry room (Prod.ext normalizedResult rfl) classified made absent takenRecord
  change body = missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
    request key deterministic missEntry at routed
  dsimp only [MissProjected] at projected
  rw [shape] at projected
  have actualRoute : actual = finish (Publication.external ops.arguments) base.allocator
      (missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
        request key deterministic missEntry).1
      (missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer
        request key deterministic missEntry).2 := by
    change finish _ _ body.1 body.2 = _
    rw [routed]
  have continuation : MissContinuation (Publication.external ops.arguments) base.budget base.allocator p base.queries ports
      logicalModel source buffer request entry trailing := by
    intro actualValues actualKey actualDet normalized takenActual _ actualInitialized actualClassified actualMade _ _
    have sameValues : actualValues = values := Except.ok.inj (actualInitialized.symm.trans normalizedResult)
    subst actualValues
    have sameKey : actualKey = key := Except.ok.inj (actualMade.symm.trans made)
    subst actualKey
    have sameDet : actualDet = deterministic := Except.ok.inj (actualClassified.symm.trans classified)
    subst actualDet
    have sameTake : takenActual = (.ok (), missEntry) := takenRecord
    simp only [sameTake]
    intro ordinaryMiss
    have finished := projected ordinaryMiss
    let bodyMiss := missBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports
      source buffer request key deterministic missEntry
    let actualMiss := finish (Publication.external ops.arguments) base.allocator bodyMiss.1 bodyMiss.2
    let resourcesMiss := resources (actualMiss.2.events ++ trailing) (.preparation .incomplete)
    have history : actualMiss.2.events = missLeading ++ middle ++ observed.body ++ observed.cleanup := finished.2.2.1
    have resourceEq : resourcesMiss = r := by simp only [resourcesMiss, history, r, events]
    change (actualMiss.1, scopeView actualMiss.2) =
      ((Interner.findCode.controlMiss (Interner.Scoped.execution resourcesMiss logicalModel) request key deterministic
        (scopeView missEntry)).1.mapError Fault.language,
        Interner.Scoped.close resourcesMiss (Interner.findCode.controlMiss (Interner.Scoped.execution resourcesMiss logicalModel)
          request key deterministic (scopeView missEntry)).2) ∧ actualMiss.2.tokens.incomplete = false
    rw [resourceEq]
    exact ⟨finished.2.1, finished.2.2.2⟩
  refine ⟨continuation, ?_⟩
  intro completed
  rw [actualRoute]
  exact (projected (by rw [← routed]; exact completed)).2.2.1


/-- Derive the general entry's local continuation from the proper-child
relation. Only the actual initialization/take prefix is supplied; the reached
protocol state, body/close history and cleanup are derived. The continuation
uses one replay model and is available before assuming an ordinary caller
result. Native input-frame and proper-child correspondence remain obligations. -/
theorem initialized_miss_continuation
    (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (deterministic commutative : Bool)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (stack : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId)
    (prepared called : OwnedCall.State (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (leading : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, stack))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (admitted : Admitted (Publication.external ops.arguments))
    (initialized : Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source
      ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : OwnedCall.take (Publication.external ops.arguments) base.allocator prepared = (.ok (), called))
    (room : base.queries.atCapacity before.graph = false)
    (classified : base.queries.deterministic request.item = .ok deterministic)
    (made : Interner.makeKey request values = .ok key)
    (absent : deterministic = true → before.graph.table key = none) :
    let buffer : View := ⟨before.memory.memory.nextId, 0, 2⟩
    let start := { before with memory := { before.memory with memory := stack } }
    let init := Initialization.capture (Publication.external ops.arguments) base.budget base.allocator
      commutative source buffer request.arguments start.memory
    ∃ lookup, init.1 = .ok (some lookup) ∧
      let handle := init.2.effects.handle
      let taken := Take.capture (Publication.external ops.arguments) base.allocator lookup.origin handle prepared.world.memory
      let missLeading := leading ++ init.2.events.map Event.normalization ++ taken.2.events.map Event.normalization
      ∃ slice remaining, called.scope = ⟨some remaining, some slice, false⟩ ∧
        Normalization.Taken base.allocator source request.arguments handle prepared.world.memory slice remaining called.world.memory ∧
        slice.items = values ∧
        request.item.eval (Folding.wordMeaning other) read values sequence =
          request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
        record (OwnedCall.take (Publication.external ops.arguments) base.allocator)
          (taking (Publication.external ops.arguments) base.allocator)
          (record (Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source buffer request)
            (initialization (Publication.external ops.arguments) base.budget base.allocator source buffer request)
            ⟨⟨start, { lookup := none }⟩, {}, leading⟩).2 =
          (.ok (), ⟨called, { lookup := some taken.1.2, items := remaining.values, phase := .cleanup }, missLeading⟩) ∧
        ∀ (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
          (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (rows : List Storage.Cell),
          predicate called.world → InputFrame safety base.allocator owner rows source request.arguments slice called.world →
          ((deterministic && (request.item.kind == 1)) = true →
            ∀ rows, (projectionAt (cursorGraph (MissStream.childCursor missLeading.length called.world))
            (fun world => predicate world ∧ InputFrame safety base.allocator owner rows source request.arguments slice world)).SourceConstructorsAt (Nested.storageReads rows) debug
              (ChildTrace.constructors children observations) model) →
          ∀ (trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault),
            let child := ChildTrace.constructors children observations
            let observedChildren := ChildTrace.liftObservations observations
            let p := physical ops allocate safety owner meaning base growth usizeBits child debug source address input
            let ports := graphObservations ops allocate safety owner meaning base growth usizeBits child observedChildren debug source address input
            let middle := Native.middle ops allocate safety owner meaning base growth usizeBits child observedChildren debug source address input
              request key slice deterministic called.world
            let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits child debug source address input
              request key slice deterministic called.world remaining taken.1.2
            let events := missLeading ++ middle ++ observed.body ++ observed.cleanup ++ trailing
            let logicalModel := dispatchModel (MissStream.replay seed events observed.candidate mismatch) model usizeBits debug
            let entry : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) :=
              ⟨⟨start, { lookup := none }⟩, {}, leading⟩
            let body := findBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer request entry
            let actual := find (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer request entry
            MissContinuation (Publication.external ops.arguments) base.budget base.allocator p base.queries ports
              logicalModel source buffer request entry trailing ∧
              (ordinary body.1 = true → actual.2.events = missLeading ++ middle ++ observed.body ++ observed.cleanup) := by
  intro buffer start init
  obtain ⟨lookup, captured, ready⟩ := initialized_miss_projected ops allocate safety owner meaning base growth usizeBits
    children observations debug source address input request key deterministic commutative before stack pointer values
    prepared called leading other read sequence valid represented allocated decoded admitted initialized transferred room classified made absent
  refine ⟨lookup, captured, ?_⟩
  intro handle taken missLeading
  obtain ⟨slice, remaining, locals, lifetime, contents, unowned, caller, word, takeRecord, projected⟩ := ready
  refine ⟨slice, remaining, locals, lifetime, contents, word, takeRecord, ?_⟩
  intro model seed predicate rows initial frame coupled trailing mismatch
  apply projected model seed trailing mismatch
  have aligned : key.arguments = slice.items := (OwnedCall.key_arguments request values key made).trans contents.symm
  exact miss_traced_verified ops allocate safety owner meaning base growth usizeBits children observations debug
    source address input request key slice deterministic called.world buffer remaining taken.1.2 missLeading trailing model seed
    predicate request.arguments rows initial frame aligned coupled mismatch lifetime.detached unowned caller

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
