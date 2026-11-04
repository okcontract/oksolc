/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolContinuation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

attribute [local irreducible] Initialization.capture Take.capture

/-- An initialized native caller consumes its computed child history and
ordinary miss/close proof through the general all-entry caller theorem.
Initialization, take, miss and close use one stream;
no reached token, numeric boundary, suffix admission or cleanup success is
supplied. Proper-child preservation and the initial native input frame remain
explicit, together with pointwise source-query bindings. -/
theorem initialized_miss_traced
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
        ∀ (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
          (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (rows : List Storage.Cell),
          predicate called.world → InputFrame safety base.allocator owner rows source request.arguments slice called.world →
          (∀ rows, (projectionAt (cursorGraph (MissStream.childCursor missLeading.length called.world))
            (fun world => predicate world ∧ InputFrame safety base.allocator owner rows source request.arguments slice world)).SourceConstructorsAt (Nested.storageReads rows) debug
              (ChildTrace.constructors children observations) model) →
          seed.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph →
          seed.deterministic request.item = base.queries.deterministic request.item →
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
            let r := resources events (.preparation .incomplete)
            let logicalModel := dispatchModel (MissStream.replay seed events observed.candidate mismatch) model usizeBits debug
            let entry : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) :=
              ⟨⟨start, { lookup := none }⟩, {}, leading⟩
            let body := findBody (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer request entry
            let actual := find (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer request entry
            let logical := Interner.Scoped.findDetailed r logicalModel request { before.graph with allocationCursor := leading.length }
            ordinary body.1 = true →
              (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧
              actual.2.events = missLeading ++ middle ++ observed.body ++ observed.cleanup ∧ actual.2.tokens.incomplete = false := by
  intro buffer start init
  obtain ⟨lookup, captured, prefixProof⟩ := initialized_miss_continuation ops allocate safety owner meaning
    base growth usizeBits children observations debug source address input request key deterministic commutative
    before stack pointer values prepared called leading other read sequence valid represented allocated decoded
    admitted initialized transferred room classified made absent
  refine ⟨lookup, captured, ?_⟩
  intro handle taken missLeading
  obtain ⟨slice, remaining, locals, lifetime, contents, word, _, projected⟩ := prefixProof
  refine ⟨slice, remaining, locals, lifetime, contents, word, ?_⟩
  intro model seed predicate rows initial frame coupled capacityQuery classificationQuery trailing mismatch
  intro child observedChildren p ports middle observed events r logicalModel entry body actual logical completed
  obtain ⟨continuation, history⟩ := projected model seed predicate rows initial frame (fun _ => coupled) trailing mismatch
  have complete := find_projected (Publication.external ops.arguments) base.budget base.allocator p base.queries ports logicalModel
    source request before stack pointer leading trailing other read sequence valid represented allocated admitted
    capacityQuery classificationQuery continuation completed
  have eventsEq := history completed
  change actual.2.events = missLeading ++ middle ++ observed.body ++ observed.cleanup at eventsEq
  refine ⟨?_, eventsEq, complete.2⟩
  have projectedFind := complete.1
  change (actual.1, scopeView actual.2) =
    ((Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) logicalModel request
      { before.graph with allocationCursor := leading.length }).1.mapError Fault.language,
     (Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) logicalModel request
      { before.graph with allocationCursor := leading.length }).2) at projectedFind
  simpa only [eventsEq] using projectedFind

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
