/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolReturn
import Compiler.Extraction.InternerConstructorScratch
import Compiler.Extraction.InternerCallerProtocolInitializedMiss

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source : View) (request : Interner.Request)

/-- The full initialized miss at the reached argument state. The outer
constructor may add its actual argument retirement or host projection through `returned`.
The final equality retains the entire capture, including its native state;
no enclosing preservation result or final frame is assumed. -/
def PreparedMiss (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (action : List ProtocolEvent → Except Fault NodeId × Recorded τ)
    (returned : (Except Fault NodeId × Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent))) →
      Except Fault NodeId × Recorded τ) : Prop :=
  ∀ (constructed : ChildTrace.TracedWorld σ ProtocolEvent) (address : Compiler.ZigAir.Memory.Address),
    (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues → AssemblyItem.Initializers.DebugTyped debug →
    prepare request.item debug before = (.ok address, constructed) →
    base.queries.atCapacity constructed.graph = false → Admitted (Publication.external ops.arguments) →
    ∀ (leading : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32),
    ∃ stack, Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, stack) ∧
    ∀ (values : List NodeId) (prepared called : OwnedCall.State (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
      (key : Key) (deterministic commutative : Bool),
      Interner.Scoped.commutative request.item = .ok commutative →
      Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source
        ⟨constructed.memory.memory.nextId, 0, 2⟩ request
        ⟨{ constructed with memory := { constructed.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, prepared) →
      OwnedCall.take (Publication.external ops.arguments) base.allocator prepared = (.ok (), called) →
      base.queries.deterministic request.item = .ok deterministic →
      Interner.makeKey request values = .ok key →
      (deterministic = true → constructed.graph.table key = none) →
      let buffer : View := ⟨constructed.memory.memory.nextId, 0, 2⟩
      let start := { constructed with memory := { constructed.memory with memory := stack } }
      let init := Caller.Initialization.capture (Publication.external ops.arguments) base.budget base.allocator
        commutative source buffer request.arguments start.memory
      ∃ lookup, init.1 = .ok (some lookup) ∧
        let handle := init.2.effects.handle
        let taken := Caller.Take.capture (Publication.external ops.arguments) base.allocator lookup.origin handle prepared.world.memory
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
            seed.atCapacity { constructed.graph with allocationCursor := leading.length } = base.queries.atCapacity constructed.graph →
            seed.deterministic request.item = base.queries.deterministic request.item →
            ∀ (trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault),
              let child := ChildTrace.constructors children observations
              let observedChildren := ChildTrace.liftObservations observations
              let nativeInput := input request.item debug
              let p := Caller.ProtocolTrace.Native.physical ops allocate safety owner meaning base growth usizeBits child debug source address nativeInput
              let ports := Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits
                child observedChildren debug source address nativeInput
              let middle := Caller.ProtocolTrace.Native.middle ops allocate safety owner meaning base growth usizeBits
                child observedChildren debug source address nativeInput request key slice deterministic called.world
              let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits child debug source address nativeInput
                request key slice deterministic called.world remaining taken.1.2
              let events := missLeading ++ middle ++ observed.body ++ observed.cleanup ++ trailing
              let r := resources events (.preparation .incomplete)
              let logicalModel := dispatchModel (MissStream.replay seed events observed.candidate mismatch) model usizeBits debug
              let entry : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) :=
                ⟨⟨start, { lookup := none }⟩, {}, leading⟩
              let body := Caller.ProtocolTrace.findBody (Publication.external ops.arguments) base.budget base.allocator
                p base.queries ports source buffer request entry
              let finished := Caller.ProtocolTrace.find (Publication.external ops.arguments) base.budget base.allocator
                p base.queries ports source buffer request entry
              let logical := Interner.Scoped.findDetailed r logicalModel request { constructed.graph with allocationCursor := leading.length }
              let actual := action leading
              ordinary body.1 = true →
                outcome actual = (logical.1.mapError Fault.language, logical.2,
                  missLeading ++ middle ++ observed.body ++ observed.cleanup, false) ∧
                actual = returned (retire before.memory.memory.nextId (retire constructed.memory.memory.nextId finished))

/-- Every actual item entry supplies the same reached-state miss contract.
Argument-producing wrappers discharge `Good` from their native preparation. -/
def ItemMiss (action : Capture (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) NodeId) : Prop :=
  ∀ before, Good source request.arguments before →
    PreparedMiss ops allocate safety owner meaning base growth usizeBits children observations debug source request before (action before) id

/-- Consume the full initialized-caller theorem in the actual item wrapper.
Typed successful item preparation supplies scratch allocation and preserved
source reads. The shared return theorem handles both native marks and all
caller-local protocol metadata. No enclosing constructor projection is assumed. -/
theorem item_miss_traced :
    ItemMiss ops allocate safety owner meaning base growth usizeBits children observations debug source request
      (item (NativeRecursion.context (callerContext ops allocate safety owner meaning base growth) owner usizeBits
        (ChildTrace.constructors children observations) debug)
        (Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits
          (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug) source request debug) := by
  intro before good constructed address domain typed made room admitted leading other read sequence
  obtain ⟨stack, allocated⟩ := prepare_scratch request.item debug before constructed address good.1 domain typed made
  have preparedItem := (prepare_success request.item debug before constructed address good.1 domain typed made).2
  have constructedGood := good_frame before constructed source request.arguments good preparedItem.valid preparedItem.memory
  refine ⟨stack, allocated, ?_⟩
  intro values prepared called key deterministic commutative decoded initialized transferred classified keyed absent
  intro buffer start init
  obtain ⟨lookup, captured, projected⟩ := Caller.ProtocolTrace.Native.initialized_miss_traced ops allocate safety owner meaning
    base growth usizeBits children observations debug source address (input request.item debug) request key deterministic commutative
    constructed stack _ values prepared called leading other read sequence constructedGood.1 constructedGood.2 allocated decoded admitted
    initialized transferred room classified keyed absent
  refine ⟨lookup, captured, ?_⟩
  intro handle taken missLeading
  obtain ⟨slice, remaining, locals, lifetime, contents, word, projected⟩ := projected
  refine ⟨slice, remaining, locals, lifetime, contents, word, ?_⟩
  intro model seed predicate rows initial frame coupled capacityQuery classificationQuery trailing mismatch
  intro child observedChildren nativeInput p ports middle observed events r logicalModel entry body finished logical actual completed
  have checked := projected model seed predicate rows initial frame coupled capacityQuery classificationQuery trailing mismatch completed
  have returned := item_returned (NativeRecursion.context (callerContext ops allocate safety owner meaning base growth)
    owner usizeBits child debug)
    (Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits child observedChildren debug)
    source request debug before constructed address _ stack leading made room allocated
  refine ⟨returned.2.1.trans ?_, returned.1⟩
  change outcome finished = _
  have callerResult : (finished.1, scopeView finished.2) = (logical.1.mapError Fault.language, logical.2) ∧
      finished.2.events = missLeading ++ middle ++ observed.body ++ observed.cleanup ∧ finished.2.tokens.incomplete = false := checked
  obtain ⟨result, scopeEq⟩ := Prod.mk.inj callerResult.1
  simp only [outcome, result, scopeEq, callerResult.2.1, callerResult.2.2]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
