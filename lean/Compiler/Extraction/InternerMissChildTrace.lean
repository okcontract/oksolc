/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInvocationChildTrace
import Compiler.Extraction.InternerMissInitialized

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

abbrev ProtocolEvent := Event Failure Insertion.Native.Fault

/-- Initialization/take determine the logical entry position. Child history is
relative to that entry, so pre-existing recorder history is neither recounted
as a protocol operation nor silently discarded. -/
def childCursor (start : Nat) (before world : ChildTrace.TracedWorld σ ProtocolEvent) : Nat :=
  start + (ChildTrace.history world).length - (ChildTrace.history before).length

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)

/-- The actual source guard either records the shared dispatcher or contributes
no events. The computed middle and both relative cursors hold on all outcomes,
without a child-success, cursor or caller-frame assumption. Correctness of each
child observation remains a proper-child protocol obligation. -/
theorem child_boundaries (request : Interner.Request) (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (start : Nat) :
    let p := physical ops allocate safety owner meaning base growth owner usizeBits
      (ChildTrace.constructors children observations) debug source address input
    let action := selected p request key slice deterministic
    let captured := action (ChildTrace.restore [] (ChildTrace.erase before))
    ChildTrace.history (action before).2 = ChildTrace.history before ++ ChildTrace.history captured.2 ∧
      childCursor start before before = start ∧
      childCursor start before (action before).2 = start + (ChildTrace.history captured.2).length := by
  intro p action captured
  have independent : ∀ leading, Effect.Transport
      (World.mapEffects (Publication.Effects.mapAllocator (ChildTrace.prepend leading))) action action := by
    intro leading before
    unfold action selected
    split
    · exact dispatcher_erases (Publication.Effects.mapAllocator (ChildTrace.prepend leading))
        (callerContext ops allocate safety owner meaning base growth) (callerContext ops allocate safety owner meaning base growth)
        owner usizeBits (ChildTrace.constructors_prefix children observations leading) debug source address input key slice before
    · rfl
  have recorded := (ChildTrace.action_segment action independent before).2
  change ChildTrace.history (action before).2 = ChildTrace.history before ++ ChildTrace.history captured.2 at recorded
  refine ⟨recorded, ?_, ?_⟩
  · simp only [childCursor, Nat.add_sub_cancel]
  · simp only [childCursor, recorded, List.length_append]
    omega

attribute [local irreducible] Caller.Initialization.capture Caller.Take.capture segment

/-- A computed child segment supplies the initialized miss's two cursor
boundaries. The shared native/scoped composition is unchanged. Proper children
must still prove their protocol/model relation and preserve the live parent;
their observations are implementation obligations, not admitted host behavior. -/
theorem initialized_recorded_children (request : Interner.Request) (key : Key) (deterministic commutative : Bool)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (stack : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared called : OwnedCall.State (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (leading : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, stack))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (admitted : Admitted (Publication.external ops.arguments))
    (initialized : Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source
      ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : OwnedCall.take (Publication.external ops.arguments) base.allocator prepared = (.ok (), called)) :
    let start := { before with memory := { before.memory with memory := stack } }
    let initialization := Caller.Initialization.capture (Publication.external ops.arguments) base.budget base.allocator
      commutative source ⟨before.memory.memory.nextId, 0, 2⟩ request.arguments start.memory
    ∃ lookup, initialization.1 = .ok (some lookup) ∧
      let handle := initialization.2.effects.handle
      let taken := Caller.Take.capture (Publication.external ops.arguments) base.allocator lookup.origin handle prepared.world.memory
      let missLeading := leading ++ initialization.2.events.map Event.normalization ++ taken.2.events.map Event.normalization
      ∃ slice remaining, called.scope = ⟨some remaining, some slice, false⟩ ∧
        Normalization.Taken base.allocator source request.arguments handle prepared.world.memory slice remaining called.world.memory ∧
        slice.items = values ∧
        request.item.eval (Folding.wordMeaning other) read values sequence =
          request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
        let traced := ChildTrace.constructors children observations
        let p := physical ops allocate safety owner meaning base growth owner usizeBits traced debug source address input
        let decision := selected p request key slice deterministic called.world
        let middle := ChildTrace.history (selected p request key slice deterministic (ChildTrace.restore [] (ChildTrace.erase called.world))).2
        let cursor := childCursor missLeading.length called.world
        ∀ (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
          (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (originalRows : List Storage.Cell),
          predicate called.world → InputFrame safety base.allocator owner originalRows source request.arguments slice called.world →
          key.arguments = values →
          (∀ rows, (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
            InputFrame safety base.allocator owner rows source request.arguments slice world)).SourceConstructorsAt (Nested.storageReads rows) debug traced model) →
          ∀ (trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault),
            let tailLeading := missLeading ++ middle
            let observed := segment ops allocate safety owner meaning base growth usizeBits traced debug source address input
              request key slice deterministic called.world remaining taken.1.2
            let events := tailLeading ++ observed.body ++ observed.cleanup ++ trailing
            let r := resources events (.preparation .incomplete)
            let initialScope := Interner.Scoped.initScope r request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
            let takeScope := Interner.Scoped.take r initialScope.2
            let actual := Interner.findCode.controlMiss (execution (Publication.external ops.arguments) base.allocator p)
              request key deterministic called
            let logical := Interner.findCode.controlMiss
              (Interner.Scoped.execution r (dispatchModel (replay seed events observed.candidate mismatch) model usizeBits debug))
              request key deterministic takeScope.2
            let close := Caller.Close.capture (Publication.external ops.arguments) base.allocator taken.1.2 observed.phase remaining actual.2
            Caller.Initialization.checked initialization (normalizations leading)
              (taken.2.events ++ normalizations (middle ++ observed.body ++ observed.cleanup ++ trailing)) request
              { before.graph with allocationCursor := leading.length } = .ok initialScope ∧
            Caller.Take.checked taken (normalizations leading ++ initialization.2.events)
              (normalizations (middle ++ observed.body ++ observed.cleanup ++ trailing)) lookup values initialScope.2.heap = .ok takeScope ∧
            takeScope.1 = .ok () ∧
            Completion ops allocate safety owner meaning base growth usizeBits traced debug source address input
              request key slice deterministic called.world remaining taken.1.2 request.arguments tailLeading trailing mismatch ∧
            ChildTrace.history decision.2 = ChildTrace.history called.world ++ middle ∧
            (ordinary decision.1 = true →
              actual.1 = logical.1.mapError Fault.language ∧
              logical.2 = ⟨⟨some taken.1.2, remaining.values, observed.phase⟩,
                { actual.2.world.graph with allocationCursor := (tailLeading ++ observed.body).length }⟩ ∧
              (ordinary actual.1 = true →
                Caller.Close.checked close (normalizations (tailLeading ++ observed.body)) (normalizations trailing)
                  taken.1.2 observed.phase remaining.values logical.2.heap = .ok (Interner.Scoped.close r logical.2))) := by
  intro start initialization
  obtain ⟨lookup, captured, prefixProof⟩ := initialized_from_children ops allocate safety owner meaning base growth usizeBits
    (ChildTrace.constructors children observations) debug source address input request key deterministic commutative
    before stack pointer values prepared called leading other read sequence valid represented allocated decoded admitted initialized transferred
  refine ⟨lookup, captured, ?_⟩
  intro handle taken missLeading
  obtain ⟨slice, remaining, locals, lifetime, contents, word, continuation⟩ := prefixProof
  refine ⟨slice, remaining, locals, lifetime, contents, word, ?_⟩
  intro traced p decision middle cursor model seed predicate originalRows initial frame aligned coupled trailing mismatch
  intro tailLeading observed events r initialScope takeScope actual logical close
  have composed := continuation cursor model seed predicate originalRows initial frame aligned coupled middle trailing mismatch
  have boundaries := child_boundaries ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    request key slice deterministic called.world missLeading.length
  exact ⟨composed.1, composed.2.1, composed.2.2.1, composed.2.2.2.1, boundaries.1,
    fun ordinary => composed.2.2.2.2 ordinary boundaries.2.1 (by
      change cursor decision.2 = (missLeading ++ middle).length
      rw [List.length_append]
      exact boundaries.2.2)⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
