/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerMissReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

attribute [local irreducible] Caller.Initialization.capture Caller.Take.capture segment

/-- The actual initialization and take now enter the whole scoped miss through
recorded suffix ports. The continuation receives the real detached handle and
normalized slice; neither suffix graph projections nor lifetime contracts are
assumed. Only the dispatcher/child segment and its cursor boundaries remain
explicit, along with the proper-child preservation hypothesis. -/
theorem initialized_from_children (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (debug : AssemblyItem.Fields.Values)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (deterministic commutative : Bool)
    (before : World (Publication.Effects σ)) (stack : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared called : OwnedCall.State (Publication.Effects σ))
    (leading : List (Event Failure Insertion.Native.Fault)) (other : Meaning) (read : Read) (sequence : BitVec 32)
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
        ∀ (cursor : World (Publication.Effects σ) → Nat) (model : Associative.Constructors AssemblyItem.Fields.Values)
          (seed : Interner.Primitives) (predicate : World (Publication.Effects σ) → Prop) (originalRows : List Storage.Cell),
          predicate called.world → InputFrame safety base.allocator owner originalRows source request.arguments slice called.world →
          key.arguments = values →
          (∀ rows, (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
            InputFrame safety base.allocator owner rows source request.arguments slice world)).SourceConstructorsAt (Nested.storageReads rows) debug children model) →
          ∀ (middle trailing : List (Event Failure Insertion.Native.Fault)) (mismatch : Insertion.Native.Fault),
            let tailLeading := missLeading ++ middle
            let observed := segment ops allocate safety owner meaning base growth usizeBits children debug source address input
              request key slice deterministic called.world remaining taken.1.2
            let events := tailLeading ++ observed.body ++ observed.cleanup ++ trailing
            let r := resources events (.preparation .incomplete)
            let initialScope := Interner.Scoped.initScope r request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
            let takeScope := Interner.Scoped.take r initialScope.2
            let p := physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input
            let decision := selected p request key slice deterministic called.world
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
            Completion ops allocate safety owner meaning base growth usizeBits children debug source address input
              request key slice deterministic called.world remaining taken.1.2 request.arguments tailLeading trailing mismatch ∧
            (ordinary decision.1 = true → cursor called.world = missLeading.length → cursor decision.2 = tailLeading.length →
              actual.1 = logical.1.mapError Fault.language ∧
              logical.2 = ⟨⟨some taken.1.2, remaining.values, observed.phase⟩,
                { actual.2.world.graph with allocationCursor := (tailLeading ++ observed.body).length }⟩ ∧
              (ordinary actual.1 = true →
                Caller.Close.checked close (normalizations (tailLeading ++ observed.body)) (normalizations trailing)
                  taken.1.2 observed.phase remaining.values logical.2.heap = .ok (Interner.Scoped.close r logical.2))) := by
  intro start initialization
  obtain ⟨lookup, captured, prefixProof⟩ := Caller.Take.initialized_taken_stream (Publication.external ops.arguments)
    base.budget base.allocator commutative source request before stack pointer values prepared called leading other read sequence
    valid represented allocated decoded admitted initialized transferred
  refine ⟨lookup, captured, ?_⟩
  intro handle taken missLeading
  obtain ⟨slice, remaining, locals, lifetime, contents, unowned, caller, word, prefixProof⟩ := prefixProof
  refine ⟨slice, remaining, locals, lifetime, lifetime.values.trans contents, word, ?_⟩
  intro cursor model seed predicate originalRows initial frame aligned coupled middle trailing mismatch
  intro tailLeading observed events r initialScope takeScope p decision actual logical close
  -- Keep the shared event order explicit before comparing whole executions.
  have eventOrder : events = tailLeading ++ observed.body ++ observed.cleanup ++ trailing := rfl
  have composed := scoped_from_children ops allocate safety owner meaning base growth usizeBits children debug source address input
    request key slice deterministic called.world remaining taken.1.2 cursor model seed predicate request.arguments originalRows
    initial frame (aligned.trans (lifetime.values.trans contents).symm) (fun _ => coupled) tailLeading trailing mismatch lifetime.detached unowned caller
  obtain ⟨_, _, initChecked, takeChecked, succeeded, takenState⟩ := prefixProof (middle ++ observed.body ++ observed.cleanup ++ trailing)
  have shape : takeScope.2 = ⟨⟨some taken.1.2, remaining.values, .cleanup⟩,
      { called.world.graph with allocationCursor := missLeading.length }⟩ := by
    simpa only [takeScope, initialScope, r, eventOrder, tailLeading, missLeading, List.append_assoc] using takenState
  refine ⟨?_, ?_, ?_, composed.1, ?_⟩
  · simpa only [initialScope, r, eventOrder, tailLeading, missLeading, List.append_assoc] using initChecked
  · simpa only [takeScope, initialScope, r, eventOrder, tailLeading, missLeading, List.append_assoc] using takeChecked
  · simpa only [takeScope, initialScope, r, eventOrder, tailLeading, missLeading, List.append_assoc] using succeeded
  · intro completed entered ended
    have projected := composed.2 completed ended
    have nativeState : (⟨called.world, ⟨some remaining, some slice, false⟩⟩ : OwnedCall.State (Publication.Effects σ)) = called := by
      rw [← locals]
    have scopeSame : takeScope.2 = ⟨⟨some taken.1.2, remaining.values, .cleanup⟩, cursorGraph cursor called.world⟩ := by
      simpa only [cursorGraph, entered] using shape
    simpa only [Projected, logical, scopeSame, actual, nativeState, close, observed, eventOrder, r, p] using projected

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.MissStream
