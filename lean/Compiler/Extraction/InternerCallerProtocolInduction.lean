/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolContinuation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (request : Interner.Request)

/-- Local induction data at the actual taken state. The native input frame and
proper-child relation remain explicit. The fixed entry model must use the same
dispatcher, children and recorded insertion/publication ports. No caller or
miss result, cleanup success, or final preservation is assumed. -/
def MissInduction (model : Interner.Primitives) (key : Key) (deterministic : Bool)
    (taken : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (trailing : List ProtocolEvent) : Prop :=
  ∀ (slice : ArgumentSlice) (handle : Handle) (lookup : NormalizationOwnership.State),
    taken.native.scope = ⟨some handle, some slice, false⟩ →
    taken.tokens = { lookup := some lookup, items := handle.values, phase := .cleanup } →
    ∃ (childModel : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
      (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (rows : List Storage.Cell)
      (mismatch : Insertion.Native.Fault),
      predicate taken.native.world ∧
      InputFrame safety base.allocator owner rows source request.arguments slice taken.native.world ∧
      ((deterministic && (request.item.kind == 1)) = true →
        ∀ rows, (projectionAt (cursorGraph (MissStream.childCursor taken.events.length taken.native.world))
        (fun world => predicate world ∧ InputFrame safety base.allocator owner rows source request.arguments slice world)).SourceConstructorsAt (Nested.storageReads rows) debug
          (ChildTrace.constructors children observations) childModel) ∧
      let child := ChildTrace.constructors children observations
      let middle := Native.middle ops allocate safety owner meaning base growth usizeBits child
        (ChildTrace.liftObservations observations) debug source address input request key slice deterministic taken.native.world
      let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits child debug source address input
        request key slice deterministic taken.native.world handle lookup
      let events := taken.events ++ middle ++ observed.body ++ observed.cleanup ++ trailing
      model = dispatchModel (MissStream.replay seed events observed.candidate mismatch) childModel usizeBits debug

/-- Only a source-selected miss requests induction data. Earlier failures and
cache hits impose no child, frame or replay-model obligation. -/
def EntryInduction (model : Interner.Primitives) (buffer : View)
    (before : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (trailing : List ProtocolEvent) : Prop :=
  ∀ (values : List NodeId) (key : Key) (deterministic : Bool),
    let normalized := record (Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source buffer request)
      (initialization (Publication.external ops.arguments) base.budget base.allocator source buffer request) before
    let taken := record (OwnedCall.take (Publication.external ops.arguments) base.allocator)
      (taking (Publication.external ops.arguments) base.allocator) normalized.2
    base.queries.atCapacity before.native.world.graph = false → normalized.1 = .ok values →
    base.queries.deterministic request.item = .ok deterministic → Interner.makeKey request values = .ok key →
    (deterministic = true → before.native.world.graph.table key = none) → taken.1 = .ok () →
    MissInduction ops allocate safety owner meaning base growth usizeBits children observations debug source address input
      request model key deterministic taken.2 trailing

/-- Derive the general caller's continuation from actual prefix execution and
proper-child induction data. Initialization/take supply their own scoped token,
ownership and event prefix; the child proof supplies miss execution and close.
The entry model is fixed before selecting any of these branches. -/
theorem entry_continuation (model : Interner.Primitives) (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (admitted : Admitted (Publication.external ops.arguments))
    (induction : EntryInduction ops allocate safety owner meaning base growth usizeBits children observations debug source address input
      request model ⟨before.memory.memory.nextId, 0, 2⟩
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩ trailing) :
    MissContinuation (Publication.external ops.arguments) base.budget base.allocator
      (physical ops allocate safety owner meaning base growth usizeBits (ChildTrace.constructors children observations) debug source address input)
      base.queries (graphObservations ops allocate safety owner meaning base growth usizeBits
        (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug source address input)
      model source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩ trailing := by
  intro values key deterministic normalized taken room initialized classified made absent transferred
  have nativeInitialized : Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source
      ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩ =
      (.ok values, normalized.2.native) := Prod.ext initialized rfl
  have nativeTaken : OwnedCall.take (Publication.external ops.arguments) base.allocator normalized.2.native =
      (.ok (), taken.2.native) := Prod.ext transferred rfl
  obtain ⟨commutative, decoded⟩ : ∃ commutative, Interner.Scoped.commutative request.item = .ok commutative := by
    cases decoded : Interner.Scoped.commutative request.item with
    | error error => simp only [Caller.initLookup, decoded] at nativeInitialized; cases nativeInitialized
    | ok commutative => exact ⟨commutative, rfl⟩
  obtain ⟨lookup, captured, ready⟩ := initialized_miss_continuation ops allocate safety owner meaning base growth usizeBits
    children observations debug source address input request key deterministic commutative before memory pointer values
    normalized.2.native taken.2.native leading other read sequence valid represented allocated decoded admitted
    nativeInitialized nativeTaken room classified made absent
  dsimp only at ready
  obtain ⟨slice, remaining, locals, _, _, _, takeRecord, projected⟩ := ready
  have localInduction := induction values key deterministic room initialized classified made absent transferred
  change MissInduction ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    request model key deterministic taken.2 trailing at localInduction
  change taken = _ at takeRecord
  rw [takeRecord] at localInduction
  obtain ⟨childModel, seed, predicate, rows, mismatch, initial, frame, coupled, bound⟩ :=
    localInduction slice remaining _ locals rfl
  obtain ⟨continuation, _⟩ := projected childModel seed predicate rows initial frame coupled trailing mismatch
  have fixed : MissContinuation (Publication.external ops.arguments) base.budget base.allocator
      (physical ops allocate safety owner meaning base growth usizeBits (ChildTrace.constructors children observations) debug source address input)
      base.queries (graphObservations ops allocate safety owner meaning base growth usizeBits
        (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug source address input)
      model source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩ trailing := by
    simpa only [bound] using continuation
  exact fixed values key deterministic room initialized classified made absent transferred

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
