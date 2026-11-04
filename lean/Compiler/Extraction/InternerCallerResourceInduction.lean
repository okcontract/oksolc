/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolInduction
import Compiler.Extraction.InternerCallerResourceReplay

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.ResourceEntry
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

/-- Resource-aware induction data at the actual taken state. Admission is bound
to its captured child stream and complete suffix; the native frame remains
explicit. The fixed entry model must use the same
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
      let child := ChildTrace.constructors children observations
      let middle := Native.middle ops allocate safety owner meaning base growth usizeBits child
        (ChildTrace.liftObservations observations) debug source address input request key slice deterministic taken.native.world
      let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits child debug source address input
        request key slice deterministic taken.native.world handle lookup
      let events := taken.events ++ middle ++ observed.body ++ observed.cleanup ++ trailing
      let stream := ChildTrace.history (MissStream.selected
        (physical ops allocate safety owner meaning base growth usizeBits child debug source address input)
        request key slice deterministic taken.native.world).2 ++ observed.body ++ observed.cleanup ++ trailing
      ((deterministic && (request.item.kind == 1)) = true →
        ∀ rows, (Resource.projection ChildTrace.history stream
          (cursorGraph (MissStream.childCursor taken.events.length taken.native.world))
          (fun world => predicate world ∧ InputFrame safety base.allocator owner rows source request.arguments slice world)).SourceConstructorsAt
            (Nested.storageReads rows) debug child childModel) ∧
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

/-- Existing all-input child proofs specialize the resource-aware relation.
The actual recorder supplies history growth, including ordinary failures. -/
theorem source_of_projects (stream : List ProtocolEvent) (cursor : ChildTrace.TracedWorld σ ProtocolEvent → Nat)
    (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (reads : Nested.Reads)
    (model : Associative.Constructors AssemblyItem.Fields.Values)
    (related : (projectionAt (cursorGraph cursor) predicate).SourceConstructorsAt reads debug
      (ChildTrace.constructors children observations) model) :
    (Resource.projection ChildTrace.history stream (cursorGraph cursor) predicate).SourceConstructorsAt reads debug
      (ChildTrace.constructors children observations) model := by
  have lift (action : GraphAction (Publication.Effects σ) NodeId)
      (observed : World (Publication.Effects σ) → List ProtocolEvent) (logical : Interner.Action NodeId)
      (same : ProjectsAt (cursorGraph cursor) predicate (ChildTrace.record action observed) logical) :
      Resource.Projects ChildTrace.history stream (cursorGraph cursor) predicate (ChildTrace.record action observed) logical :=
    Resource.Projects.of_projects _ _ _ _ _ _ (fun before => ⟨observed (ChildTrace.erase before), rfl⟩) same
  rcases related with ⟨operation, constant, materialize, borrowed, localRule⟩
  exact ⟨fun opcode values d => lift _ _ _ (operation opcode values d),
    fun value d => lift _ _ _ (constant value d), fun id value d => lift _ _ _ (materialize id value d),
    fun id queried source found opcode d => lift _ _ _ (borrowed id queried source found opcode d),
    fun id opcode source found shape selected bound repeated first d =>
      lift _ _ _ (localRule id opcode source found shape selected bound repeated first d)⟩

theorem MissInduction.of_unrestricted (model : Interner.Primitives) (key : Key) (deterministic : Bool)
    (taken : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent))) (trailing : List ProtocolEvent)
    (original : Native.MissInduction ops allocate safety owner meaning base growth usizeBits children observations
      debug source address input request model key deterministic taken trailing) :
    MissInduction ops allocate safety owner meaning base growth usizeBits children observations
      debug source address input request model key deterministic taken trailing := by
  intro slice handle lookup locals tokens
  obtain ⟨childModel, seed, predicate, rows, mismatch, initial, frame, coupled, bound⟩ := original slice handle lookup locals tokens
  refine ⟨childModel, seed, predicate, rows, mismatch, initial, frame, ?_, bound⟩
  intro selected rows
  exact source_of_projects children observations debug _ _ _ _ _ (coupled selected rows)

theorem EntryInduction.of_unrestricted (model : Interner.Primitives) (buffer : View)
    (before : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent))) (trailing : List ProtocolEvent)
    (original : Native.EntryInduction ops allocate safety owner meaning base growth usizeBits children observations
      debug source address input request model buffer before trailing) :
    EntryInduction ops allocate safety owner meaning base growth usizeBits children observations
      debug source address input request model buffer before trailing := by
  intro values key deterministic normalized taken room initialized classified made absent transferred
  exact MissInduction.of_unrestricted ops allocate safety owner meaning base growth usizeBits children observations
    debug source address input request model key deterministic taken.2 trailing
    (original values key deterministic room initialized classified made absent transferred)

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
  obtain ⟨lookup, captured, ready⟩ := initialized_miss_projected ops allocate safety owner meaning base growth usizeBits
    children observations debug source address input request key deterministic commutative before memory pointer values
    normalized.2.native taken.2.native leading other read sequence valid represented allocated decoded admitted
    nativeInitialized nativeTaken room classified made absent
  dsimp only at ready
  obtain ⟨slice, remaining, locals, lifetime, contents, unowned, caller, _, takeRecord, projected⟩ := ready
  have localInduction := induction values key deterministic room initialized classified made absent transferred
  change MissInduction ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    request model key deterministic taken.2 trailing at localInduction
  change taken = _ at takeRecord
  rw [takeRecord] at localInduction
  obtain ⟨childModel, seed, predicate, rows, mismatch, initial, frame, coupled, bound⟩ :=
    localInduction slice remaining _ locals rfl
  have aligned : key.arguments = slice.items := (OwnedCall.key_arguments request values key made).trans contents.symm
  have projectedMiss := miss_resource_traced ops allocate safety owner meaning base growth usizeBits children observations debug
    source address input request key slice deterministic taken.2.native.world ⟨before.memory.memory.nextId, 0, 2⟩ remaining _
    _ trailing childModel seed predicate request.arguments rows initial frame aligned mismatch lifetime.detached unowned caller coupled
  obtain ⟨continuation, _⟩ := projected childModel seed trailing mismatch projectedMiss
  have fixed : MissContinuation (Publication.external ops.arguments) base.budget base.allocator
      (physical ops allocate safety owner meaning base growth usizeBits (ChildTrace.constructors children observations) debug source address input)
      base.queries (graphObservations ops allocate safety owner meaning base growth usizeBits
        (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug source address input)
      model source ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩ trailing := by
    simpa only [bound] using continuation
  exact fixed values key deterministic room initialized classified made absent transferred

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.ResourceEntry
