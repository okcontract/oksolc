/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointInputModel
import Compiler.Extraction.InternerCallerProtocolComplete

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.CheckpointEntry
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Recursive Interner.InvocationTrace

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (debug : AssemblyItem.Fields.Values)
    (source : View) (address : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (incoming : Nat) (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)

local notation "physicalPorts" => physical ops allocate safety owner meaning base growth usizeBits children debug source address input
local notation "recordedPorts" => AllocationTrace.graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
local notation "entryModel" => dispatchModel (AllocationTrace.inputGraphReplay seed input incoming meaning stream mismatch) model usizeBits debug

/-- Local proper-child obligations at a source-selected miss. The model was
fixed at entry: neither the normalized descriptor nor a completed candidate is
part of its construction. Frame, dispatcher correspondence and full stream
binding remain obligations of the recursive body, not trusted assumptions. -/
def Miss (key : Key) (deterministic : Bool) (taken : Recorded (Publication.Effects σ))
    (trailing : List ProtocolEvent) : Prop :=
  ∀ (slice : ArgumentSlice) (handle : Handle) (lookup : NormalizationOwnership.State),
    taken.native.scope = ⟨some handle, some slice, false⟩ →
    taken.tokens = { lookup := some lookup, items := handle.values, phase := .cleanup } →
    key.arguments = slice.items →
    ∃ (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop),
      let decision := MissStream.selected physicalPorts request key slice deterministic taken.native.world
      let middle := if deterministic && request.item.kind == 1 then (recordedPorts).simplify key slice taken.native.world else []
      let observed := MissStream.segment ops allocate safety owner meaning base growth usizeBits children debug source address input
        request key slice deterministic taken.native.world handle lookup
      let bodyEvents := match decision.1 with
        | .ok none => (recordedPorts).insert key slice deterministic decision.2
        | _ => observed.body
      let history := taken.events ++ middle ++ bodyEvents ++ observed.cleanup
      let logicalDecision := if deterministic && request.item.kind == 1 then (entryModel).simplify key (scopeView taken).heap
        else (.ok none, (scopeView taken).heap)
      (ordinary decision.1 = true → CallFrame safety base.allocator owner rows source request.arguments slice address input parent decision.2) ∧
      history ++ trailing = stream ∧
      (ordinary decision.1 = true → decision.1 = logicalDecision.1.mapError Fault.language ∧
        { decision.2.graph with allocationCursor := (taken.events ++ middle).length } = logicalDecision.2)

/-- Shared source guards for local miss obligations. Earlier errors and hits
impose none; both entry replay and proper-child bodies use this same prefix. -/
def AtMiss (next : Key → Bool → Recorded (Publication.Effects σ) → Prop)
    (buffer : View) (before : Recorded (Publication.Effects σ)) : Prop :=
  ∀ (values : List NodeId) (key : Key) (deterministic : Bool),
    let normalized := record (Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source buffer request)
      (initialization (Publication.external ops.arguments) base.budget base.allocator source buffer request) before
    let taken := record (OwnedCall.take (Publication.external ops.arguments) base.allocator)
      (taking (Publication.external ops.arguments) base.allocator) normalized.2
    base.queries.atCapacity before.native.world.graph = false → normalized.1 = .ok values →
    base.queries.deterministic request.item = .ok deterministic → Interner.makeKey request values = .ok key →
    (deterministic = true → before.native.world.graph.table key = none) → taken.1 = .ok () →
    next key deterministic taken.2

theorem AtMiss.mono (left right : Key → Bool → Recorded (Publication.Effects σ) → Prop)
    (buffer : View) (before : Recorded (Publication.Effects σ))
    (convert : ∀ key deterministic taken, left key deterministic taken → right key deterministic taken)
    (ready : AtMiss ops base source request left buffer before) :
    AtMiss ops base source request right buffer before := by
  intro values key deterministic normalized taken room initialized classified made absent transferred
  exact convert key deterministic taken.2 (ready values key deterministic room initialized classified made absent transferred)

/-- Initialization/take select the local proof while retaining the model and
stream fixed at entry. Alignment and ordinary status are derived by its caller. -/
def Induction (buffer : View) (before : Recorded (Publication.Effects σ)) (trailing : List ProtocolEvent) : Prop :=
  AtMiss ops base source request
    (fun key deterministic taken => Miss ops allocate safety owner meaning base growth usizeBits children observations debug
      source address input request model seed incoming stream mismatch key deterministic taken trailing) buffer before

omit incoming in
/-- The actual initialized caller consumes the fixed input model. Its key
arguments and the only relevant incoming address are derived from init/take;
the complete checkpoint miss supplies body, cleanup and recorder completion. -/
theorem entry_continuation (before : World (Publication.Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted ops.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (closedQuery : base.queries.deterministic request.item = Interner.Queries.queries.deterministic request.item)
    (induction : Induction ops allocate safety owner meaning base growth usizeBits children observations debug source address input request model seed
      (before.memory.memory.nextId + 1) stream mismatch ⟨before.memory.memory.nextId, 0, 2⟩
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩ trailing) :
    MissContinuation (Publication.external ops.arguments) base.budget base.allocator physicalPorts base.queries recordedPorts
      (dispatchModel (AllocationTrace.inputGraphReplay seed input (before.memory.memory.nextId + 1) meaning stream mismatch) model usizeBits debug)
      source ⟨before.memory.memory.nextId, 0, 2⟩ request
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
    | error fault => simp only [Caller.initLookup, decoded] at nativeInitialized; cases nativeInitialized
    | ok commutative => exact ⟨commutative, rfl⟩
  obtain ⟨lookup, captured, ready⟩ := initialized_taken_recorded (Publication.external ops.arguments) base.budget base.allocator commutative
    source request before memory pointer values normalized.2.native taken.2.native leading other read sequence
    good.1 good.2 allocated decoded (Publication.external_admitted ops.arguments admitted) nativeInitialized nativeTaken
  dsimp only at ready
  obtain ⟨slice, remaining, locals, lifetime, contents, unowned, caller, _, _, takeRecord, _⟩ := ready
  have inputs := Caller.taken_replay_inputs (Publication.external ops.arguments) base.budget base.allocator source request before memory pointer
    values normalized.2.native taken.2.native key slice deterministic good (Publication.external_admitted ops.arguments admitted)
    allocated nativeInitialized nativeTaken (closedQuery ▸ classified) made (congrArg Local.slice locals)
  have localStep := induction values key deterministic room initialized classified made absent transferred
  change Miss ops allocate safety owner meaning base growth usizeBits children observations debug source address input request model seed
    (before.memory.memory.nextId + 1) stream mismatch key deterministic taken.2 trailing at localStep
  change taken = _ at takeRecord
  have selectedOrdinary := missBody_selected_ordinary (Publication.external ops.arguments) base.budget base.allocator physicalPorts
    base.queries recordedPorts source ⟨before.memory.memory.nextId, 0, 2⟩ request key slice deterministic taken.2 remaining locals
  rw [takeRecord] at localStep selectedOrdinary ⊢
  obtain ⟨rows, parent, frame, history, projected⟩ := localStep slice remaining _ locals rfl inputs.1.symm
  let oldModel := dispatchModel (AllocationTrace.graphReplay seed input slice meaning stream mismatch) model usizeBits debug
  let fixedModel := dispatchModel (AllocationTrace.inputGraphReplay seed input (before.memory.memory.nextId + 1) meaning stream mismatch) model usizeBits debug
  have sameLogical (resources : Interner.Scoped.Resources) (scope : Interner.Scoped.Session) :
      Interner.findCode.controlMiss (Interner.Scoped.execution resources oldModel) request key deterministic scope =
        Interner.findCode.controlMiss (Interner.Scoped.execution resources fixedModel) request key deterministic scope := by
    apply MissStream.scoped_ports resources oldModel fixedModel request key deterministic scope rfl rfl
    simpa only [oldModel, fixedModel, dispatchModel, AllocationTrace.graphReplay, AllocationTrace.inputGraphReplay] using
      (AllocationTrace.insertionReplay_inputs input slice (before.memory.memory.nextId + 1) meaning key deterministic stream mismatch inputs.1 inputs.2)
  have shape : (⟨taken.2.native.world, ⟨some remaining, some slice, false⟩⟩ : OwnedCall.State _) = taken.2.native := by rw [← locals]
  intro body actual resources logical completed
  obtain ⟨selected, reached⟩ := projected (selectedOrdinary completed)
  have checked := checkpoint_miss ops allocate safety owner meaning base growth usizeBits children observations debug
    source ⟨before.memory.memory.nextId, 0, 2⟩ address input request key slice deterministic taken.2.native.world remaining _ model seed
    request.arguments rows parent _ stream mismatch admitted inputs.1.symm lifetime.detached unowned caller frame
    ⟨trailing, history⟩ selected reached
  rw [shape] at checked
  have done := checked completed
  rw [sameLogical] at done
  have consumed : actual.2.events ++ trailing = stream := done.2.2.1 ▸ history
  change (actual.1, scopeView actual.2) =
    ((Interner.findCode.controlMiss (Interner.Scoped.execution (Interner.InvocationTrace.resources (actual.2.events ++ trailing) (.preparation .incomplete)) fixedModel)
      request key deterministic _).1.mapError Fault.language,
      Interner.Scoped.close (Interner.InvocationTrace.resources (actual.2.events ++ trailing) (.preparation .incomplete))
        (Interner.findCode.controlMiss (Interner.Scoped.execution (Interner.InvocationTrace.resources (actual.2.events ++ trailing) (.preparation .incomplete)) fixedModel)
          request key deterministic _).2) ∧ actual.2.tokens.incomplete = false
  rw [consumed]
  exact ⟨done.2.1, done.2.2.2⟩

omit incoming in
/-- The fixed input model reaches the complete caller, including ordinary
early errors and cache hits. Initialization, allocation, take and deferred
cleanup are shared with the existing all-entry caller proof. -/
theorem find_projected (before : World (Publication.Effects σ))
    (memory : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted ops.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, memory))
    (closedQuery : base.queries.deterministic request.item = Interner.Queries.queries.deterministic request.item)
    (capacityQuery : seed.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
    (classificationQuery : seed.deterministic request.item = base.queries.deterministic request.item)
    (induction : Induction ops allocate safety owner meaning base growth usizeBits children observations debug source address input request model seed
      (before.memory.memory.nextId + 1) stream mismatch ⟨before.memory.memory.nextId, 0, 2⟩
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩ trailing) :
    let logicalModel := dispatchModel (AllocationTrace.inputGraphReplay seed input (before.memory.memory.nextId + 1) meaning stream mismatch) model usizeBits debug
    let entry : Recorded (Publication.Effects σ) :=
      ⟨⟨{ before with memory := { before.memory with memory } }, { lookup := none }⟩, {}, leading⟩
    let body := findBody (Publication.external ops.arguments) base.budget base.allocator physicalPorts base.queries recordedPorts
      source ⟨before.memory.memory.nextId, 0, 2⟩ request entry
    let actual := find (Publication.external ops.arguments) base.budget base.allocator physicalPorts base.queries recordedPorts
      source ⟨before.memory.memory.nextId, 0, 2⟩ request entry
    let logical := Interner.Scoped.findDetailed (resources (actual.2.events ++ trailing) (.preparation .incomplete)) logicalModel request
      { before.graph with allocationCursor := leading.length }
    ordinary body.1 = true →
      (actual.1, scopeView actual.2) = (logical.1.mapError Fault.language, logical.2) ∧ actual.2.tokens.incomplete = false := by
  intro logicalModel entry body actual logical completed
  have checked := Caller.ProtocolTrace.find_projected (Publication.external ops.arguments) base.budget base.allocator physicalPorts base.queries recordedPorts
    logicalModel source request before memory pointer leading trailing other read sequence good.1 good.2 allocated
    (Publication.external_admitted ops.arguments admitted) capacityQuery classificationQuery
    (entry_continuation ops allocate safety owner meaning base growth usizeBits children observations debug source address input request model seed
      stream mismatch before memory pointer leading trailing other read sequence good admitted allocated closedQuery induction)
  exact checked completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.CheckpointEntry
