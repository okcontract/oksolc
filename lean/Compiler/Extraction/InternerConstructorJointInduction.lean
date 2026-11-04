/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolInduction
import Compiler.Extraction.InternerNativeConstructorWords

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

/-- The already defined native recorder at the actual initialization/take
prefix. No caller control or observation is replaced by this composition. -/
def takenPrefix (external : External σ) (budget allocator : Nat) (source : View)
    (request : Interner.Request) (constructed : World σ) (memory : Compiler.ZigAir.Memory.State)
    (leading : List ProtocolEvent) : Except Fault Unit × Recorded σ :=
  let buffer : View := ⟨constructed.memory.memory.nextId, 0, 2⟩
  let ready := start { constructed with memory := { constructed.memory with memory } } leading
  let initialized := record (Caller.initLookup external budget allocator source buffer request)
    (initialization external budget allocator source buffer request) ready
  record (OwnedCall.take external allocator) (taking external allocator) initialized.2

/-- The native owner and recorded token come from the same admitted prefix.
The token and its event position are derived, never supplied by the caller. -/
theorem takenPrefix_tokens (external : External σ) (budget allocator : Nat) (source : View)
    (request : Interner.Request) (constructed : World σ) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (values : List NodeId) (prepared taken : OwnedCall.State σ)
    (normalized : ArgumentSlice) (remaining : Handle) (leading : List ProtocolEvent) (other : Meaning)
    (good : Good source request.arguments constructed) (admitted : Admitted external)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory))
    (initialized : Caller.initLookup external budget allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : OwnedCall.take external allocator prepared = (.ok (), taken))
    (scope : taken.scope = ⟨some remaining, some normalized, false⟩) :
    ∃ token events, takenPrefix external budget allocator source request constructed memory leading =
      (.ok (), ⟨taken, { lookup := some token, items := remaining.values, phase := .cleanup }, events⟩) := by
  obtain ⟨commutative, decoded⟩ : ∃ commutative, Interner.Scoped.commutative request.item = .ok commutative := by
    cases decoded : Interner.Scoped.commutative request.item with
    | error error => simp only [Caller.initLookup, decoded] at initialized; cases initialized
    | ok commutative => exact ⟨commutative, rfl⟩
  obtain ⟨lookup, captured, ready⟩ := initialized_taken_recorded external budget allocator commutative source request
    constructed memory pointer values prepared taken leading other constructed.graph.read request.sequence
    good.1 good.2 allocated decoded admitted initialized transferred
  dsimp only at ready
  obtain ⟨slice, handle, locals, _, _, _, _, _, _, recorded, _⟩ := ready
  have same : handle = remaining := Option.some.inj (congrArg Local.lookup (locals.symm.trans scope))
  subst handle
  exact ⟨_, _, recorded⟩

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (source : View) (request : Interner.Request) (rows : List Storage.Cell)
    (parent : ChildTrace.TracedWorld σ ProtocolEvent → Prop)

/-- The replay ports are determined by this actual prefix, selected native
suffix and the same proper-child model used by semantic preservation. -/
def replayModel (address : Compiler.ZigAir.Memory.Address) (key : Key) (normalized : ArgumentSlice)
    (remaining : Handle) (deterministic : Bool)
    (recorded : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (token : NormalizationOwnership.State) (trailing : List ProtocolEvent)
    (seed : Interner.Primitives) (childModel : Associative.Constructors AssemblyItem.Fields.Values)
    (mismatch : Insertion.Native.Fault) : Interner.Primitives :=
  let child := ChildTrace.constructors children observations
  let middle := Caller.ProtocolTrace.Native.middle ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits child
    (ChildTrace.liftObservations observations) debug source address (input request.item debug) request key normalized deterministic recorded.native.world
  let observed := MissStream.segment ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits child debug source address
    (input request.item debug) request key normalized deterministic recorded.native.world remaining token
  let events := recorded.events ++ middle ++ observed.body ++ observed.cleanup ++ trailing
  dispatchModel (MissStream.replay seed events observed.candidate mismatch) childModel usizeBits debug

/-- One reached child model serves recorded replay and native preservation.
The actual recorded prefix selects the cursor; the suffix model is bound to
its actual candidate and resource events. Native suffix words are derived by
the existing native adapter, not included in this obligation. -/
def TakenModel (address : Compiler.ZigAir.Memory.Address) (key : Key) (normalized : ArgumentSlice)
    (remaining : Handle) (deterministic : Bool)
    (recorded : Recorded (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (model : Interner.Primitives) (trailing : List ProtocolEvent) : Prop :=
  ∀ token, recorded.tokens = { lookup := some token, items := remaining.values, phase := .cleanup } →
    ∃ (childModel : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
      (mismatch : Insertion.Native.Fault),
      let child := ChildTrace.constructors children observations
      let cursor := MissStream.childCursor recorded.events.length recorded.native.world
      ((deterministic && (request.item.kind == 1)) = true →
        ∀ rows, (projectionAt (cursorGraph cursor)
        (CallFrame safety base.allocator owner rows source request.arguments normalized address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads rows) debug
          child childModel) ∧
      MissFrames (Publication.external ops.arguments) base.allocator
        ((context (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
          owner usizeBits child debug).primitives source address (input request.item debug))
        (CallFrame safety base.allocator owner rows source request.arguments normalized address (input request.item debug) parent)
        (GraphFrame safety base.allocator owner rows parent) key normalized remaining deterministic
        (deterministic && (request.item.kind == 1)) ∧
      ((deterministic && (request.item.kind == 1)) = true →
        Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) childModel) ∧
      ((deterministic && (request.item.kind == 1)) = true →
        AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) childModel.operation) ∧
      ((deterministic && (request.item.kind == 1)) = true →
        ArithmeticShift.Constructs (AddressMask.addressMeaning env other) childModel.operation) ∧
      model = replayModel ops allocate safety owner usizeBits base growth children observations env other debug source request
        address key normalized remaining deterministic recorded token trailing seed childModel mismatch

/-- The existing parent laws and actual native prefix observations select one
joint miss witness. No complete entry result, native frame at the reached take,
word result, successful preparation or resource token is assumed at entry. -/
structure JointEntry (model : Interner.Primitives) (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (leading trailing : List ProtocolEvent) : Prop where
  retained : ∀ after, Valid after.memory → after.graph = before.graph → Retains before after → parent after
  localParent : ∀ constructed address, prepare request.item debug before = (.ok address, constructed) →
    ∀ world, parent world → parent (returnWorld before.memory.memory.nextId constructed.memory.memory.nextId world)
  taken : ∀ constructed address pointer memory values prepared taken key normalized lookup deterministic,
    prepare request.item debug before = (.ok address, constructed) →
    base.queries.atCapacity constructed.graph = false →
    Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory) →
    Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, prepared) →
    base.queries.deterministic request.item = .ok deterministic → Interner.makeKey request values = .ok key →
    (deterministic = true → constructed.graph.table key = none) →
    OwnedCall.take (Publication.external ops.arguments) base.allocator prepared = (.ok (), taken) →
    Insertion.Native.CallerInput base.allocator source address request values (input request.item debug) key constructed taken normalized lookup →
    TakenModel ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
      address key normalized lookup deterministic
      (takenPrefix (Publication.external ops.arguments) base.budget base.allocator source request constructed memory leading).2 model trailing

variable {model : Interner.Primitives} {before : ChildTrace.TracedWorld σ ProtocolEvent}
    {leading trailing : List ProtocolEvent}

attribute [local irreducible] dispatchModel MissStream.replay

/-- The derived recorded token lets the native entry select the very same
child model/cursor that is bound to replay. Its suffix words remain derived. -/
theorem JointEntry.native_frames
    (joint : JointEntry ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
      model before leading trailing)
    (good : Good source request.arguments before) (admitted : Admitted ops.arguments)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug) :
    EntryFrames safety owner usizeBits
      (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
      (ChildTrace.constructors children observations) source request debug before rows parent env other where
  retained := joint.retained
  localParent := joint.localParent
  taken := by
    intro constructed address pointer memory values prepared taken key normalized lookup deterministic
      made room allocated initialized classified keyed missed transferred entry
    have item := (prepare_success request.item debug before constructed address good.1 domain typed made).2
    have constructedGood := good_frame before constructed source request.arguments good item.valid item.memory
    obtain ⟨token, events, captured⟩ := takenPrefix_tokens (Publication.external ops.arguments) base.budget base.allocator source request
      constructed memory pointer values prepared taken normalized lookup leading other constructedGood
      (Publication.external_admitted ops.arguments admitted) allocated initialized transferred entry.origin.scope
    have selected := joint.taken constructed address pointer memory values prepared taken key normalized lookup deterministic
      made room allocated initialized classified keyed missed transferred entry
    rw [captured] at selected
    obtain ⟨childModel, seed, mismatch, coupled, frames, correct, addresses, shifts, bound⟩ := selected token rfl
    exact ⟨MissStream.childCursor events.length taken.world, childModel,
      ⟨fun selected => coupled selected rows, frames, correct, addresses, shifts⟩⟩

/-- The same reached witnesses discharge recorded induction. Original item
preparation and caller input derive the live native frame; the shared child
model is used unchanged by both the projection and its replay binding. -/
theorem JointEntry.recorded {capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    (joint : JointEntry ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
      model before leading trailing)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (admitted : Admitted ops.arguments)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (constructed : ChildTrace.TracedWorld σ ProtocolEvent) (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State)
    (made : prepare request.item debug before = (.ok address, constructed))
    (room : base.queries.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory)) :
    Caller.ProtocolTrace.Native.EntryInduction ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits
      children observations debug source address (input request.item debug) request model ⟨constructed.memory.memory.nextId, 0, 2⟩
      (start { constructed with memory := { constructed.memory with memory } } leading) trailing := by
  intro values key deterministic normalized taken _ initialized classified keyed missed transferred
  have initializedNative : Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ = (.ok values, normalized.2.native) :=
    Prod.ext initialized rfl
  have takenNative : OwnedCall.take (Publication.external ops.arguments) base.allocator normalized.2.native = (.ok (), taken.2.native) :=
    Prod.ext transferred rfl
  obtain ⟨owned, handle, entry⟩ := caller_input ops.arguments base.budget base.allocator source request debug before constructed
    address memory _ values normalized.2.native taken.2.native key ⟨facts.valid, represented⟩ domain typed admitted made allocated
    initializedNative takenNative keyed facts.live facts.unique (privateSource key)
  intro slice remaining token locals tokens
  have sameHandle : handle = remaining := Option.some.inj (congrArg Local.lookup (entry.origin.scope.symm.trans locals))
  have sameSlice : owned = slice := Option.some.inj (congrArg Local.slice (entry.origin.scope.symm.trans locals))
  subst remaining slice
  have selected := joint.taken constructed address _ memory values normalized.2.native taken.2.native key owned handle deterministic
    made room allocated initializedNative classified keyed missed takenNative entry
  have reached : TakenModel ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
      address key owned handle deterministic taken.2 model trailing := selected
  obtain ⟨childModel, seed, mismatch, coupled, frames, correct, addresses, shifts, bound⟩ := reached token tokens
  have item := (prepare_success request.item debug before constructed address facts.valid domain typed made).2
  have constructedFacts := facts.frame item.valid (by rw [item.graph]; exact facts.projected)
    (congrArg Interner.Heap.table item.graph) (congrArg Publication.Effects.keys item.effects)
    (fun id cell found _ => item.memory id cell found) (fun _ _ found => item.heap ▸ found)
  have parentTaken := joint.retained taken.2.native.world entry.origin.held.1.1 (entry.origin.graph.trans item.graph)
    ⟨entry.keys.trans (congrArg Publication.Effects.keys item.effects),
      fun id cell found => entry.origin.memory id cell (item.memory id cell found),
      fun id block found => entry.origin.registry id block (item.heap ▸ found)⟩
  have frame := CallFrame.caller entry constructedFacts (by rw [item.effects]; exact privateSource)
    (array.frame (fun _ cell found => item.memory _ cell found)) parent parentTaken
  let predicate := fun world : ChildTrace.TracedWorld σ ProtocolEvent =>
    AssemblyClone.NativeFields.Represents world.memory.memory address (input request.item debug) ∧ parent world ∧
      ArraySource source world.memory.memory
  refine ⟨childModel, seed, predicate, rows, mismatch, frame.2, frame.1, ?_, bound⟩
  intro selected suffixRows
  have same : (fun world => predicate world ∧ InputFrame safety base.allocator owner suffixRows source request.arguments owned world) =
      CallFrame safety base.allocator owner suffixRows source request.arguments owned address (input request.item debug) parent := by
    funext world
    exact propext and_comm
  rw [same]
  exact coupled selected suffixRows

attribute [local irreducible] InvocationPost EntryProjected

/-- The complete recorded item and native preservation now consume one joint
reached-miss obligation. Erasure identifies the exact same result/world; the
shared prefix determines tokens, child cursor and model binding. All ordinary
entry routes are covered without assuming successful preparation or a final
word/frame theorem. Deriving the local frame laws and recursive witnesses is
still required for production induction. -/
theorem item_joint_verified {capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    (joint : JointEntry ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
      model before leading trailing)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (admitted : Admitted ops.arguments)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = base.queries.deterministic request.item)
    (expected : Word) (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some expected)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other) :
    let ctx := context (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
      owner usizeBits (ChildTrace.constructors children observations) debug
    let ports := Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits
      (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug
    let actual := item ctx ports source request debug before leading
    EntryProjected model request before.graph leading trailing actual ∧
      InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
        before.graph (actual.1, actual.2.native) expected := by
  intro ctx ports actual
  have good : Good source request.arguments before := ⟨facts.valid, represented⟩
  constructor
  · exact item_induction_projected ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits children observations
      model debug source request before leading trailing (Dispatch.wordBaseMeaning env other) before.graph.read request.sequence
      good (Publication.external_admitted ops.arguments admitted) domain typed capacityQuery classificationQuery
      (joint.recorded ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
        facts represented privateSource array admitted domain typed)
  · have native := (joint.native_frames ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
        good admitted domain typed).native_verified ops allocate safety owner usizeBits base growth (ChildTrace.constructors children observations) env other
        facts admitted typed valid represented privateSource array domain evaluated pushes
    change InvocationPost (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent) before.graph
      (invoke ctx.external ctx.budget ctx.allocator (ctx.primitives source) ctx.queries source request debug before) expected at native
    rw [item_erases ctx ports source request debug before leading] at native
    exact native

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
