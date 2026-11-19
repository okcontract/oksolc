/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointEntryReplay
import Compiler.Extraction.InternerTakenSite
import Compiler.Extraction.InternerCheckpointHistory
import Compiler.Extraction.InternerNativeFrameEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.CheckpointEntry
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem ConstructorItem.NativeRecursion Recursive

/-- Actual checkpoint-prefix guards supply the existing reached-site admission.
The native input and normalized owner are derived by caller_input. -/
theorem AtMiss.reached
    (ops : Insertion.Operations σ) (base : PairInput.Context (Publication.Effects σ))
    (external : base.external = Publication.external ops.arguments)
    (safety : Bool) (owner capacity : Nat) (data : Compiler.ZigAir.Memory.Address) (rows : List Storage.Cell)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World (Publication.Effects σ))
    (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State)
    (pointer : Compiler.ZigAir.Memory.Value) (leading : List ProtocolEvent)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (typed : AssemblyItem.Initializers.DebugTyped debug) (admitted : Admitted ops.arguments)
    (made : ConstructorItem.prepare request.item debug before = (.ok address, constructed))
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory)) :
    AtMiss ops base source request
      (fun key deterministic taken => ∃ site : ConstructorItem.ProtocolTrace.TakenSite σ,
        site.Reached base source request debug before ∧ site.key = key ∧ site.deterministic = deterministic ∧ site.taken = taken.native)
      ⟨constructed.memory.memory.nextId, 0, 2⟩
      (ConstructorItem.ProtocolTrace.start { constructed with memory := { constructed.memory with memory } } leading) := by
  intro values key deterministic normalized taken room initialized classified keyed absent transferred
  have nativeInitialized : Caller.initLookup (Publication.external ops.arguments) base.budget base.allocator source
      ⟨constructed.memory.memory.nextId, 0, 2⟩ request
      ⟨{ constructed with memory := { constructed.memory with memory } }, { lookup := none }⟩ =
        (.ok values, normalized.2.native) := Prod.ext initialized rfl
  have nativeTaken : OwnedCall.take (Publication.external ops.arguments) base.allocator normalized.2.native =
      (.ok (), taken.2.native) := Prod.ext transferred rfl
  obtain ⟨slice, handle, entry⟩ := ConstructorItem.caller_input ops.arguments base.budget base.allocator source request debug
    before constructed address memory pointer values normalized.2.native taken.2.native key ⟨facts.valid, represented⟩ domain typed admitted
    made allocated nativeInitialized nativeTaken keyed facts.live facts.unique (privateSource key)
  let site : ConstructorItem.ProtocolTrace.TakenSite σ :=
    ⟨constructed, address, pointer, memory, values, normalized.2.native, taken.2.native, key, slice, handle, deterministic⟩
  refine ⟨site, ⟨made, room, allocated, ?_, classified, keyed, absent, ?_, entry⟩, rfl, rfl, rfl⟩
  · simpa only [external] using nativeInitialized
  · simpa only [external] using nativeTaken

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native.CheckpointEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace NativeRecursion Recursive

theorem retire_result (mark : Nat) (ran : Except Fault NodeId × Recorded σ) :
    (retire mark ran).1 = ran.1 := by
  unfold retire TemporaryArguments.unwind
  split <;> rfl

/-- The original item/scratch guards and actual init/take observations reduce
one constructor item to its existing recorded miss and both return frames. -/
theorem item_taken (base : PairInput.Context σ)
    (ports : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations σ)
    (source : View) (request : Interner.Request) (debug : AssemblyItem.Fields.Values)
    (before constructed : World σ) (address : Compiler.ZigAir.Memory.Address)
    (pointer : Compiler.ZigAir.Memory.Value) (memory : Compiler.ZigAir.Memory.State)
    (leading : List ProtocolEvent) (values : List NodeId) (key : Key) (deterministic : Bool)
    (made : ConstructorItem.prepare request.item debug before = (.ok address, constructed))
    (room : base.queries.atCapacity constructed.graph = false)
    (allocated : Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) = .ok (pointer, memory)) :
    let buffer : View := ⟨constructed.memory.memory.nextId, 0, 2⟩
    let initial := start { constructed with memory := { constructed.memory with memory } } leading
    let normalized := record (Caller.initLookup base.external base.budget base.allocator source buffer request)
      (initialization base.external base.budget base.allocator source buffer request) initial
    let taken := record (OwnedCall.take base.external base.allocator) (taking base.external base.allocator) normalized.2
    let p := base.primitives source address (input request.item debug)
    let observations := ports source address (input request.item debug)
    let body := missBody base.external base.budget base.allocator p base.queries observations source buffer request key deterministic taken.2
    normalized.1 = .ok values → base.queries.deterministic request.item = .ok deterministic →
    Interner.makeKey request values = .ok key →
    (deterministic = true → constructed.graph.table key = none) → taken.1 = .ok () →
    item base ports source request debug before leading =
      retire before.memory.memory.nextId (retire constructed.memory.memory.nextId
        (Caller.ProtocolTrace.finish base.external base.allocator body.1 body.2)) := by
  intro buffer initial normalized taken p observations body initialized classified keyed absent transferred
  have reduced := findBody_taken base.external base.budget base.allocator p base.queries observations source buffer request key deterministic values
    initial normalized.2 taken.2 room (Prod.ext initialized rfl) classified keyed absent (Prod.ext transferred rfl)
  simp only [item, made, frame, room, Bool.false_eq_true, ↓reduceIte, allocated]
  simp only [Caller.ProtocolTrace.find, Caller.ProtocolTrace.invoke]
  exact congrArg (fun ran : Except Fault NodeId × Recorded σ =>
    retire before.memory.memory.nextId (retire constructed.memory.memory.nextId
      (Caller.ProtocolTrace.finish base.external base.allocator ran.1 ran.2))) reduced

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage

theorem finish_body_ordinary (external : External σ) (allocator : Nat) (result : Except Fault α) (before : Recorded σ)
    (completed : ordinary (finish external allocator result before).1 = true) : ordinary result = true := by
  cases branch : ordinary result with
  | false => simp only [finish, branch, Bool.false_eq_true, ↓reduceIte] at completed
  | true => rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

theorem callFrame_input (safety : Bool) (allocator owner : Nat) (rows reachedRows : List Storage.Cell)
    (source : View) (values : List NodeId) (normalized : ArgumentSlice)
    (address : Compiler.ZigAir.Memory.Address) (native : AssemblyClone.NativeFields.ItemValue)
    (parent : World (Publication.Effects σ) → Prop) :
    (fun world => CallFrame safety allocator owner rows source values normalized address native parent world ∧
      InputFrame safety allocator owner reachedRows source values normalized world) =
    CallFrame safety allocator owner reachedRows source values normalized address native
      (CallFrame safety allocator owner rows source values normalized address native parent) := by
  funext world
  apply propext
  constructor
  · rintro ⟨frame, inputs⟩
    exact ⟨inputs, frame.2.1, frame, frame.2.2.2⟩
  · intro frame
    exact ⟨frame.parent, frame.1⟩

/-- Pull an existing enclosing-frame witness back through allocator-only instrumentation. -/
theorem Enclosing.mapAllocator (project : σ → τ) {safety : Bool} {allocator owner : Nat}
    {parent : World (Publication.Effects τ) → Prop} (stack : Enclosing safety allocator owner parent) :
    Enclosing safety allocator owner (fun world : World (Publication.Effects σ) =>
      parent (world.mapEffects (Publication.Effects.mapAllocator project))) := by
  induction stack with
  | root => exact .root
  | @call rows source values normalized address native parent outer ih =>
    have same : (fun world : World (Publication.Effects σ) =>
        CallFrame safety allocator owner rows source values normalized address native parent
          (world.mapEffects (Publication.Effects.mapAllocator project))) =
        CallFrame safety allocator owner rows source values normalized address native
          (fun world => parent (world.mapEffects (Publication.Effects.mapAllocator project))) := by
      funext world
      exact propext (CallFrame.mapAllocator_iff project)
    rw [same]
    exact .call ih

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Recursive
open Caller.ProtocolTrace (ProtocolEvent)

theorem Enclosing.traced_selected_frame (depth : Nat)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (request : Interner.Request) (key : Key) (slice : ArgumentSlice)
    (deterministic : Bool) (before : ChildTrace.TracedWorld σ ProtocolEvent)
    (values : List NodeId) (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (stack : Enclosing safety base.allocator owner parent)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (frame : CallFrame safety base.allocator owner rows source values slice address input parent (ChildTrace.erase before)) :
    let traced := AllocationTrace.children ops allocate safety owner meaning base growth usizeBits depth
    let p := Caller.ProtocolTrace.Native.physical outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      traced debug source address input
    let decision := MissStream.selected p request key slice deterministic before
    ordinary decision.1 = true →
      CallFrame safety base.allocator owner rows source values slice address input parent (ChildTrace.erase decision.2) := by
  intro traced p decision
  let children := unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth
  let observations := ProtocolTrace.observe (AllocationTrace.unfold ops allocate safety owner meaning base growth usizeBits depth)
  let nativeP := Caller.ProtocolTrace.Native.physical ops allocate safety owner meaning base growth usizeBits children debug source address input
  have mapped : (decision.1, ChildTrace.erase decision.2) =
      MissStream.selected nativeP request key slice deterministic (ChildTrace.erase before) := by
    dsimp only [decision, MissStream.selected]
    split
    · exact (dispatcher_erases (Publication.Effects.mapAllocator Prod.fst)
        (callerContext outerOps outerAllocate safety owner meaning outerBase outerGrowth)
        (callerContext ops allocate safety owner meaning base growth) owner usizeBits
        (ChildTrace.constructors_erase children observations) debug source address input key slice before).symm
    · rfl
  have kept := stack.unfold_selected_frame ops allocate safety owner usizeBits base growth meaning debug depth
    rows source values slice address input parent admitted typed (ChildTrace.erase before) frame request key deterministic
  change ordinary (MissStream.selected nativeP request key slice deterministic (ChildTrace.erase before)).1 = true →
    CallFrame safety base.allocator owner rows source values slice address input parent
      (MissStream.selected nativeP request key slice deterministic (ChildTrace.erase before)).2 at kept
  rw [← mapped] at kept
  exact kept

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
