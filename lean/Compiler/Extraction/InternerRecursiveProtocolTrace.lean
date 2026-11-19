/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolTrace
import Compiler.Extraction.InternerCallerNativeProtocol
import Compiler.Extraction.InternerMissChildTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace ConstructorItem.ProtocolTrace
open Recursive Interner.InvocationTrace
open MissStream (Completion replay segment)

abbrev Captures (σ : Type) := Associative.Constructors AssemblyItem.Fields.Values (Capture (Publication.Effects σ))

/-- Every entry chooses its own original debug fields before entering the same
wrapper family. The map commutes with that choice. -/
def atDebug {m : Type → Type} (family : Debug → Associative.Constructors Debug m) : Associative.Constructors Debug m where
  operation := fun opcode values debug => (family debug).operation opcode values debug
  constant := fun value debug => (family debug).constant value debug
  materialize := fun id value debug => (family debug).materialize id value debug
  borrowedOperation := fun address opcode values debug => (family debug).borrowedOperation address opcode values debug
  localOperation := fun opcode source selected repeated first debug => (family debug).localOperation opcode source selected repeated first debug

theorem map_atDebug {m n : Type → Type} (f : m NodeId → n NodeId) (family : Debug → Associative.Constructors Debug m) :
    mapConstructors f (atDebug family) = atDebug (fun debug => mapConstructors f (family debug)) := rfl

def observe (captured : Captures σ) : ChildTrace.Observations σ ProtocolEvent :=
  mapConstructors (fun action before => (action before []).2.events) captured

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)

/-- All graph observations use the same native constructor recorder. Changing
proof instrumentation does not require another wrapper execution path. -/
def stepWith (children : Constructors (Publication.Effects σ))
    (ports : AssemblyItem.Fields.Values → View → Compiler.ZigAir.Memory.Address →
      AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects σ)) : Captures σ :=
  atDebug fun debug => ConstructorItem.ProtocolTrace.constructors
    (context (callerContext ops allocate safety owner meaning base growth) owner usizeBits children debug)
    (ports debug)

/-- Bind all graph observations to their native executors at the exact wrapper
source/item inputs. Only the proper-child observations remain parameters here. -/
def step (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent) : Captures σ :=
  stepWith ops allocate safety owner meaning base growth usizeBits children
    (Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits children observations)

attribute [local irreducible] ConstructorItem.ProtocolTrace.constructors ViewInput.constructors

theorem stepWith_erases (children : Constructors (Publication.Effects σ))
    (ports : AssemblyItem.Fields.Values → View → Compiler.ZigAir.Memory.Address →
      AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects σ))
    (leading : List ProtocolEvent) :
    mapConstructors (eraseCapture leading) (stepWith ops allocate safety owner meaning base growth usizeBits children ports) =
      NativeRecursion.step (callerContext ops allocate safety owner meaning base growth) owner usizeBits children := by
  unfold stepWith
  rw [map_atDebug]
  have equal := funext fun debug => ConstructorItem.ProtocolTrace.constructors_erases
    (context (callerContext ops allocate safety owner meaning base growth) owner usizeBits children debug)
    (ports debug) leading
  exact congrArg atDebug equal

theorem step_erases (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (leading : List ProtocolEvent) :
    mapConstructors (eraseCapture leading) (step ops allocate safety owner meaning base growth usizeBits children observations) =
      NativeRecursion.step (callerContext ops allocate safety owner meaning base growth) owner usizeBits children :=
  stepWith_erases ops allocate safety owner meaning base growth usizeBits children _ leading

theorem stepWith_prefix (children : Constructors (Publication.Effects σ))
    (ports : AssemblyItem.Fields.Values → View → Compiler.ZigAir.Memory.Address →
      AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects σ))
    (earlier leading : List ProtocolEvent) :
    mapConstructors (m := Capture (Publication.Effects σ))
      (n := fun _ => World (Publication.Effects σ) → Except Fault NodeId × Recorded (Publication.Effects σ))
      (fun action before => action before (earlier ++ leading)) (stepWith ops allocate safety owner meaning base growth usizeBits children ports) =
    mapConstructors (prefixCapture earlier leading) (stepWith ops allocate safety owner meaning base growth usizeBits children ports) := by
  unfold stepWith
  rw [map_atDebug, map_atDebug]
  exact congrArg atDebug (funext fun debug => ConstructorItem.ProtocolTrace.constructors_prefix _ _ earlier leading)

theorem step_prefix (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (earlier leading : List ProtocolEvent) :
    mapConstructors (m := Capture (Publication.Effects σ))
      (n := fun _ => World (Publication.Effects σ) → Except Fault NodeId × Recorded (Publication.Effects σ))
      (fun action before => action before (earlier ++ leading)) (step ops allocate safety owner meaning base growth usizeBits children observations) =
    mapConstructors (prefixCapture earlier leading) (step ops allocate safety owner meaning base growth usizeBits children observations) :=
  stepWith_prefix ops allocate safety owner meaning base growth usizeBits children _ earlier leading

/-- Zero depth is the same explicit unsupported result as NativeRecursion.unfold.
Each successor observes the proper child's full wrapper/caller execution; there
are no supplied event lists in this finite family. A finite observation is not
a termination theorem, scoped admission, or a word-preservation theorem. -/
def unfold : Nat → Captures σ
  | 0 => mapConstructors (fun action before leading =>
      let actual := action before
      (actual.1, start actual.2 leading)) (NativeRecursion.exhausted (σ := Publication.Effects σ))
  | depth + 1 => step ops allocate safety owner meaning base growth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold depth))

theorem unfold_erases (depth : Nat) (leading : List ProtocolEvent) :
    mapConstructors (eraseCapture leading) (unfold ops allocate safety owner meaning base growth usizeBits depth) =
      NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth := by
  cases depth with
  | zero => rfl
  | succ depth => exact step_erases ops allocate safety owner meaning base growth usizeBits _ _ leading

theorem unfold_prefix (depth : Nat) (earlier leading : List ProtocolEvent) :
    mapConstructors (m := Capture (Publication.Effects σ))
      (n := fun _ => World (Publication.Effects σ) → Except Fault NodeId × Recorded (Publication.Effects σ))
      (fun action before => action before (earlier ++ leading)) (unfold ops allocate safety owner meaning base growth usizeBits depth) =
    mapConstructors (prefixCapture earlier leading) (unfold ops allocate safety owner meaning base growth usizeBits depth) := by
  cases depth with
  | zero => rfl
  | succ depth => exact step_prefix ops allocate safety owner meaning base growth usizeBits _ _ earlier leading

/-- Consume computed recursive observations at the existing dispatcher boundary.
The event histories are now defined by actual constructor bodies, while the
native/scoped relation and live-parent frame remain induction obligations. -/
def children (depth : Nat) : Constructors (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) :=
  ChildTrace.constructors
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (observe (unfold ops allocate safety owner meaning base growth usizeBits depth))

/-- All five dispatcher callbacks record the result/world and event segment of
the very same full constructor capture at the actual input. This consumes the
wrapper erasure theorem, not just the unconditional erasure of record itself. -/
theorem children_recorded (depth : Nat) :
    children ops allocate safety owner meaning base growth usizeBits depth =
      mapConstructors (fun captured => ChildTrace.record (eraseCapture [] captured)
        (fun before => (captured before []).2.events)) (unfold ops allocate safety owner meaning base growth usizeBits depth) := by
  unfold children
  rw [← unfold_erases ops allocate safety owner meaning base growth usizeBits depth []]
  rfl

theorem children_erases (depth : Nat) :
    (Recursive.erasing (Publication.Effects.mapAllocator Prod.fst)).Constructors
      (children ops allocate safety owner meaning base growth usizeBits depth)
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth) :=
  ChildTrace.constructors_erase _ _

/-- Specialize initialized miss immediately to this computed family. The
statement retains every native/scoped/frame premise of the existing
composition theorem; no arbitrary child observation parameter remains. -/
theorem initialized_children (depth : Nat)
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)
    (request : Interner.Request) (key : Key) (deterministic commutative : Bool)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (stack : Compiler.ZigAir.Memory.State) (pointer : Compiler.ZigAir.Memory.Value)
    (values : List NodeId) (prepared called : OwnedCall.State (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (leading : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)
    (valid : Valid before.memory) (represented : Represents before.memory.memory source request.arguments)
    (allocated : Compiler.ZigAir.Memory.allocate before.memory.memory (.array 2 word) = .ok (pointer, stack))
    (decoded : Interner.Scoped.commutative request.item = .ok commutative)
    (admitted : Admitted (Publication.external outerOps.arguments))
    (initialized : Caller.initLookup (Publication.external outerOps.arguments) outerBase.budget outerBase.allocator source
      ⟨before.memory.memory.nextId, 0, 2⟩ request
      ⟨{ before with memory := { before.memory with memory := stack } }, { lookup := none }⟩ = (.ok values, prepared))
    (transferred : OwnedCall.take (Publication.external outerOps.arguments) outerBase.allocator prepared = (.ok (), called)) :
    let start := { before with memory := { before.memory with memory := stack } }
    let initialization := Caller.Initialization.capture (Publication.external outerOps.arguments) outerBase.budget outerBase.allocator
      commutative source ⟨before.memory.memory.nextId, 0, 2⟩ request.arguments start.memory
    ∃ lookup, initialization.1 = .ok (some lookup) ∧
      let handle := initialization.2.effects.handle
      let taken := Caller.Take.capture (Publication.external outerOps.arguments) outerBase.allocator lookup.origin handle prepared.world.memory
      let missLeading := leading ++ initialization.2.events.map Event.normalization ++ taken.2.events.map Event.normalization
      ∃ slice remaining, called.scope = ⟨some remaining, some slice, false⟩ ∧
        Normalization.Taken outerBase.allocator source request.arguments handle prepared.world.memory slice remaining called.world.memory ∧
        slice.items = values ∧
        request.item.eval (Folding.wordMeaning other) read values sequence =
          request.item.eval (Folding.wordMeaning other) read request.arguments sequence ∧
        let traced := children ops allocate safety owner meaning base growth usizeBits depth
        let p := MissStream.physical outerOps outerAllocate safety owner meaning outerBase outerGrowth owner usizeBits traced debug source address input
        let decision := MissStream.selected p request key slice deterministic called.world
        let middle := ChildTrace.history (MissStream.selected p request key slice deterministic (ChildTrace.restore [] (ChildTrace.erase called.world))).2
        let cursor := MissStream.childCursor missLeading.length called.world
        ∀ (model : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
          (predicate : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (originalRows : List Storage.Cell),
          predicate called.world → InputFrame safety outerBase.allocator owner originalRows source request.arguments slice called.world →
          key.arguments = values →
          (∀ rows, (projectionAt (cursorGraph cursor) (fun world => predicate world ∧
            InputFrame safety outerBase.allocator owner rows source request.arguments slice world)).SourceConstructorsAt (Nested.storageReads rows) debug traced model) →
          ∀ (trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault),
            let tailLeading := missLeading ++ middle
            let observed := segment outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits traced debug source address input
              request key slice deterministic called.world remaining taken.1.2
            let events := tailLeading ++ observed.body ++ observed.cleanup ++ trailing
            let r := resources events (.preparation .incomplete)
            let initialScope := Interner.Scoped.initScope r request ⟨{}, { before.graph with allocationCursor := leading.length }⟩
            let takeScope := Interner.Scoped.take r initialScope.2
            let actual := Interner.findCode.controlMiss (execution (Publication.external outerOps.arguments) outerBase.allocator p)
              request key deterministic called
            let logical := Interner.findCode.controlMiss
              (Interner.Scoped.execution r (dispatchModel (replay seed events observed.candidate mismatch) model usizeBits debug))
              request key deterministic takeScope.2
            let close := Caller.Close.capture (Publication.external outerOps.arguments) outerBase.allocator taken.1.2 observed.phase remaining actual.2
            Caller.Initialization.checked initialization (normalizations leading)
              (taken.2.events ++ normalizations (middle ++ observed.body ++ observed.cleanup ++ trailing)) request
              { before.graph with allocationCursor := leading.length } = .ok initialScope ∧
            Caller.Take.checked taken (normalizations leading ++ initialization.2.events)
              (normalizations (middle ++ observed.body ++ observed.cleanup ++ trailing)) lookup values initialScope.2.heap = .ok takeScope ∧
            takeScope.1 = .ok () ∧
            Completion outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits traced debug source address input
              request key slice deterministic called.world remaining taken.1.2 request.arguments tailLeading trailing mismatch ∧
            ChildTrace.history decision.2 = ChildTrace.history called.world ++ middle ∧
            (ordinary decision.1 = true →
              actual.1 = logical.1.mapError Fault.language ∧
              logical.2 = ⟨⟨some taken.1.2, remaining.values, observed.phase⟩,
                { actual.2.world.graph with allocationCursor := (tailLeading ++ observed.body).length }⟩ ∧
              (ordinary actual.1 = true →
                Caller.Close.checked close (normalizations (tailLeading ++ observed.body)) (normalizations trailing)
                  taken.1.2 observed.phase remaining.values logical.2.heap = .ok (Interner.Scoped.close r logical.2))) :=
  MissStream.initialized_recorded_children outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (observe (unfold ops allocate safety owner meaning base growth usizeBits depth))
    debug source address input request key deterministic commutative before stack pointer values prepared called leading other read sequence
    valid represented allocated decoded admitted initialized transferred

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
