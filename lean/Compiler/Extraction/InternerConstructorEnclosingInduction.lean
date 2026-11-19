/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorReplayChoice
import Compiler.Extraction.InternerEnclosingNativeMiss

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (source : View) (request : Interner.Request) (rows : List Storage.Cell)
    (parent : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (leading trailing : List ProtocolEvent)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (seed : Interner.Primitives) (mismatch : Insertion.Native.Fault)

local notation "nativeBase" => callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth
local notation "child" => ChildTrace.constructors children observations

include mismatch in
/-- The joint item theorem with a concrete finite chain of enclosing native
calls. Retained-parent, local return, publication and child-failure cleanup laws
are derived, as are capacity and preparation refusal in both ownership modes
and backing refusal in both modes. First/spare/no-remap publication and its refusal derive all enclosing
frames from the source provenance carried by the call frame. Only initial array
provenance and proper-child correspondence/words remain explicit. Source coverage
now derives every ordinary insertion frame for the admitted item domain. -/
theorem item_enclosing_replay_joint {capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    (stack : Enclosing safety base.allocator owner parent) (initial : parent before)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (admitted : Admitted ops.arguments)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : seed.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
    (classificationQuery : seed.deterministic request.item = base.queries.deterministic request.item)
    (expected : Word) (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some expected)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other)
    (proper : ∀ site : TakenSite (ChildTrace.Recorded σ ProtocolEvent), site.Reached nativeBase source request debug before →
      ∃ childModel,
        ((site.deterministic && (request.item.kind == 1)) = true → ∀ childRows,
          (projectionAt (cursorGraph (MissStream.childCursor (sitePrefix ops base source request leading site).2.events.length
            (sitePrefix ops base source request leading site).2.native.world))
            (CallFrame safety base.allocator owner childRows source request.arguments site.normalized site.address (input request.item debug) parent)).SourceConstructorsAt (Nested.storageReads childRows) debug
              child childModel) ∧
        ((site.deterministic && (request.item.kind == 1)) = true →
          Associative.ConstructorSound (Dispatch.wordBaseMeaning env other) childModel) ∧
        ((site.deterministic && (request.item.kind == 1)) = true →
          AddressMask.Constructs env (ArithmeticShift.shiftMeaning other) childModel.operation) ∧
        ((site.deterministic && (request.item.kind == 1)) = true →
          ArithmeticShift.Constructs (AddressMask.addressMeaning env other) childModel.operation)) :
    ∃ model : Interner.Primitives,
      model.atCapacity = seed.atCapacity ∧ model.deterministic = seed.deterministic ∧
      JointPost model request before.graph leading trailing (Dispatch.wordDispatchMeaning env other)
        (GraphFrame safety base.allocator owner rows parent)
        (item (jointContext ops allocate safety owner usizeBits base growth children observations env other debug)
          (jointPorts ops allocate safety owner usizeBits base growth children observations env other debug)
          source request debug before leading) expected := by
  have retained : ∀ after, Valid after.memory → after.graph = before.graph → Retains before after → parent after :=
    fun _ valid graph kept => stack.retained initial valid graph kept
  have localParent : ∀ constructed address, prepare request.item debug before = (.ok address, constructed) →
      ∀ world, parent world → parent (returnWorld before.memory.memory.nextId constructed.memory.memory.nextId world) := by
    intro constructed address made
    have prepared := (prepare_success request.item debug before constructed address facts.valid domain typed made).2
    exact stack.locals initial _ _ (Nat.le_refl _) (by rw [prepared.nextId]; omega)
  refine item_replay_joint ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
    leading trailing before seed mismatch retained localParent ?_ facts represented privateSource array admitted domain typed
    capacityQuery classificationQuery expected valid evaluated pushes
  intro site reached
  obtain ⟨childModel, coupled, correct, addresses, shifts⟩ := proper site reached
  have prepared := (prepare_success request.item debug before site.constructed site.address facts.valid domain typed reached.made).2
  have parentConstructed := stack.retained initial prepared.valid prepared.graph
    ⟨congrArg Publication.Effects.keys prepared.effects, prepared.memory, fun _ _ found => prepared.heap ▸ found⟩
  have frames := stack.native_miss_frames parentConstructed reached.input.origin rows site.address (input request.item debug)
    ops allocate growth (Dispatch.wordDispatchMeaning env other)
    ((context nativeBase owner usizeBits child debug).primitives source site.address (input request.item debug))
    rfl rfl site.key site.deterministic (site.deterministic && (request.item.kind == 1)) admitted
    reached.input.publication.aligned domain
  exact ⟨childModel, coupled, ⟨fun selected => coupled selected rows, frames, correct, addresses, shifts⟩⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
