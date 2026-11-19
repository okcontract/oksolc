/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorJointInduction

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

/-- Recorded correspondence and native preservation refer to the same complete
capture, including its caller scope. This is a conclusion, not an entry law. -/
def JointPost (model : Interner.Primitives) (request : Interner.Request) (before : Interner.Heap)
    (leading trailing : List ProtocolEvent) (meaning : Meaning) (frame : World σ → Prop)
    (actual : Except Fault NodeId × Recorded σ) (expected : Word) : Prop :=
  EntryProjected model request before leading trailing actual ∧
    InvocationPost meaning frame before (actual.1, actual.2.native) expected

theorem JointPost.rejected (model : Interner.Primitives) (request : Interner.Request) (before : Interner.Heap)
    (leading trailing : List ProtocolEvent) (meaning : Meaning) (frame : World σ → Prop)
    (actual : Except Fault NodeId × Recorded σ) (expected : Word) (rejected : ordinary actual.1 = false) :
    JointPost model request before leading trailing meaning frame actual expected := by
  constructor <;> intro completed <;> rw [rejected] at completed <;> cases completed

/-- The original ordinary unwinder supplies native frame/word preservation;
its scoped observation and internal caller closure are retained together. -/
theorem JointPost.retire {model : Interner.Primitives} {request : Interner.Request} {before : Interner.Heap}
    {leading trailing : List ProtocolEvent} {meaning : Meaning} {safety : Bool} {owner : Nat}
    {base : PairInput.Context (Publication.Effects σ)}
    {rows : List Storage.Cell} {parent : World (Publication.Effects σ) → Prop}
    {actual : Except Fault NodeId × Recorded (Publication.Effects σ)} {expected : Word}
    (post : JointPost model request before leading trailing meaning (GraphFrame safety base.allocator owner rows parent) actual expected)
    (mark : Nat) (older : owner < mark)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup mark world.memory.memory } }) :
    JointPost model request before leading trailing meaning (GraphFrame safety base.allocator owner rows parent)
      (ProtocolTrace.retire mark actual) expected := by
  refine ⟨EntryProjected.of_outcome (retire_outcome mark actual) post.1, ?_⟩
  rw [retire_native]
  by_cases completed : ordinary actual.1 = true
  · rw [if_pos completed]
    have returned := post.2.unwind (base := base) mark older localParent
    simp only [TemporaryArguments.unwind, completed, ↓reduceIte] at returned
    exact fun _ => ⟨(post.2 completed).1, returned completed⟩
  · rw [if_neg completed]
    exact post.2

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner usizeBits : Nat)
    (base : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (env : AddressMask.Environment) (other : Meaning) (debug : AssemblyItem.Fields.Values)
    (model : Interner.Primitives) (source : View) (request : Interner.Request)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (rows : List Storage.Cell)
    (parent : ChildTrace.TracedWorld σ ProtocolEvent → Prop) (leading trailing : List ProtocolEvent)

abbrev jointContext := context (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth)
  owner usizeBits (ChildTrace.constructors children observations) debug

abbrev jointPorts := Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner
  (Dispatch.wordDispatchMeaning env other) base growth usizeBits (ChildTrace.constructors children observations)
  (ChildTrace.liftObservations observations) debug

/-- Actual argument preparation supplies the same graph and private source to
the joint item proof. The entry graph and stream position remain the caller's. -/
theorem prepared_item_joint {prepared : ChildTrace.TracedWorld σ ProtocolEvent} {capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address}
    (ready : Arguments.Prepared request.arguments before source prepared)
    (joint : JointEntry ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
      model prepared leading trailing)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (admitted : Admitted ops.arguments)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = base.queries.deterministic request.item)
    (expected : Word) (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some expected)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other) :
    JointPost model request before.graph leading trailing (Dispatch.wordDispatchMeaning env other)
      (GraphFrame safety base.allocator owner rows parent)
      (item (jointContext ops allocate safety owner usizeBits base growth children observations env other debug)
        (jointPorts ops allocate safety owner usizeBits base growth children observations env other debug)
        source request debug prepared leading) expected := by
  obtain ⟨native, privateSource⟩ := prepared_input_frame ready facts
  have post := item_joint_verified ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
    joint native ready.good.2 privateSource ready.arraySource admitted domain typed (by rw [ready.graph]; exact capacityQuery) classificationQuery
    expected (ready.graph.symm ▸ valid) (ready.graph.symm ▸ evaluated) pushes
  simpa only [JointPost, ready.graph] using post

/-- Literal allocation and named-local copy share this entire constructor
composition. The executed producer supplies its view and reached state; the
original optional retirement consumes the same joint item result. -/
theorem prepared_constructor_joint {capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    (producer : GraphAction (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) View)
    (action : Capture (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) NodeId) (retiring : Bool)
    (forwarded : action before leading = match producer before with
      | (.error fault, reached) => (.error fault, start reached leading)
      | (.ok source, prepared) =>
        let called := item (jointContext ops allocate safety owner usizeBits base growth children observations env other debug)
          (jointPorts ops allocate safety owner usizeBits base growth children observations env other debug)
          source request debug prepared leading
        if retiring then retire before.memory.memory.nextId called else called)
    (ready : ∀ source prepared, producer before = (.ok source, prepared) → Arguments.Prepared request.arguments before source prepared)
    (rejected : ∀ fault reached, producer before = (.error fault, reached) → ordinary (.error fault : Except Fault NodeId) = false)
    (joint : ∀ source prepared, producer before = (.ok source, prepared) → Arguments.Prepared request.arguments before source prepared →
      JointEntry ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
        model prepared leading trailing)
    (facts : NativeGraph.Facts safety base.allocator owner data capacity before rows)
    (admitted : Admitted ops.arguments)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = base.queries.deterministic request.item)
    (expected : Word) (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (evaluated : request.item.eval (Dispatch.wordDispatchMeaning env other) before.graph.read request.arguments request.sequence = some expected)
    (pushes : request.item.kind = 2#32 → Insertion.Native.PushValues other)
    (localParent : retiring = true → ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    JointPost model request before.graph leading trailing (Dispatch.wordDispatchMeaning env other)
      (GraphFrame safety base.allocator owner rows parent) (action before leading) expected := by
  cases ran : producer before with
  | mk result prepared =>
    cases result with
    | error fault =>
      rw [show action before leading = (.error fault, start prepared leading) from by simpa only [ran] using forwarded]
      exact JointPost.rejected _ _ _ _ _ _ _ _ _ (rejected fault prepared ran)
    | ok source =>
      have input := ready source prepared ran
      have post := prepared_item_joint ops allocate safety owner usizeBits base growth children observations env other debug model source request
        before rows parent leading trailing input (joint source prepared ran input) facts admitted domain typed capacityQuery classificationQuery
        expected valid evaluated pushes
      rw [show action before leading = _ from by simpa only [ran] using forwarded]
      split
      · rename_i retiringNow
        obtain ⟨cell, found, _⟩ := facts.ownerLive
        have older := (Compiler.ZigAir.Memory.valid_lookup _ _ _ facts.valid.memory found).1
        exact post.retire (base := base) before.memory.memory.nextId older (localParent retiringNow)
      · exact post

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
