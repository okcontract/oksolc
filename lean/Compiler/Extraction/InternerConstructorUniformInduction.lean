/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorEnclosingInduction
import Compiler.Extraction.InternerUniformChildren

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
/-- The actual joint item step now constructs its shared child model from
native induction data. Admission, ordinary observational agreement, live-frame
preservation and native word laws remain explicit compiler obligations; no
logical child constructor, its soundness, or complete item result is assumed. -/
theorem item_enclosing_replay_uniform {capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
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
      ∃ domains : Uniform.Domains (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)) AssemblyItem.Fields.Values,
        (site.deterministic && (request.item.kind == 1)) = true →
        let observe := cursorGraph (MissStream.childCursor (sitePrefix ops base source request leading site).2.events.length
          (sitePrefix ops base source request leading site).2.native.world)
        Uniform.Agreement observe domains child ∧
        Uniform.Words observe (Dispatch.wordDispatchMeaning env other) domains child ∧
        ∀ childRows,
          let frame := CallFrame safety base.allocator owner childRows source request.arguments site.normalized
            site.address (input request.item debug) parent
          Uniform.SourceAdmission domains debug (Nested.storageReads childRows) frame ∧
          (keeping frame).SourceConstructorsAt (Nested.storageReads childRows) debug child child) :
    ∃ model : Interner.Primitives,
      model.atCapacity = seed.atCapacity ∧ model.deterministic = seed.deterministic ∧
      JointPost model request before.graph leading trailing (Dispatch.wordDispatchMeaning env other)
        (GraphFrame safety base.allocator owner rows parent)
        (item (jointContext ops allocate safety owner usizeBits base growth children observations env other debug)
          (jointPorts ops allocate safety owner usizeBits base growth children observations env other debug)
          source request debug before leading) expected := by
  apply item_enclosing_replay_joint ops allocate safety owner usizeBits base growth children observations env other debug source request rows parent
    leading trailing before seed mismatch stack initial facts represented privateSource array admitted domain typed capacityQuery classificationQuery
    expected valid evaluated pushes _
  intro site reached
  obtain ⟨domains, native⟩ := proper site reached
  exact Uniform.proper _ domains child env other debug _ (fun childRows => Nested.storageReads childRows)
    (fun childRows => CallFrame safety base.allocator owner childRows source request.arguments site.normalized
      site.address (input request.item debug) parent) native

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace
