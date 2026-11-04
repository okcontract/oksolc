/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerProtocolTrace
import Compiler.Extraction.InternerInvocationChildTrace
import Compiler.Extraction.InternerMissInvocation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open ConstructorItem.NativeRecursion Interner.InvocationTrace

/-- Use the existing dispatcher snapshot theorem: native reads are unchanged,
while proper-child calls append their observations in source order. -/
def dispatch (owner usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (debug : AssemblyItem.Fields.Values)
    (key : Key) (slice : ArgumentSlice) (before : World (Publication.Effects σ)) :=
  (Dispatch.simplifyWithInputs (NativeReads.reads owner before.memory.memory)
    (ChildTrace.constructors children observations) usizeBits key.instruction key.arguments debug operand slice.address)
    (ChildTrace.restore [] before)

theorem dispatch_erases (base : ConstructorItem.PairInput.Context (Publication.Effects σ)) (owner usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (slice : ArgumentSlice) (before : World (Publication.Effects σ)) :
    let captured := dispatch owner usizeBits children observations debug key slice before
    ((context base owner usizeBits children debug).primitives source address input).simplify key slice before =
      (captured.1, ChildTrace.erase captured.2) := by
  rw [dispatcher_snapshot]
  exact (Recursive.erasing (Publication.Effects.mapAllocator Prod.fst)).simplify_operands
    (ChildTrace.constructors_erase children observations) ⟨operand_erases _⟩
    (NativeReads.reads owner before.memory.memory) usizeBits key.instruction key.arguments debug slice.address
    (ChildTrace.restore [] before)

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : ConstructorItem.PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue)

/-- Native admission/count failures precede the corresponding protocol call.
No default rows or invented publication probe are emitted on those paths. The
three graph observations now come from actual executors; child observations
remain the recursive obligation. -/
def graphObservations : GraphObservations (Publication.Effects σ) where
  simplify := fun key slice before => ChildTrace.history (dispatch owner usizeBits children observations debug key slice before).2
  publish := fun key slice _ before =>
    match Publication.admit base.allocator source key slice before with
    | .error _ => []
    | .ok () => [.publicationProbe key (ops.probe key (Publication.forget before.memory)).1]
  insert := fun key slice deterministic before =>
    match before.graph.representatives with
    | none => []
    | some cells => match Insertion.Native.checkedCount before.memory.memory owner cells with
      | .error _ => []
      | .ok _ => (Insertion.Native.recordExecution ops allocate safety base.allocator owner source address meaning input
          key slice deterministic cells before growth []).2.events.map Event.insertion

abbrev physical := MissStream.physical ops allocate safety owner meaning base growth owner usizeBits children debug source address input

/-- Full source caller observation from native local operations and native graph
ports. This supplies a computed child segment, not an admitted host transcript.
It does not yet prove scoped admission or preservation for every child body. -/
theorem find_segment (buffer : View) (request : Interner.Request) (before : World (Publication.Effects σ))
    (leading : List ProtocolEvent) :
    let p := physical ops allocate safety owner meaning base growth usizeBits children debug source address input
    let ports := graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    let captured := find (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer request
      ⟨⟨before, { lookup := none }⟩, {}, []⟩
    Caller.find (Publication.external ops.arguments) base.budget base.allocator p base.queries source buffer request before =
      (captured.1, captured.2.native) ∧
    find (Publication.external ops.arguments) base.budget base.allocator p base.queries ports source buffer request
      ⟨⟨before, { lookup := none }⟩, {}, leading⟩ = (captured.1, prepend leading captured.2) :=
  ProtocolTrace.find_segment _ _ _ _ _ _ _ _ _ _ _

/-- Expose the exact existing insertion recorder on an admitted native header.
The caller cannot substitute rows or emit insertion events before this read. -/
theorem insertion_events (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (cells : List Storage.Cell) (backing : Compiler.ZigAir.Memory.Address)
    (rows : before.graph.representatives = some cells)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType backing cells.length)) :
    (graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input).insert
      key slice deterministic before =
      (Insertion.Native.recordExecution ops allocate safety base.allocator owner source address meaning input
        key slice deterministic cells before growth []).2.events.map Event.insertion := by
  simp only [graphObservations, rows, Insertion.Native.checkedCount_read _ _ _ backing header]

theorem publication_rejected (key : Key) (slice : ArgumentSlice) (id : NodeId)
    (before : World (Publication.Effects σ)) (reason : Publication.Rejection)
    (rejected : Publication.admit base.allocator source key slice before = .error reason) :
    (graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input).publish
      key slice id before = [] ∧
    (physical ops allocate safety owner meaning base growth usizeBits children debug source address input).publish key slice id before =
      (.error (.language .safetyFault), before) := by
  simp only [graphObservations, rejected, physical, MissStream.physical, context_publishes, Publication.publish]
  exact ⟨trivial, trivial⟩

theorem publication_events (key : Key) (slice : ArgumentSlice) (id : NodeId)
    (before : World (Publication.Effects σ))
    (admitted : Publication.admit base.allocator source key slice before = .ok ()) :
    (graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input).publish
      key slice id before = [.publicationProbe key (ops.probe key (Publication.forget before.memory)).1] := by
  simp only [graphObservations, admitted]

theorem insertion_rejected (key : Key) (slice : ArgumentSlice) (deterministic : Bool)
    (before : World (Publication.Effects σ))
    (rejected : before.graph.representatives = none ∨ ∃ cells reason,
      before.graph.representatives = some cells ∧ Insertion.Native.checkedCount before.memory.memory owner cells = .error reason) :
    (graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input).insert
      key slice deterministic before = [] ∧
    (physical ops allocate safety owner meaning base growth usizeBits children debug source address input).insert key slice deterministic before =
      (.error (.language .safetyFault), before) := by
  rcases rejected with missing | ⟨cells, reason, rows, rejected⟩
  · simp only [graphObservations, missing, physical, MissStream.physical, context_inserts, Insertion.Native.insert]
    exact ⟨trivial, trivial⟩
  · simp only [graphObservations, rows, rejected, physical, MissStream.physical, context_inserts, Insertion.Native.insert]
    exact ⟨trivial, Insertion.Native.body_rejected _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rejected⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller.ProtocolTrace.Native
