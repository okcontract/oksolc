/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAllocationReplay
import Compiler.Extraction.InternerNativeAllocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace (ProtocolEvent)
open Interner.InvocationTrace

/-- Consume only the reached insertion checkpoint. A constructor entry or
allocation decision cannot stand in for this observation. -/
def insertionRead (stream : List ProtocolEvent) : Interner.Action (Nat × Nat) := fun before =>
  match stream[before.allocationCursor]? with
  | some (.nativeInsertion id address) => (.ok (id, address), { before with allocationCursor := before.allocationCursor + 1 })
  | _ => (.error .safetyFault, { before with allocationCursor := stream.length + 1 })

/-- One model across native inputs. Its allocation identity is read from the
fixed stream at the reached cursor, not supplied from a completed native call. -/
def insertionReplay (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice)
    (meaning : Meaning) (key : Key) (deterministic : Bool) (stream : List ProtocolEvent)
    (mismatch : Insertion.Native.Fault) : Interner.Action NodeId := do
  let ids ← insertionRead stream
  Insertion.Native.allocationReplay input key normalized meaning deterministic ids.1 (insertions stream) mismatch

theorem insertion_read (before : World σ) (leading trailing : List ProtocolEvent) :
    insertionRead (leading ++ insertionEntry before :: trailing) { before.graph with allocationCursor := leading.length } =
      (.ok (before.memory.memory.nextId, before.memory.memory.nextAddress),
        { before.graph with allocationCursor := leading.length + 1 }) := by
  simp only [insertionRead, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, insertionEntry]

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator owner : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))

/-- The actual insertion replay consumes its reached checkpoint and then the
existing allocation/publication/cleanup transcript. Success and ordinary OOM
share the same model; no allocation-identity equality is a caller premise. -/
theorem insertion_replayed (mismatch : Insertion.Native.Fault) (leading trailing : List ProtocolEvent)
    (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells)
    (initial : Valid before.memory) (live : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (admitted : Admitted ops.arguments) :
    let captured := Insertion.Native.recordExecution ops allocate safety allocator owner source address meaning input key normalized deterministic cells before growth []
    let stream := leading ++ insertionEntry before :: (captured.2.events.map Event.insertion ++ trailing)
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning input key normalized deterministic growth before
    let logical := insertionReplay input normalized meaning key deterministic stream mismatch
      { before.graph with allocationCursor := leading.length }
    ordinary actual.1 = true →
      (actual.1, { actual.2.graph with allocationCursor := leading.length + 1 + captured.2.events.length }) =
        (logical.1.mapError Fault.language, logical.2) := by
  intro captured stream actual logical completed
  have projected := Insertion.Native.insert_allocation_replayed ops allocate safety allocator owner source address meaning input key normalized
    deterministic cells before growth mismatch (insertions (leading ++ [insertionEntry before])) (insertions trailing)
    backing header rows initial live represented admitted completed
  have read := insertion_read before leading (captured.2.events.map Event.insertion ++ trailing)
  have model : logical = Insertion.Native.allocationReplay input key normalized meaning deterministic before.memory.memory.nextId
      (insertions stream) mismatch { before.graph with allocationCursor := leading.length + 1 } := by
    dsimp only [logical, insertionReplay, Bind.bind, Effect.bind]
    rw [read]
  rw [model]
  have streamEq : stream = (leading ++ [insertionEntry before]) ++ (captured.2.events.map Event.insertion ++ trailing) := by
    simp only [stream, List.append_assoc, List.singleton_append]
  have decoded : insertions stream = insertions (leading ++ [insertionEntry before]) ++ captured.2.events ++ insertions trailing := by
    simp only [streamEq, insertions_append, insertions_embed, List.append_assoc]
  rw [decoded]
  simp only [insertions_length, List.length_append, List.length_singleton] at projected
  exact Prod.ext projected.1 projected.2.1.symm

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.AllocationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace (ProtocolEvent)
open Interner.InvocationTrace AllocationTrace

/-- The real caller frame and actual insertion-port observation supply the
checkpoint replay. Its stream fixes the reached allocation identity, even when
initialization and proper children have allocated since constructor entry. -/
theorem CallFrame.insertion_checkpoint_stream
    {safety : Bool} {owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {input : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before : World (Publication.Effects σ)}
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (debug : AssemblyItem.Fields.Values)
    (frame : CallFrame safety base.allocator owner rows source values normalized address input parent before)
    (meaning : Meaning) (key : Key) (deterministic : Bool) (mismatch : Insertion.Native.Fault)
    (leading stream : List ProtocolEvent) (admitted : Admitted ops.arguments)
    (inside : leading ++ (graphObservations ops allocate safety owner meaning base growth usizeBits children observations
      debug source address input).insert key normalized deterministic before <+: stream) :
    let observed := (graphObservations ops allocate safety owner meaning base growth usizeBits children observations
      debug source address input).insert key normalized deterministic before
    let actual := Insertion.Native.insert ops allocate safety base.allocator owner source address meaning input key normalized deterministic growth before
    let logical := insertionReplay input normalized meaning key deterministic stream mismatch
      { before.graph with allocationCursor := leading.length }
    ordinary actual.1 = true →
      (actual.1, { actual.2.graph with allocationCursor := leading.length + observed.length }) =
        (logical.1.mapError Fault.language, logical.2) := by
  obtain ⟨added, data, capacity, facts, _, _⟩ := frame.1.1
  have exactRows : before.graph.representatives = some (before.graph.representatives.getD []) := by
    rw [facts.projected]; rfl
  have header : readItems before.memory.memory (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType data (before.graph.representatives.getD []).length) := by
    simpa only [facts.projected, Option.getD_some] using readHeader_items _ _ _ _ facts.header
  have events := Caller.ProtocolTrace.Native.insertion_events ops allocate safety owner meaning base growth usizeBits children observations
    debug source address input key normalized deterministic before (before.graph.representatives.getD []) data exactRows header
  have actualEvents : leading ++ (insertionEntry before ::
      (Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits children observations
        debug source address input).insert key normalized deterministic before) <+: stream := inside
  rw [events] at actualEvents
  obtain ⟨trailing, rfl⟩ := actualEvents
  intro observed actual logical completed
  have related := insertion_replayed ops allocate safety base.allocator owner source address meaning input key normalized
    deterministic (before.graph.representatives.getD []) before growth mismatch leading trailing data header exactRows
    facts.valid frame.1.2.2.1 frame.2.1 admitted completed
  dsimp only [observed, logical, graphObservations]
  rw [events]
  simpa only [List.append_assoc, List.cons_append, List.length_cons, List.length_map, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using related

/-- One fixed stream and equal observed heaps now determine ordinary insertion
agreement without assuming equal native allocation cursors. The checkpoints
are observations of each actual port call, including after recursive children. -/
theorem CallFrame.insertion_checkpoint_agrees
    {safety : Bool} {owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {input : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {left right : World (Publication.Effects σ)}
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (debug : AssemblyItem.Fields.Values)
    (one : CallFrame safety base.allocator owner rows source values normalized address input parent left)
    (two : CallFrame safety base.allocator owner rows source values normalized address input parent right)
    (meaning : Meaning) (key : Key) (deterministic : Bool) (mismatch : Insertion.Native.Fault)
    (leading stream : List ProtocolEvent) (admitted : Admitted ops.arguments)
    (same : { left.graph with allocationCursor := leading.length } = { right.graph with allocationCursor := leading.length })
    (insideLeft : leading ++ (graphObservations ops allocate safety owner meaning base growth usizeBits children observations
      debug source address input).insert key normalized deterministic left <+: stream)
    (insideRight : leading ++ (graphObservations ops allocate safety owner meaning base growth usizeBits children observations
      debug source address input).insert key normalized deterministic right <+: stream) :
    let ports := graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug source address input
    let first := Insertion.Native.insert ops allocate safety base.allocator owner source address meaning input key normalized deterministic growth left
    let second := Insertion.Native.insert ops allocate safety base.allocator owner source address meaning input key normalized deterministic growth right
    ordinary first.1 = true → ordinary second.1 = true →
      (first.1, { first.2.graph with allocationCursor := leading.length + (ports.insert key normalized deterministic left).length }) =
        (second.1, { second.2.graph with allocationCursor := leading.length + (ports.insert key normalized deterministic right).length }) := by
  intro ports first second firstDone secondDone
  have firstSame := CallFrame.insertion_checkpoint_stream ops allocate base growth usizeBits children observations debug one
    meaning key deterministic mismatch leading stream admitted insideLeft firstDone
  have secondSame := CallFrame.insertion_checkpoint_stream ops allocate base growth usizeBits children observations debug two
    meaning key deterministic mismatch leading stream admitted insideRight secondDone
  dsimp only at firstSame secondSame
  rw [same] at firstSame
  exact firstSame.trans secondSame.symm

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
