/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointRecursiveEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.CheckpointEntry
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open NativeRecursion Recursive Caller.ProtocolTrace Interner.InvocationTrace

variable (depth : Nat) (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (allocators : outerBase.allocator = base.allocator)
    (debug : AssemblyItem.Fields.Values) (models : List ProtocolEvent → AllocationTrace.Models) (seed : Interner.Primitives)
    (stream leading trailing : List ProtocolEvent) (mismatch : Insertion.Native.Fault)
    (rows : List Storage.Cell) (parent : World (Publication.Effects σ) → Prop)
    (stack : Enclosing safety base.allocator owner parent)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (initial : parent (ChildTrace.erase before))
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety outerBase.allocator owner data capacity before rows)
    (admitted : Admitted ops.arguments) (outerAdmitted : Admitted outerOps.arguments)
    (typed : AssemblyItem.Initializers.DebugTyped debug)
    (sources : AllocationTrace.RecursiveSources ops allocate safety owner usizeBits meaning base growth debug depth models)
    (closedQuery : ∀ item, outerBase.queries.deterministic item = Interner.Queries.queries.deterministic item)
    (capacityQuery : seed.atCapacity {before.graph with allocationCursor := leading.length} = outerBase.queries.atCapacity before.graph)
    (classificationQuery : ∀ item, seed.deterministic item = outerBase.queries.deterministic item)

local notation "children" => AllocationTrace.children ops allocate safety owner meaning base growth usizeBits depth
local notation "observations" => ChildTrace.liftObservations
  (NativeRecursion.ProtocolTrace.observe (AllocationTrace.unfold ops allocate safety owner meaning base growth usizeBits depth))
local notation "captured" => AllocationTrace.step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits children observations
local notation "entryContext" => NativeRecursion.context (callerContext outerOps outerAllocate safety owner meaning outerBase outerGrowth)
  owner usizeBits children debug
local notation "entryPorts" => AllocationTrace.graphObservations outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
  children observations debug
local notation "childModel" => AllocationTrace.streamReplay stream (models stream)
local notation "fixedModel" => model meaning usizeBits debug childModel seed stream mismatch
include allocators stack initial facts admitted outerAdmitted typed sources closedQuery capacityQuery classificationQuery

theorem operation_from_sources (opcode : Opcode) (values : List NodeId)
    (joined : ((captured).operation opcode values debug before leading).2.events ++ trailing = stream) :
    EntryProjected (fixedModel (before.memory.memory.nextId + if values.isEmpty then 0 else 1)
      (Interner.constructorCode.operationRequest opcode values).item)
      (Interner.constructorCode.operationRequest opcode values) before.graph leading trailing
      ((captured).operation opcode values debug before leading) := by
  intro completed
  have lifted : Enclosing safety outerBase.allocator owner (fun world : ChildTrace.TracedWorld σ ProtocolEvent => parent (ChildTrace.erase world)) := by
    rw [allocators]
    exact stack.mapAllocator Prod.fst
  have checked := operation_projected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits children observations debug
    childModel seed stream mismatch before leading trailing meaning (fun _ => none) 0 outerAdmitted typed capacityQuery
    opcode values facts.valid (closedQuery _) (classificationQuery _) (by
      intro source prepared ran
      have ready := Arguments.prepare_success values before prepared source facts.valid ran
      obtain ⟨native, privateSource⟩ := prepared_input_frame (base := outerBase) (request := Interner.constructorCode.operationRequest opcode values) ready facts
      have parentPrepared := lifted.retained initial ready.good.1 ready.graph
        ⟨congrArg Publication.Effects.keys ready.effects, ready.frame, fun _ _ found => ready.heap ▸ found⟩
      have childCompleted : ordinary (item entryContext entryPorts source
          (Interner.constructorCode.operationRequest opcode values) debug prepared leading).1 = true := by
        dsimp only [AllocationTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug,
          constructors, literal] at completed
        simp only [ran] at completed
        split at completed <;> simpa only [retire_result] using completed
      have childJoined : (item entryContext entryPorts source
          (Interner.constructorCode.operationRequest opcode values) debug prepared leading).2.events ++ trailing = stream := by
        dsimp only [AllocationTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug,
          constructors, literal] at joined
        simp only [ran] at joined
        split at joined <;> exact joined
      have induction := item_induction_from_sources depth ops allocate safety owner usizeBits meaning base growth
        outerOps outerAllocate outerBase outerGrowth allocators debug source (Interner.constructorCode.operationRequest opcode values)
        prepared data capacity rows parent models seed stream leading trailing mismatch stack native ready.good.2 privateSource
        ready.arraySource (fun after valid graph retained => lifted.retained parentPrepared valid graph retained)
        (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) admitted outerAdmitted typed sources childCompleted childJoined
      simpa only [ready.counter] using induction)
  exact checked completed


theorem item_from_sources (source : View) (request : Interner.Request)
    (represented : Represents before.memory.memory source request.arguments)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (array : ArraySource source before.memory.memory)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (joined : (item entryContext entryPorts source request debug before leading).2.events ++ trailing = stream) :
    EntryProjected (fixedModel before.memory.memory.nextId request.item) request before.graph leading trailing
      (item entryContext entryPorts source request debug before leading) := by
  intro completed
  have lifted : Enclosing safety outerBase.allocator owner
      (fun world : ChildTrace.TracedWorld σ ProtocolEvent => parent (ChildTrace.erase world)) := by
    rw [allocators]
    exact stack.mapAllocator Prod.fst
  have induction := item_induction_from_sources depth ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth allocators debug source request before data capacity rows parent models seed
    stream leading trailing mismatch stack facts represented privateSource array
    (fun after valid graph retained => lifted.retained initial valid graph retained) domain admitted outerAdmitted typed sources completed joined
  exact item_projected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits children observations debug childModel
    seed stream mismatch source request before leading trailing meaning (fun _ => none) 0 ⟨facts.valid, represented⟩ outerAdmitted domain typed
    (closedQuery _) capacityQuery (classificationQuery _) induction completed

theorem borrowed_from_sources (source : ArgumentSlice) (opcode : Opcode)
    (represented : Represents before.memory.memory (view source) source.items)
    (privateSource : Caller.SourcePrivate (view source) before.memory.effects.keys)
    (array : ArraySource (view source) before.memory.memory)
    (joined : ((captured).borrowedOperation source.address opcode source.items debug before leading).2.events ++ trailing = stream) :
    EntryProjected (fixedModel before.memory.memory.nextId (Interner.constructorCode.operationRequest opcode source.items).item)
      (Interner.constructorCode.operationRequest opcode source.items) before.graph leading trailing
      ((captured).borrowedOperation source.address opcode source.items debug before leading) := by
  exact item_from_sources depth ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth allocators debug models seed stream leading trailing mismatch rows parent stack
    before initial data capacity facts admitted outerAdmitted typed sources closedQuery capacityQuery classificationQuery
    (view source) (Interner.constructorCode.operationRequest opcode source.items) represented privateSource array
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) joined

theorem constant_from_sources (value : Word)
    (joined : ((captured).constant value debug before leading).2.events ++ trailing = stream) :
    EntryProjected (fixedModel before.memory.memory.nextId (Interner.constructorCode.constantRequest value).item)
      (Interner.constructorCode.constantRequest value) before.graph leading trailing
      ((captured).constant value debug before leading) := by
  exact item_from_sources depth ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth allocators debug models seed stream leading trailing mismatch rows parent stack
    before initial data capacity facts admitted outerAdmitted typed sources closedQuery capacityQuery classificationQuery
    ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value)
    ⟨rfl, by intro index inside; exact (Nat.not_lt_zero index inside).elim⟩
    (by intro key old found nonempty impossible; exact (impossible rfl).elim) (ArraySource.empty rfl)
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) joined

theorem materialize_from_sources (id : NodeId) (value : Word)
    (joined : ((captured).materialize id value debug before leading).2.events ++ trailing = stream) :
    EntryProjected (fixedModel before.memory.memory.nextId (Interner.constructorCode.constantRequest value).item)
      (Interner.constructorCode.constantRequest value) before.graph leading trailing
      ((captured).materialize id value debug before leading) :=
  constant_from_sources depth ops allocate safety owner usizeBits meaning base growth
    outerOps outerAllocate outerBase outerGrowth allocators debug models seed stream leading trailing mismatch rows parent stack
    before initial data capacity facts admitted outerAdmitted typed sources closedQuery capacityQuery classificationQuery value joined

theorem local_from_sources (address : Nat) (opcode : Opcode) (left right repeated : NodeId)
    (selected : Nat) (first : Bool)
    (represented : Represents before.memory.memory ⟨address, 0, 2⟩ [left, right])
    (inside : first = true → selected < 2)
    (joined : ((captured).localOperation opcode ⟨address, [left, right]⟩ selected repeated first debug before leading).2.events ++ trailing = stream) :
    EntryProjected (fixedModel (before.memory.memory.nextId + 1)
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])).item)
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right]))
      before.graph leading trailing
      ((captured).localOperation opcode ⟨address, [left, right]⟩ selected repeated first debug before leading) := by
  intro completed
  have lifted : Enclosing safety outerBase.allocator owner (fun world : ChildTrace.TracedWorld σ ProtocolEvent => parent (ChildTrace.erase world)) := by
    rw [allocators]
    exact stack.mapAllocator Prod.fst
  have checked := local_projected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits children observations debug
    childModel seed stream mismatch before leading trailing meaning (fun _ => none) 0 outerAdmitted typed capacityQuery
    address opcode left right repeated selected first ⟨facts.valid, represented⟩ inside (closedQuery _) (classificationQuery _) (by
      intro source prepared ran
      have ready := ViewInput.local_input_optional ⟨address, 0, 2⟩ source left right repeated selected first before prepared
        ⟨facts.valid, represented⟩ inside ran
      obtain ⟨native, privateSource⟩ := prepared_input_frame (base := outerBase)
        (request := Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])) ready facts
      have parentPrepared := lifted.retained initial ready.good.1 ready.graph
        ⟨congrArg Publication.Effects.keys ready.effects, ready.frame, fun _ _ found => ready.heap ▸ found⟩
      have childCompleted : ordinary (item entryContext entryPorts source
          (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])) debug prepared leading).1 = true := by
        simpa only [AllocationTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug,
          constructors, namedLocal, view, List.length, ran, retire_result] using completed
      have childJoined : (item entryContext entryPorts source
          (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])) debug prepared leading).2.events ++ trailing = stream := by
        simpa only [AllocationTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug,
          constructors, namedLocal, view, List.length, ran] using joined
      have induction := item_induction_from_sources depth ops allocate safety owner usizeBits meaning base growth
        outerOps outerAllocate outerBase outerGrowth allocators debug source
        (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right]))
        prepared data capacity rows parent models seed stream leading trailing mismatch stack native ready.good.2 privateSource
        ready.arraySource (fun after valid graph retained => lifted.retained parentPrepared valid graph retained)
        (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) admitted outerAdmitted typed sources childCompleted childJoined
      have size : (if first then [left, right].set selected repeated else [left, right]).isEmpty = false := by
        cases first <;> simp
      simpa only [ready.counter, size, Bool.false_eq_true, ↓reduceIte] using induction)
  exact checked completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.CheckpointEntry
