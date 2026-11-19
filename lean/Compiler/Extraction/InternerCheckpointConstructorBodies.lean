/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointEntryBodies

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.CheckpointBodies
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

variable (depth : Nat) (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (debug : AssemblyItem.Fields.Values) (models : AllocationTrace.Models)
    (seed : Interner.Primitives)
    (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)

local notation "fixedChildren" => AllocationTrace.streamReplay stream models

local notation "nativeChildren" => AllocationTrace.children ops allocate safety owner meaning base growth usizeBits (depth + 1)
local notation "nativeObservations" => ChildTrace.liftObservations
  (NativeRecursion.ProtocolTrace.observe (AllocationTrace.unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)))

/-- Actual successful item/scratch preparation selects the proper-body
obligations. Constructor return, prefix execution and input identities remain
owned by the existing shared entry proofs. -/
def ItemBodies (source : View) (request : Interner.Request)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (leading trailing : List ProtocolEvent) : Prop :=
  ∀ (constructed : ChildTrace.TracedWorld σ ProtocolEvent)
    (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State),
    prepare request.item debug before = (.ok address, constructed) →
    outerBase.queries.atCapacity constructed.graph = false →
    Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) →
    Native.CheckpointEntry.BodyInduction depth ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
      debug source address (input request.item debug) request models stream ⟨constructed.memory.memory.nextId, 0, 2⟩
      (start { constructed with memory := { constructed.memory with memory } } leading) trailing

theorem item_induction_from_bodies (initialId : Nat) (source : View) (request : Interner.Request)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (leading trailing : List ProtocolEvent)
    (bodies : ItemBodies depth ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
      debug models stream source request before leading trailing) :
    CheckpointEntry.ItemInduction outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits nativeChildren nativeObservations
      debug fixedChildren seed stream mismatch initialId source request before leading trailing := by
  intro constructed address memory made room allocated
  have proper := bodies constructed address memory made room allocated
  with_reducible
    exact Native.CheckpointEntry.induction_from_bodies depth ops allocate safety owner usizeBits meaning base growth
      outerOps outerAllocate outerBase outerGrowth debug source address (input request.item debug) request models seed
      (initialId + 2) stream mismatch _ _ trailing proper

variable (before : ChildTrace.TracedWorld σ ProtocolEvent) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (admitted : Admitted outerOps.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : seed.atCapacity { before.graph with allocationCursor := leading.length } = outerBase.queries.atCapacity before.graph)
include other read sequence admitted typed capacityQuery

local notation "captured" => AllocationTrace.step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits nativeChildren nativeObservations
local notation "fixedModel" => CheckpointEntry.model meaning usizeBits debug fixedChildren seed stream mismatch
local notation "localBodies" => ItemBodies depth ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
  debug models stream
local notation "liftBodies" => item_induction_from_bodies depth ops allocate safety owner usizeBits meaning base growth outerOps outerAllocate outerBase outerGrowth
  debug models seed stream mismatch

theorem borrowed_projected (source : ArgumentSlice) (opcode : Opcode)
    (good : Good (view source) source.items before)
    (closedQuery : outerBase.queries.deterministic (Interner.constructorCode.operationRequest opcode source.items).item =
      Interner.Queries.queries.deterministic (Interner.constructorCode.operationRequest opcode source.items).item)
    (classificationQuery : seed.deterministic (Interner.constructorCode.operationRequest opcode source.items).item =
      outerBase.queries.deterministic (Interner.constructorCode.operationRequest opcode source.items).item)
    (bodies : localBodies (view source)
      (Interner.constructorCode.operationRequest opcode source.items) before leading trailing) :
    EntryProjected (fixedModel before.memory.memory.nextId (Interner.constructorCode.operationRequest opcode source.items).item)
      (Interner.constructorCode.operationRequest opcode source.items) before.graph leading trailing
      ((captured).borrowedOperation source.address opcode source.items debug before leading) := by
  have checked := CheckpointEntry.borrowed_projected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits nativeChildren nativeObservations
    debug fixedChildren seed stream mismatch before leading trailing other read sequence admitted typed capacityQuery source opcode good closedQuery classificationQuery
    (liftBodies before.memory.memory.nextId _ _ _ _ _ bodies)
  with_reducible exact checked

theorem constant_projected (value : Word) (valid : Valid before.memory)
    (closedQuery : outerBase.queries.deterministic (Interner.constructorCode.constantRequest value).item =
      Interner.Queries.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (classificationQuery : seed.deterministic (Interner.constructorCode.constantRequest value).item =
      outerBase.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (bodies : localBodies ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) before leading trailing) :
    EntryProjected (fixedModel before.memory.memory.nextId (Interner.constructorCode.constantRequest value).item)
      (Interner.constructorCode.constantRequest value) before.graph leading trailing
      ((captured).constant value debug before leading) := by
  have checked := CheckpointEntry.constant_projected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits nativeChildren nativeObservations
    debug fixedChildren seed stream mismatch before leading trailing other read sequence admitted typed capacityQuery value valid closedQuery classificationQuery
    (liftBodies before.memory.memory.nextId _ _ _ _ _ bodies)
  with_reducible exact checked

theorem materialize_projected (id : NodeId) (value : Word) (valid : Valid before.memory)
    (closedQuery : outerBase.queries.deterministic (Interner.constructorCode.constantRequest value).item =
      Interner.Queries.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (classificationQuery : seed.deterministic (Interner.constructorCode.constantRequest value).item =
      outerBase.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (bodies : localBodies ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) before leading trailing) :
    EntryProjected (fixedModel before.memory.memory.nextId (Interner.constructorCode.constantRequest value).item)
      (Interner.constructorCode.constantRequest value) before.graph leading trailing
      ((captured).materialize id value debug before leading) := by
  have checked := CheckpointEntry.materialize_projected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits nativeChildren nativeObservations
    debug fixedChildren seed stream mismatch before leading trailing other read sequence admitted typed capacityQuery id value valid closedQuery classificationQuery
    (liftBodies before.memory.memory.nextId _ _ _ _ _ bodies)
  with_reducible exact checked

theorem operation_projected (opcode : Opcode) (values : List NodeId) (valid : Valid before.memory)
    (closedQuery : outerBase.queries.deterministic (Interner.constructorCode.operationRequest opcode values).item =
      Interner.Queries.queries.deterministic (Interner.constructorCode.operationRequest opcode values).item)
    (classificationQuery : seed.deterministic (Interner.constructorCode.operationRequest opcode values).item =
      outerBase.queries.deterministic (Interner.constructorCode.operationRequest opcode values).item)
    (bodies : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) →
      localBodies source
        (Interner.constructorCode.operationRequest opcode values) prepared leading trailing) :
    EntryProjected (fixedModel (before.memory.memory.nextId + if values.isEmpty then 0 else 1)
      (Interner.constructorCode.operationRequest opcode values).item)
      (Interner.constructorCode.operationRequest opcode values) before.graph leading trailing
      ((captured).operation opcode values debug before leading) := by
  have checked := CheckpointEntry.operation_projected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits nativeChildren nativeObservations
    debug fixedChildren seed stream mismatch before leading trailing other read sequence admitted typed capacityQuery opcode values valid closedQuery classificationQuery
    (by
      intro source prepared ran
      have proper := liftBodies (before.memory.memory.nextId + if values.isEmpty then 0 else 1)
        source _ prepared leading trailing (bodies source prepared ran)
      with_reducible exact proper)
  with_reducible exact checked

theorem local_projected (address : Nat) (opcode : Opcode) (left right repeated : NodeId)
    (selected : Nat) (first : Bool) (good : Good ⟨address, 0, 2⟩ [left, right] before)
    (inside : first = true → selected < 2)
    (closedQuery : outerBase.queries.deterministic (Interner.constructorCode.operationRequest opcode
      (if first then [left, right].set selected repeated else [left, right])).item =
      Interner.Queries.queries.deterministic (Interner.constructorCode.operationRequest opcode
        (if first then [left, right].set selected repeated else [left, right])).item)
    (classificationQuery : seed.deterministic (Interner.constructorCode.operationRequest opcode
      (if first then [left, right].set selected repeated else [left, right])).item =
      outerBase.queries.deterministic (Interner.constructorCode.operationRequest opcode
        (if first then [left, right].set selected repeated else [left, right])).item)
    (bodies : ∀ source prepared, LocalArguments.zigLocal ⟨address, 0, 2⟩ selected repeated first before = (.ok source, prepared) →
      localBodies source
        (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right]))
        prepared leading trailing) :
    EntryProjected (fixedModel (before.memory.memory.nextId + 1)
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])).item)
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right]))
      before.graph leading trailing
      ((captured).localOperation opcode ⟨address, [left, right]⟩ selected repeated first debug before leading) := by
  have checked := CheckpointEntry.local_projected outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits nativeChildren nativeObservations
    debug fixedChildren seed stream mismatch before leading trailing other read sequence admitted typed capacityQuery address opcode left right repeated selected first good inside closedQuery classificationQuery
    (fun source prepared ran => liftBodies (before.memory.memory.nextId + 1)
      source _ prepared leading trailing (bodies source prepared ran))
  with_reducible exact checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.CheckpointBodies
