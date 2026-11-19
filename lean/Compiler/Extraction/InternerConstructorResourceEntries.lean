/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerResourceInduction
import Compiler.Extraction.InternerConstructorProtocolPreparedEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.ResourceEntry
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

variable (ops : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (allocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (growth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent))) (usizeBits : Nat)
    (children : Constructors (Publication.Effects σ)) (observations : ChildTrace.Observations σ ProtocolEvent)
    (debug : AssemblyItem.Fields.Values)

local notation "entryContext" => NativeRecursion.context (callerContext ops allocate safety owner meaning base growth)
  owner usizeBits (ChildTrace.constructors children observations) debug
local notation "entryPorts" => Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits
  (ChildTrace.constructors children observations) (ChildTrace.liftObservations observations) debug

/-- Only successful item/scratch preparation requests entry induction. Each
reached miss retains the model fixed at the original item entry. -/
def ItemInduction (model : Interner.Primitives) (source : View) (request : Interner.Request)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (leading trailing : List ProtocolEvent) : Prop :=
  ∀ (constructed : ChildTrace.TracedWorld σ ProtocolEvent)
    (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State),
    prepare request.item debug before = (.ok address, constructed) →
    base.queries.atCapacity constructed.graph = false →
    Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) →
    Caller.ProtocolTrace.Native.ResourceEntry.EntryInduction ops allocate safety owner meaning base growth usizeBits children observations
      debug source address (input request.item debug) request model ⟨constructed.memory.memory.nextId, 0, 2⟩
      (start { constructed with memory := { constructed.memory with memory } } leading) trailing

theorem item_continuation (model : Interner.Primitives) (source : View) (request : Interner.Request)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted (Publication.external ops.arguments))
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (induction : ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug
      model source request before leading trailing) :
    EntryContinuation entryContext entryPorts model source request debug before leading trailing := by
  intro constructed address memory made room allocated
  have preparedItem := (prepare_success request.item debug before constructed address good.1 domain typed made).2
  have constructedGood := good_frame before constructed source request.arguments good preparedItem.valid preparedItem.memory
  exact Caller.ProtocolTrace.Native.ResourceEntry.entry_continuation ops allocate safety owner meaning base growth usizeBits
    children observations debug source address (input request.item debug) request model constructed memory _ leading trailing other read sequence
    constructedGood.1 constructedGood.2 allocated admitted (induction constructed address memory made room allocated)

/-- Preparation, cache/error branches and both original retirement marks use
the existing complete item proof; resource induction is needed only at misses. -/
theorem item_projected (model : Interner.Primitives) (source : View) (request : Interner.Request)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted (Publication.external ops.arguments))
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
    (classificationQuery : model.deterministic request.item = base.queries.deterministic request.item)
    (induction : ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug
      model source request before leading trailing) :
    EntryProjected model request before.graph leading trailing (item entryContext entryPorts source request debug before leading) :=
  item_entry_projected entryContext entryPorts model source request debug before leading trailing other read sequence
    good admitted domain typed capacityQuery classificationQuery
    (item_continuation ops allocate safety owner meaning base growth usizeBits children observations debug
      model source request before leading trailing other read sequence good admitted domain typed induction)

variable (model : Interner.Primitives) (before : ChildTrace.TracedWorld σ ProtocolEvent) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (admitted : Admitted (Publication.external ops.arguments)) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
include other read sequence admitted typed capacityQuery

theorem borrowed_projected (source : ArgumentSlice) (opcode : Opcode)
    (good : Good (view source) source.items before)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode source.items).item =
      base.queries.deterministic (Interner.constructorCode.operationRequest opcode source.items).item)
    (induction : ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug
      model (view source) (Interner.constructorCode.operationRequest opcode source.items) before leading trailing) :
    EntryProjected model (Interner.constructorCode.operationRequest opcode source.items) before.graph leading trailing
      ((constructors entryContext entryPorts).borrowedOperation source.address opcode source.items debug before leading) :=
  item_projected ops allocate safety owner meaning base growth usizeBits children observations debug model (view source)
    _ before leading trailing other read sequence good admitted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide)
    typed capacityQuery classificationQuery induction

theorem constant_projected (value : Word) (valid : Valid before.memory)
    (classificationQuery : model.deterministic (Interner.constructorCode.constantRequest value).item =
      base.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (induction : ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug
      model ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) before leading trailing) :
    EntryProjected model (Interner.constructorCode.constantRequest value) before.graph leading trailing
      ((constructors entryContext entryPorts).constant value debug before leading) :=
  item_projected ops allocate safety owner meaning base growth usizeBits children observations debug model ⟨0, 0, 0⟩
    (Interner.constructorCode.constantRequest value) before leading trailing other read sequence
    ⟨valid, rfl, by intro index inside; exact (Nat.not_lt_zero index inside).elim⟩ admitted
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) typed capacityQuery classificationQuery induction

theorem materialize_projected (id : NodeId) (value : Word) (valid : Valid before.memory)
    (classificationQuery : model.deterministic (Interner.constructorCode.constantRequest value).item =
      base.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (induction : ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug
      model ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) before leading trailing) :
    EntryProjected model (Interner.constructorCode.constantRequest value) before.graph leading trailing
      ((constructors entryContext entryPorts).materialize id value debug before leading) :=
  constant_projected ops allocate safety owner meaning base growth usizeBits children observations debug model before leading trailing
    other read sequence admitted typed capacityQuery value valid classificationQuery induction

theorem operation_projected (opcode : Opcode) (values : List NodeId) (valid : Valid before.memory)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode values).item =
      base.queries.deterministic (Interner.constructorCode.operationRequest opcode values).item)
    (induction : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) →
      ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug
        model source (Interner.constructorCode.operationRequest opcode values) prepared leading trailing) :
    EntryProjected model (Interner.constructorCode.operationRequest opcode values) before.graph leading trailing
      ((constructors entryContext entryPorts).operation opcode values debug before leading) := by
  apply literal_entry_projected entryContext entryPorts model opcode values debug before leading trailing other read sequence
    valid admitted typed capacityQuery classificationQuery
  intro source prepared ran
  exact item_continuation ops allocate safety owner meaning base growth usizeBits children observations debug
    model source _ prepared leading trailing other read sequence (Arguments.prepare_success values before prepared source valid ran).good
    admitted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed (induction source prepared ran)

theorem local_projected (address : Nat) (opcode : Opcode) (left right repeated : NodeId)
    (selected : Nat) (first : Bool) (good : Good ⟨address, 0, 2⟩ [left, right] before)
    (inside : first = true → selected < 2)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode
      (if first then [left, right].set selected repeated else [left, right])).item =
      base.queries.deterministic (Interner.constructorCode.operationRequest opcode
        (if first then [left, right].set selected repeated else [left, right])).item)
    (induction : ∀ source prepared, LocalArguments.zigLocal ⟨address, 0, 2⟩ selected repeated first before = (.ok source, prepared) →
      ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug
        model source (Interner.constructorCode.operationRequest opcode
          (if first then [left, right].set selected repeated else [left, right])) prepared leading trailing) :
    EntryProjected model (Interner.constructorCode.operationRequest opcode
      (if first then [left, right].set selected repeated else [left, right])) before.graph leading trailing
      ((constructors entryContext entryPorts).localOperation opcode ⟨address, [left, right]⟩ selected repeated first debug before leading) := by
  refine local_entry_projected entryContext entryPorts model opcode ⟨address, 0, 2⟩ left right repeated selected first debug
    before leading trailing other read sequence good inside admitted typed capacityQuery classificationQuery ?_
  intro source prepared ran
  exact item_continuation ops allocate safety owner meaning base growth usizeBits children observations debug
    model source _ prepared leading trailing other read sequence
    (ViewInput.local_input_optional ⟨address, 0, 2⟩ source left right repeated selected first before prepared good inside ran).good
    admitted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed (induction source prepared ran)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.ResourceEntry
