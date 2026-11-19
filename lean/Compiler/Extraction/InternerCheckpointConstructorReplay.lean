/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCheckpointEntryReplay
import Compiler.Extraction.InternerConstructorProtocolPreparedEntry

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.CheckpointEntry
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace
open NativeRecursion Recursive Interner.InvocationTrace

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning)
    (base : PairInput.Context (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (usizeBits : Nat) (children : Constructors (Publication.Effects σ))
    (observations : ChildTrace.Observations σ ProtocolEvent) (debug : AssemblyItem.Fields.Values)
    (childModel : Associative.Constructors AssemblyItem.Fields.Values) (seed : Interner.Primitives)
    (stream : List ProtocolEvent) (mismatch : Insertion.Native.Fault)

local notation "entryContext" => NativeRecursion.context (callerContext ops allocate safety owner meaning base growth)
  owner usizeBits children debug
local notation "entryPorts" => AllocationTrace.graphObservations ops allocate safety owner meaning base growth usizeBits children observations debug

/-- The item and scratch allocations precede normalization. Their identities
come from the constructor's initial cursor, not a selected miss or final slice. -/
def model (initialId : Nat) (item : Item) : Interner.Primitives :=
  dispatchModel (AllocationTrace.inputGraphReplay seed (input item debug) (initialId + 2) meaning stream mismatch)
    childModel usizeBits debug

/-- Actual preparation selects the local obligations while preserving the
model fixed before either allocation. Rejected preparation needs no miss law. -/
def ItemInduction (initialId : Nat) (source : View) (request : Interner.Request)
    (before : World (Publication.Effects σ)) (leading trailing : List ProtocolEvent) : Prop :=
  ∀ (constructed : World (Publication.Effects σ))
    (address : Compiler.ZigAir.Memory.Address) (memory : Compiler.ZigAir.Memory.State),
    prepare request.item debug before = (.ok address, constructed) →
    base.queries.atCapacity constructed.graph = false →
    Compiler.ZigAir.Memory.allocate constructed.memory.memory (.array 2 word) =
      .ok (.pointer (.pointer true false (.array 2 word)) ⟨constructed.memory.memory.nextId, 0⟩, memory) →
    Caller.ProtocolTrace.Native.CheckpointEntry.Induction ops allocate safety owner meaning base growth usizeBits children observations
      debug source address (input request.item debug) request childModel seed (initialId + 2) stream mismatch
      ⟨constructed.memory.memory.nextId, 0, 2⟩
      (start { constructed with memory := { constructed.memory with memory } } leading) trailing

theorem item_continuation (source : View) (request : Interner.Request)
    (before : World (Publication.Effects σ)) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted ops.arguments)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (closedQuery : base.queries.deterministic request.item = Interner.Queries.queries.deterministic request.item)
    (induction : ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch
      before.memory.memory.nextId source request before leading trailing) :
    EntryContinuation entryContext entryPorts
      (model meaning usizeBits debug childModel seed stream mismatch before.memory.memory.nextId request.item)
      source request debug before leading trailing := by
  intro constructed address memory made room allocated
  have preparedItem := (prepare_success request.item debug before constructed address good.1 domain typed made).2
  have constructedGood := good_frame before constructed source request.arguments good preparedItem.valid preparedItem.memory
  have cursor : constructed.memory.memory.nextId + 1 = before.memory.memory.nextId + 2 := by
    rw [preparedItem.nextId]
  have localStep := induction constructed address memory made room allocated
  have checked := Caller.ProtocolTrace.Native.CheckpointEntry.entry_continuation ops allocate safety owner meaning base growth usizeBits
    children observations debug source address (input request.item debug) request childModel seed stream mismatch
    constructed memory _ leading trailing other read sequence constructedGood admitted allocated closedQuery
    (by simpa only [cursor] using localStep)
  simpa only [model, cursor] using checked

/-- The original complete item proof supplies errors, cache hits and both
retirement marks. Only the local checkpoint obligations remain conditional. -/
theorem item_projected (source : View) (request : Interner.Request)
    (before : World (Publication.Effects σ)) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (good : Good source request.arguments before) (admitted : Admitted ops.arguments)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (closedQuery : base.queries.deterministic request.item = Interner.Queries.queries.deterministic request.item)
    (capacityQuery : seed.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
    (classificationQuery : seed.deterministic request.item = base.queries.deterministic request.item)
    (induction : ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch
      before.memory.memory.nextId source request before leading trailing) :
    EntryProjected (model meaning usizeBits debug childModel seed stream mismatch before.memory.memory.nextId request.item)
      request before.graph leading trailing (item entryContext entryPorts source request debug before leading) :=
  item_entry_projected entryContext entryPorts
    (model meaning usizeBits debug childModel seed stream mismatch before.memory.memory.nextId request.item)
    source request debug before leading trailing other read sequence good
    (Publication.external_admitted ops.arguments admitted) domain typed capacityQuery classificationQuery
    (item_continuation ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch
      source request before leading trailing other read sequence good admitted domain typed closedQuery induction)

/-- Literal arrays and local copies already share Prepared. Its counter law
fixes the outer model before their allocation; their actual return proofs can
therefore consume the same item continuation without rebuilding preparation. -/
theorem prepared_continuation (source : View) (request : Interner.Request)
    (before prepared : World (Publication.Effects σ)) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (ready : Arguments.Prepared request.arguments before source prepared) (admitted : Admitted ops.arguments)
    (domain : (request.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (closedQuery : base.queries.deterministic request.item = Interner.Queries.queries.deterministic request.item)
    (induction : ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch
      (before.memory.memory.nextId + if request.arguments.isEmpty then 0 else 1) source request prepared leading trailing) :
    EntryContinuation entryContext entryPorts
      (model meaning usizeBits debug childModel seed stream mismatch
        (before.memory.memory.nextId + if request.arguments.isEmpty then 0 else 1) request.item)
      source request debug prepared leading trailing := by
  have checked := item_continuation ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch
    source request prepared leading trailing other read sequence ready.good admitted domain typed closedQuery
    (by simpa only [ready.counter] using induction)
  simpa only [ready.counter] using checked

variable (before : World (Publication.Effects σ)) (leading trailing : List ProtocolEvent)
    (other : Meaning) (read : Read) (sequence : BitVec 32)
    (admitted : Admitted ops.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : seed.atCapacity { before.graph with allocationCursor := leading.length } = base.queries.atCapacity before.graph)
include other read sequence admitted typed capacityQuery

local notation "captured" => AllocationTrace.step ops allocate safety owner meaning base growth usizeBits children observations
local notation "fixedModel" => model meaning usizeBits debug childModel seed stream mismatch
local notation "localInduction" => ItemInduction ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch

/-- Borrowing needs no outer allocation; the observed constructor uses the
model fixed at its original entry cursor. -/
theorem borrowed_projected (source : ArgumentSlice) (opcode : Opcode)
    (good : Good (view source) source.items before)
    (closedQuery : base.queries.deterministic (Interner.constructorCode.operationRequest opcode source.items).item =
      Interner.Queries.queries.deterministic (Interner.constructorCode.operationRequest opcode source.items).item)
    (classificationQuery : seed.deterministic (Interner.constructorCode.operationRequest opcode source.items).item =
      base.queries.deterministic (Interner.constructorCode.operationRequest opcode source.items).item)
    (induction : localInduction before.memory.memory.nextId (view source)
      (Interner.constructorCode.operationRequest opcode source.items) before leading trailing) :
    EntryProjected (fixedModel before.memory.memory.nextId (Interner.constructorCode.operationRequest opcode source.items).item)
      (Interner.constructorCode.operationRequest opcode source.items) before.graph leading trailing
      ((captured).borrowedOperation source.address opcode source.items debug before leading) := by
  have checked := item_projected ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch
    (view source) (Interner.constructorCode.operationRequest opcode source.items) before leading trailing other read sequence good admitted
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed closedQuery capacityQuery classificationQuery induction
  dsimp only [AllocationTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug, constructors, view] at checked ⊢
  with_reducible exact checked

theorem constant_projected (value : Word) (valid : Valid before.memory)
    (closedQuery : base.queries.deterministic (Interner.constructorCode.constantRequest value).item =
      Interner.Queries.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (classificationQuery : seed.deterministic (Interner.constructorCode.constantRequest value).item =
      base.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (induction : localInduction before.memory.memory.nextId ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) before leading trailing) :
    EntryProjected (fixedModel before.memory.memory.nextId (Interner.constructorCode.constantRequest value).item)
      (Interner.constructorCode.constantRequest value) before.graph leading trailing
      ((captured).constant value debug before leading) := by
  have checked := item_projected ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch
    ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value) before leading trailing other read sequence
    ⟨valid, rfl, by intro index inside; exact (Nat.not_lt_zero index inside).elim⟩ admitted
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) typed closedQuery capacityQuery classificationQuery induction
  dsimp only [AllocationTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug, constructors] at checked ⊢
  with_reducible exact checked

theorem materialize_projected (id : NodeId) (value : Word) (valid : Valid before.memory)
    (closedQuery : base.queries.deterministic (Interner.constructorCode.constantRequest value).item =
      Interner.Queries.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (classificationQuery : seed.deterministic (Interner.constructorCode.constantRequest value).item =
      base.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (induction : localInduction before.memory.memory.nextId ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) before leading trailing) :
    EntryProjected (fixedModel before.memory.memory.nextId (Interner.constructorCode.constantRequest value).item)
      (Interner.constructorCode.constantRequest value) before.graph leading trailing
      ((captured).materialize id value debug before leading) := by
  have checked := constant_projected ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch
    before leading trailing other read sequence admitted typed capacityQuery value valid closedQuery classificationQuery induction
  dsimp only [AllocationTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug, constructors] at checked ⊢
  with_reducible exact checked

/-- Empty literals retain their original cursor; nonempty literals use the
single allocation already proved by Arguments.Prepared. -/
theorem operation_projected (opcode : Opcode) (values : List NodeId) (valid : Valid before.memory)
    (closedQuery : base.queries.deterministic (Interner.constructorCode.operationRequest opcode values).item =
      Interner.Queries.queries.deterministic (Interner.constructorCode.operationRequest opcode values).item)
    (classificationQuery : seed.deterministic (Interner.constructorCode.operationRequest opcode values).item =
      base.queries.deterministic (Interner.constructorCode.operationRequest opcode values).item)
    (induction : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) →
      localInduction (before.memory.memory.nextId + if values.isEmpty then 0 else 1) source
        (Interner.constructorCode.operationRequest opcode values) prepared leading trailing) :
    EntryProjected (fixedModel (before.memory.memory.nextId + if values.isEmpty then 0 else 1)
      (Interner.constructorCode.operationRequest opcode values).item)
      (Interner.constructorCode.operationRequest opcode values) before.graph leading trailing
      ((captured).operation opcode values debug before leading) := by
  have miss : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) →
      EntryContinuation entryContext entryPorts
        (fixedModel (before.memory.memory.nextId + if values.isEmpty then 0 else 1) (Interner.constructorCode.operationRequest opcode values).item)
        source (Interner.constructorCode.operationRequest opcode values) debug prepared leading trailing := by
    intro source prepared ran
    have checked := prepared_continuation ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch
      source (Interner.constructorCode.operationRequest opcode values) before prepared leading trailing other read sequence
      (Arguments.prepare_success values before prepared source valid ran)
      admitted (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed closedQuery (by
        have localStep := induction source prepared ran
        dsimp (config := { instances := true }) only [Interner.ConstructorCode.operationRequest] at localStep ⊢
        with_reducible exact localStep)
    dsimp (config := { instances := true }) only [Interner.ConstructorCode.operationRequest] at checked ⊢
    with_reducible exact checked
  have checked := literal_entry_projected entryContext entryPorts
    (fixedModel (before.memory.memory.nextId + if values.isEmpty then 0 else 1) (Interner.constructorCode.operationRequest opcode values).item)
    opcode values debug before leading trailing other read sequence
    valid (Publication.external_admitted ops.arguments admitted) typed capacityQuery classificationQuery miss
  dsimp only [AllocationTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug, constructors] at checked ⊢
  with_reducible exact checked

/-- The named copy uses the same prepared-input continuation and original
retirement mark; the optional overwrite retains its source guard. -/
theorem local_projected (address : Nat) (opcode : Opcode) (left right repeated : NodeId)
    (selected : Nat) (first : Bool) (good : Good ⟨address, 0, 2⟩ [left, right] before)
    (inside : first = true → selected < 2)
    (closedQuery : base.queries.deterministic (Interner.constructorCode.operationRequest opcode
      (if first then [left, right].set selected repeated else [left, right])).item =
      Interner.Queries.queries.deterministic (Interner.constructorCode.operationRequest opcode
        (if first then [left, right].set selected repeated else [left, right])).item)
    (classificationQuery : seed.deterministic (Interner.constructorCode.operationRequest opcode
      (if first then [left, right].set selected repeated else [left, right])).item =
      base.queries.deterministic (Interner.constructorCode.operationRequest opcode
        (if first then [left, right].set selected repeated else [left, right])).item)
    (induction : ∀ source prepared, LocalArguments.zigLocal ⟨address, 0, 2⟩ selected repeated first before = (.ok source, prepared) →
      localInduction (before.memory.memory.nextId + 1) source
        (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right]))
        prepared leading trailing) :
    EntryProjected (fixedModel (before.memory.memory.nextId + 1)
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])).item)
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right]))
      before.graph leading trailing
      ((captured).localOperation opcode ⟨address, [left, right]⟩ selected repeated first debug before leading) := by
  have miss : ∀ source prepared, LocalArguments.zigLocal ⟨address, 0, 2⟩ selected repeated first before = (.ok source, prepared) →
      EntryContinuation entryContext entryPorts
        (fixedModel (before.memory.memory.nextId + 1)
          (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])).item)
        source (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right]))
        debug prepared leading trailing := by
    intro source prepared ran
    have ready := ViewInput.local_input_optional ⟨address, 0, 2⟩ source left right repeated selected first before prepared good inside ran
    have nonempty : (if first then [left, right].set selected repeated else [left, right]).isEmpty = false := by
      apply List.isEmpty_eq_false_iff.mpr
      intro empty
      have size : (if first then [left, right].set selected repeated else [left, right]).length = 2 := by split <;> simp
      rw [empty] at size
      contradiction
    have checked := prepared_continuation ops allocate safety owner meaning base growth usizeBits children observations debug childModel seed stream mismatch
      source (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right]))
      before prepared leading trailing other read sequence ready admitted
      (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed closedQuery (by
        have localStep := induction source prepared ran
        simp only [Interner.ConstructorCode.operationRequest, nonempty, Bool.false_eq_true, ↓reduceIte] at localStep ⊢
        with_reducible exact localStep)
    simp only [Interner.ConstructorCode.operationRequest, nonempty, Bool.false_eq_true, ↓reduceIte] at checked ⊢
    with_reducible exact checked
  have checked := local_entry_projected entryContext entryPorts
    (fixedModel (before.memory.memory.nextId + 1)
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])).item)
    opcode ⟨address, 0, 2⟩ left right repeated selected first debug
    before leading trailing other read sequence good inside (Publication.external_admitted ops.arguments admitted) typed capacityQuery classificationQuery miss
  dsimp only [AllocationTrace.step, NativeRecursion.ProtocolTrace.stepWith, NativeRecursion.ProtocolTrace.atDebug, constructors, view, List.length] at checked ⊢
  with_reducible exact checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ProtocolTrace.CheckpointEntry
