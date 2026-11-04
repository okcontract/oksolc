/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorProtocolPreparedEntry
import Compiler.Extraction.InternerRecursiveProtocolTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace ConstructorItem.ProtocolTrace

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits depth : Nat)
    (model : Interner.Primitives) (debug : AssemblyItem.Fields.Values) (before : World (Publication.Effects σ))
    (leading trailing : List ProtocolEvent) (other : Meaning) (read : Read) (sequence : BitVec 32)

/-- The finite parent's existing context with the actual proper-depth children. -/
abbrev entryContext : PairInput.Context (Publication.Effects σ) :=
  context (callerContext ops allocate safety owner meaning base growth) owner usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth) debug

/-- Graph ports observe those same children at their actual source/item input. -/
abbrev entryPorts : View → Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → GraphObservations (Publication.Effects σ) :=
  Caller.ProtocolTrace.Native.graphObservations ops allocate safety owner meaning base growth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug

variable (admitted : Admitted (entryContext ops allocate safety owner meaning base growth usizeBits depth debug).external) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = (entryContext ops allocate safety owner meaning base growth usizeBits depth debug).queries.atCapacity before.graph)
include admitted typed capacityQuery other read sequence

/-- All ordinary literal entries of the actual finite family select their own
argument preparation. Children and events come from the same proper-depth
native execution; the reached miss correspondence remains an induction premise. -/
theorem operation_entry_projected (opcode : Opcode) (values : List NodeId) (valid : Valid before.memory)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode values).item =
      (entryContext ops allocate safety owner meaning base growth usizeBits depth debug).queries.deterministic (Interner.constructorCode.operationRequest opcode values).item)
    (miss : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) →
      EntryContinuation (entryContext ops allocate safety owner meaning base growth usizeBits depth debug)
      (entryPorts ops allocate safety owner meaning base growth usizeBits depth debug) model source (Interner.constructorCode.operationRequest opcode values) debug prepared leading trailing) :
    EntryProjected model (Interner.constructorCode.operationRequest opcode values) before.graph leading trailing
      ((unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)).operation opcode values debug before leading) :=
  literal_entry_projected (entryContext ops allocate safety owner meaning base growth usizeBits depth debug)
      (entryPorts ops allocate safety owner meaning base growth usizeBits depth debug) model opcode values debug before leading trailing other read sequence
    valid admitted typed capacityQuery classificationQuery miss

/-- Borrowing enters the same item theorem with its actual address and contents. -/
theorem borrowed_entry_projected (opcode : Opcode) (source : ArgumentSlice) (good : Good (view source) source.items before)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode source.items).item =
      (entryContext ops allocate safety owner meaning base growth usizeBits depth debug).queries.deterministic (Interner.constructorCode.operationRequest opcode source.items).item)
    (miss : EntryContinuation (entryContext ops allocate safety owner meaning base growth usizeBits depth debug)
      (entryPorts ops allocate safety owner meaning base growth usizeBits depth debug) model (view source)
      (Interner.constructorCode.operationRequest opcode source.items) debug before leading trailing) :
    EntryProjected model (Interner.constructorCode.operationRequest opcode source.items) before.graph leading trailing
      ((unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)).borrowedOperation source.address opcode source.items debug before leading) :=
  item_entry_projected (entryContext ops allocate safety owner meaning base growth usizeBits depth debug)
      (entryPorts ops allocate safety owner meaning base growth usizeBits depth debug) model (view source) (Interner.constructorCode.operationRequest opcode source.items)
    debug before leading trailing other read sequence good admitted
    (by change (1 : Int) ∈ AssemblyItem.itemTagValues; decide) typed capacityQuery classificationQuery miss

theorem constant_entry_projected (value : Contract.Yul.Word) (valid : Valid before.memory)
    (classificationQuery : model.deterministic (Interner.constructorCode.constantRequest value).item =
      (entryContext ops allocate safety owner meaning base growth usizeBits depth debug).queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (miss : EntryContinuation (entryContext ops allocate safety owner meaning base growth usizeBits depth debug)
      (entryPorts ops allocate safety owner meaning base growth usizeBits depth debug) model ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) debug before leading trailing) :
    EntryProjected model (Interner.constructorCode.constantRequest value) before.graph leading trailing
      ((unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)).constant value debug before leading) :=
  item_entry_projected (entryContext ops allocate safety owner meaning base growth usizeBits depth debug)
      (entryPorts ops allocate safety owner meaning base growth usizeBits depth debug) model ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest value)
    debug before leading trailing other read sequence ⟨valid, rfl, by intro index inside; change index < 0 at inside; omega⟩ admitted
    (by change (2 : Int) ∈ AssemblyItem.itemTagValues; decide) typed capacityQuery classificationQuery miss

/-- Materialization forwards to the same constant route, without inspecting
the old expression ID or changing the native children or resource observation. -/
theorem materialize_entry_projected (id : NodeId) (value : Contract.Yul.Word) (valid : Valid before.memory)
    (classificationQuery : model.deterministic (Interner.constructorCode.constantRequest value).item =
      (entryContext ops allocate safety owner meaning base growth usizeBits depth debug).queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (miss : EntryContinuation (entryContext ops allocate safety owner meaning base growth usizeBits depth debug)
      (entryPorts ops allocate safety owner meaning base growth usizeBits depth debug) model ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) debug before leading trailing) :
    EntryProjected model (Interner.constructorCode.constantRequest value) before.graph leading trailing
      ((unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)).materialize id value debug before leading) :=
  constant_entry_projected ops allocate safety owner meaning base growth usizeBits depth model debug before leading trailing
    other read sequence admitted typed capacityQuery value valid classificationQuery miss

/-- All local shapes are inspected at the actual constructor guard. A valid
two-word route derives its copy and optional overwrite; other shapes reject
before running item preparation. No successful producer state is supplied. -/
theorem local_entry_projected (opcode : Opcode) (source : ArgumentSlice) (selected : Nat) (repeated : NodeId) (first : Bool)
    (good : Good (view source) source.items before) (inside : first = true → selected < source.items.length)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode
      (if first then source.items.set selected repeated else source.items)).item =
      (entryContext ops allocate safety owner meaning base growth usizeBits depth debug).queries.deterministic (Interner.constructorCode.operationRequest opcode
        (if first then source.items.set selected repeated else source.items)).item)
    (miss : ∀ target prepared, LocalArguments.zigLocal (view source) selected repeated first before = (.ok target, prepared) →
      EntryContinuation (entryContext ops allocate safety owner meaning base growth usizeBits depth debug)
      (entryPorts ops allocate safety owner meaning base growth usizeBits depth debug) model target (Interner.constructorCode.operationRequest opcode
        (if first then source.items.set selected repeated else source.items)) debug prepared leading trailing) :
    EntryProjected model (Interner.constructorCode.operationRequest opcode
      (if first then source.items.set selected repeated else source.items)) before.graph leading trailing
      ((unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)).localOperation opcode source selected repeated first debug before leading) := by
  change EntryProjected _ _ _ _ _ ((ConstructorItem.ProtocolTrace.constructors (entryContext ops allocate safety owner meaning base growth usizeBits depth debug)
      (entryPorts ops allocate safety owner meaning base growth usizeBits depth debug)).localOperation
    opcode source selected repeated first debug before leading)
  rcases items : source.items with _ | ⟨left, _ | ⟨right, _ | ⟨extra, tail⟩⟩⟩
  · simp only [ConstructorItem.ProtocolTrace.constructors, items]
    intro completed
    cases completed
  · simp only [ConstructorItem.ProtocolTrace.constructors, items]
    intro completed
    cases completed
  · have bound : first = true → selected < 2 := by simpa only [items] using inside
    have checked := ConstructorItem.ProtocolTrace.local_entry_projected (entryContext ops allocate safety owner meaning base growth usizeBits depth debug)
      (entryPorts ops allocate safety owner meaning base growth usizeBits depth debug) model opcode (view source)
      left right repeated selected first debug before leading trailing other read sequence
      (by simpa only [items] using good) bound admitted typed capacityQuery
      (by simpa only [items] using classificationQuery) (by simpa only [items] using miss)
    simpa only [ConstructorItem.ProtocolTrace.constructors, items] using checked
  · simp only [ConstructorItem.ProtocolTrace.constructors, items]
    intro completed
    cases completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
