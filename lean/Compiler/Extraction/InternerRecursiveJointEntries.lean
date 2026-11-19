/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorJointEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Caller.ProtocolTrace ConstructorItem.ProtocolTrace

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner usizeBits depth : Nat) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (hosts : Insertion.Native.HostBindings outerOps ops outerAllocate allocate outerGrowth growth Prod.fst)
    (allocators : outerBase.allocator = base.allocator) (budgets : outerBase.budget = base.budget)
    (queries : outerBase.queries = base.queries)
    (env : AddressMask.Environment) (other : Meaning) (model : Interner.Primitives) (debug : AssemblyItem.Fields.Values)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (rows : List Storage.Cell)
    (parent : World (Publication.Effects σ) → Prop) (leading trailing : List ProtocolEvent)

local notation "properChildren" => NativeRecursion.unfold
  (callerContext ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth) owner usizeBits depth
local notation "properEvents" => observe (unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits depth)
local notation "parentFrame" => (fun world => parent (ChildTrace.erase world))

variable {capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    (facts : NativeGraph.Facts safety outerBase.allocator owner data capacity before rows)
    (admitted : Admitted outerOps.arguments) (typed : AssemblyItem.Initializers.DebugTyped debug)
    (valid : Interner.Invariant (Dispatch.wordDispatchMeaning env other) before.graph)
    (capacityQuery : model.atCapacity { before.graph with allocationCursor := leading.length } = outerBase.queries.atCapacity before.graph)
include hosts allocators budgets queries facts admitted typed valid capacityQuery

attribute [local irreducible] unfold NativeRecursion.unfold step JointPost mapReturn

/-- The actual finite constant execution consumes the joint step with native
children and computed observations at exactly the proper depth. -/
theorem constant_joint (value : Word) (pushes : Associative.Pushes other) (literals : Insertion.Native.PushValues other)
    (classificationQuery : model.deterministic (Interner.constructorCode.constantRequest value).item =
      outerBase.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (joint : JointEntry outerOps outerAllocate safety owner usizeBits outerBase outerGrowth properChildren properEvents env other debug ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) rows parentFrame model before leading trailing) :
    JointPost model (Interner.constructorCode.constantRequest value) before.graph leading trailing
      (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      ((unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits (depth + 1)).constant
        value debug (ChildTrace.erase before) leading) value := by
  have post := step_constant_joint outerOps outerAllocate safety owner usizeBits outerBase outerGrowth properChildren properEvents
    env other model debug before rows parentFrame leading trailing facts admitted typed valid capacityQuery value pushes literals classificationQuery joint
  have captured : (unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits (depth + 1)).constant
      value debug (ChildTrace.erase before) leading = _ := congrArg (fun family => family.constant value debug before leading)
    (unfold_step_traced hosts safety owner (Dispatch.wordDispatchMeaning env other) allocators usizeBits budgets queries depth)
  rw [captured]
  simpa only [allocators] using post.mapAllocator Prod.fst

theorem borrowed_joint (slice : ArgumentSlice) (opcode : Opcode) (expected : Word)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (privateSource : Caller.SourcePrivate (view slice) before.memory.effects.keys)
    (array : ArraySource (view slice) before.memory.memory)
    (evaluated : (Interner.constructorCode.operationRequest opcode slice.items).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read slice.items Interner.constructorCode.sequence = some expected)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode slice.items).item =
      outerBase.queries.deterministic (Interner.constructorCode.operationRequest opcode slice.items).item)
    (joint : JointEntry outerOps outerAllocate safety owner usizeBits outerBase outerGrowth properChildren properEvents env other debug (view slice)
      (Interner.constructorCode.operationRequest opcode slice.items) rows parentFrame model before leading trailing) :
    JointPost model (Interner.constructorCode.operationRequest opcode slice.items) before.graph leading trailing
      (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      ((unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits (depth + 1)).borrowedOperation
        slice.address opcode slice.items debug (ChildTrace.erase before) leading) expected := by
  have post := step_borrowed_joint outerOps outerAllocate safety owner usizeBits outerBase outerGrowth properChildren properEvents
    env other model debug before rows parentFrame leading trailing facts admitted typed valid capacityQuery
    slice opcode expected represented privateSource array evaluated classificationQuery joint
  have captured : (unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits (depth + 1)).borrowedOperation
      slice.address opcode slice.items debug (ChildTrace.erase before) leading = _ := congrArg (fun family => family.borrowedOperation slice.address opcode slice.items debug before leading)
    (unfold_step_traced hosts safety owner (Dispatch.wordDispatchMeaning env other) allocators usizeBits budgets queries depth)
  rw [captured]
  simpa only [allocators] using post.mapAllocator Prod.fst

theorem materialize_joint (id : NodeId) (value : Word) (pushes : Associative.Pushes other) (literals : Insertion.Native.PushValues other)
    (classificationQuery : model.deterministic (Interner.constructorCode.constantRequest value).item =
      outerBase.queries.deterministic (Interner.constructorCode.constantRequest value).item)
    (joint : JointEntry outerOps outerAllocate safety owner usizeBits outerBase outerGrowth properChildren properEvents env other debug ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) rows parentFrame model before leading trailing) :
    JointPost model (Interner.constructorCode.constantRequest value) before.graph leading trailing
      (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      ((unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits (depth + 1)).materialize id value debug (ChildTrace.erase before) leading) value := by
  have post := step_materialize_joint outerOps outerAllocate safety owner usizeBits outerBase outerGrowth properChildren properEvents
    env other model debug before rows parentFrame leading trailing facts admitted typed valid capacityQuery
    id value pushes literals classificationQuery joint
  have captured : (unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits (depth + 1)).materialize
      id value debug (ChildTrace.erase before) leading = _ := congrArg (fun family => family.materialize id value debug before leading)
    (unfold_step_traced hosts safety owner (Dispatch.wordDispatchMeaning env other) allocators usizeBits budgets queries depth)
  rw [captured]
  simpa only [allocators] using post.mapAllocator Prod.fst

theorem operation_joint (opcode : Opcode) (values : List NodeId) (expected : Word)
    (evaluated : (Interner.constructorCode.operationRequest opcode values).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read values Interner.constructorCode.sequence = some expected)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode values).item =
      outerBase.queries.deterministic (Interner.constructorCode.operationRequest opcode values).item)
    (joint : ∀ source prepared, Arguments.prepare values before = (.ok source, prepared) → Arguments.Prepared values before source prepared →
      JointEntry outerOps outerAllocate safety owner usizeBits outerBase outerGrowth properChildren properEvents env other debug source
        (Interner.constructorCode.operationRequest opcode values) rows parentFrame model prepared leading trailing)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    JointPost model (Interner.constructorCode.operationRequest opcode values) before.graph leading trailing
      (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      ((unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits (depth + 1)).operation opcode values debug (ChildTrace.erase before) leading) expected := by
  have post := step_operation_joint outerOps outerAllocate safety owner usizeBits outerBase outerGrowth properChildren properEvents
    env other model debug before rows parentFrame leading trailing facts admitted typed valid capacityQuery
    opcode values expected evaluated classificationQuery joint (fun world => localParent (ChildTrace.erase world))
  have captured : (unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits (depth + 1)).operation
      opcode values debug (ChildTrace.erase before) leading = _ := congrArg (fun family => family.operation opcode values debug before leading)
    (unfold_step_traced hosts safety owner (Dispatch.wordDispatchMeaning env other) allocators usizeBits budgets queries depth)
  rw [captured]
  simpa only [allocators] using post.mapAllocator Prod.fst

theorem local_joint (opcode : Opcode) (slice : ArgumentSlice) (selected : Nat) (repeated : NodeId) (first : Bool) (expected : Word)
    (represented : Represents before.memory.memory (view slice) slice.items)
    (inside : first = true → selected < slice.items.length)
    (evaluated : (Interner.constructorCode.operationRequest opcode
      (if first then slice.items.set selected repeated else slice.items)).item.eval
      (Dispatch.wordDispatchMeaning env other) before.graph.read
      (if first then slice.items.set selected repeated else slice.items) Interner.constructorCode.sequence = some expected)
    (classificationQuery : model.deterministic (Interner.constructorCode.operationRequest opcode
      (if first then slice.items.set selected repeated else slice.items)).item =
      outerBase.queries.deterministic (Interner.constructorCode.operationRequest opcode
        (if first then slice.items.set selected repeated else slice.items)).item)
    (joint : ∀ source prepared, LocalArguments.zigLocal (view slice) selected repeated first before = (.ok source, prepared) →
      Arguments.Prepared (if first then slice.items.set selected repeated else slice.items) before source prepared →
      JointEntry outerOps outerAllocate safety owner usizeBits outerBase outerGrowth properChildren properEvents env other debug source
        (Interner.constructorCode.operationRequest opcode (if first then slice.items.set selected repeated else slice.items))
        rows parentFrame model prepared leading trailing)
    (localParent : ∀ world, parent world → parent { world with memory := { world.memory with
      memory := Compiler.ZigAir.Memory.cleanup before.memory.memory.nextId world.memory.memory } }) :
    JointPost model (Interner.constructorCode.operationRequest opcode
      (if first then slice.items.set selected repeated else slice.items)) before.graph leading trailing
      (Dispatch.wordDispatchMeaning env other) (GraphFrame safety base.allocator owner rows parent)
      ((unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits (depth + 1)).localOperation
        opcode slice selected repeated first debug (ChildTrace.erase before) leading) expected := by
  have post := step_local_joint outerOps outerAllocate safety owner usizeBits outerBase outerGrowth properChildren properEvents
    env other model debug before rows parentFrame leading trailing facts admitted typed valid capacityQuery
    opcode slice selected repeated first expected represented inside evaluated classificationQuery joint (fun world => localParent (ChildTrace.erase world))
  have captured : (unfold ops allocate safety owner (Dispatch.wordDispatchMeaning env other) base growth usizeBits (depth + 1)).localOperation
      opcode slice selected repeated first debug (ChildTrace.erase before) leading = _ := congrArg (fun family => family.localOperation opcode slice selected repeated first debug before leading)
    (unfold_step_traced hosts safety owner (Dispatch.wordDispatchMeaning env other) allocators usizeBits budgets queries depth)
  rw [captured]
  simpa only [allocators] using post.mapAllocator Prod.fst

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
