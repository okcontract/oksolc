/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerRecursiveProtocolEffects
import Compiler.Extraction.InternerRecursiveProtocolReturn

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace ConstructorItem.ProtocolTrace

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits depth : Nat)
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (hosts : Insertion.Native.HostBindings outerOps ops outerAllocate allocate outerGrowth growth Prod.fst)
    (budgets : outerBase.budget = base.budget) (allocators : outerBase.allocator = base.allocator)
    (queries : outerBase.queries = base.queries) (debug : AssemblyItem.Fields.Values)
include hosts budgets allocators queries

omit hosts budgets allocators queries in
theorem materialize_forwarded (id : NodeId) (value : Contract.Yul.Word) :
    (unfold ops allocate safety owner meaning base growth usizeBits depth).materialize id value debug =
      (unfold ops allocate safety owner meaning base growth usizeBits depth).constant value debug := by
  cases depth <;> rfl

attribute [local irreducible] unfold PreparedMiss

/-- The borrowed miss now returns through the actual finite native family.
Only local host/configuration bindings are added to the shared miss premises;
its proper-child semantic/frame hypothesis remains explicit inside PreparedMiss. -/
theorem borrowed_miss_bound (opcode : Opcode) (source : ArgumentSlice)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (good : Good (view source) source.items before) :
    PreparedMiss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug (view source)
      (Interner.constructorCode.operationRequest opcode source.items) before
      ((unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)).borrowedOperation
        source.address opcode source.items debug (ChildTrace.erase before))
      (mapReturn (Publication.Effects.mapAllocator Prod.fst)) := by
  have forwarded := congrArg (fun family => family.borrowedOperation source.address opcode source.items debug before)
    (unfold_step_traced hosts safety owner meaning allocators usizeBits budgets queries depth)
  exact prepared_miss_map outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits _ _ debug (view source)
    (Interner.constructorCode.operationRequest opcode source.items) before _ _ id
    (mapReturn (Publication.Effects.mapAllocator Prod.fst)) (mapReturn_outcome _) (fun leading => congrFun forwarded leading)
    (borrowed_miss_projected ops allocate safety owner meaning base growth usizeBits depth outerOps outerAllocate outerBase outerGrowth
      debug opcode source before good)

theorem constant_miss_bound (value : Contract.Yul.Word)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (good : Good ⟨0, 0, 0⟩ [] before) :
    PreparedMiss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) before
      ((unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)).constant value debug (ChildTrace.erase before))
      (mapReturn (Publication.Effects.mapAllocator Prod.fst)) := by
  have forwarded := congrArg (fun family => family.constant value debug before)
    (unfold_step_traced hosts safety owner meaning allocators usizeBits budgets queries depth)
  exact prepared_miss_map outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits _ _ debug ⟨0, 0, 0⟩
    (Interner.constructorCode.constantRequest value) before _ _ id
    (mapReturn (Publication.Effects.mapAllocator Prod.fst)) (mapReturn_outcome _) (fun leading => congrFun forwarded leading)
    (constant_miss_projected ops allocate safety owner meaning base growth usizeBits depth outerOps outerAllocate outerBase outerGrowth
      debug value before good)

/-- Materialization uses the same source constant route; the old expression ID
does not select a different native constructor or resource observation. -/
theorem materialize_miss_bound (id : NodeId) (value : Contract.Yul.Word)
    (before : ChildTrace.TracedWorld σ ProtocolEvent) (good : Good ⟨0, 0, 0⟩ [] before) :
    PreparedMiss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value) before
      ((unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)).materialize id value debug (ChildTrace.erase before))
      (mapReturn (Publication.Effects.mapAllocator Prod.fst)) := by
  rw [materialize_forwarded]
  exact constant_miss_bound ops allocate safety owner meaning base growth usizeBits depth outerOps outerAllocate outerBase outerGrowth
    hosts budgets allocators queries debug value before good

/-- Actual literal preparation and original argument retirement surround the
same native successor miss; the binding changes no source request or history. -/
theorem operation_miss_bound (opcode : Opcode) (values : List NodeId)
    (before prepared : ChildTrace.TracedWorld σ ProtocolEvent) (source : View)
    (valid : Valid before.memory) (ran : Arguments.prepare values before = (.ok source, prepared)) :
    PreparedMiss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug source
      (Interner.constructorCode.operationRequest opcode values) prepared
      ((unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)).operation opcode values debug (ChildTrace.erase before))
      (fun result => mapReturn (Publication.Effects.mapAllocator Prod.fst)
        (if values.isEmpty then result else retire before.memory.memory.nextId result)) := by
  have forwarded := congrArg (fun family => family.operation opcode values debug before)
    (unfold_step_traced hosts safety owner meaning allocators usizeBits budgets queries depth)
  exact prepared_miss_map outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits _ _ debug source
    (Interner.constructorCode.operationRequest opcode values) prepared _ _ _
    (mapReturn (Publication.Effects.mapAllocator Prod.fst)) (mapReturn_outcome _) (fun leading => congrFun forwarded leading)
    (operation_miss_projected ops allocate safety owner meaning base growth usizeBits depth outerOps outerAllocate outerBase outerGrowth
      debug opcode values before prepared source valid ran)

theorem local_miss_bound (opcode : Opcode) (source : ArgumentSlice) (target : View)
    (left right repeated : NodeId) (selected : Nat) (first : Bool)
    (before prepared : ChildTrace.TracedWorld σ ProtocolEvent)
    (shape : source.items = [left, right]) (good : Good (view source) source.items before)
    (inside : first = true → selected < 2)
    (ran : LocalArguments.zigLocal (view source) selected repeated first before = (.ok target, prepared)) :
    PreparedMiss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug target
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])) prepared
      ((unfold ops allocate safety owner meaning base growth usizeBits (depth + 1)).localOperation
        opcode source selected repeated first debug (ChildTrace.erase before))
      (fun result => mapReturn (Publication.Effects.mapAllocator Prod.fst) (retire before.memory.memory.nextId result)) := by
  have forwarded := congrArg (fun family => family.localOperation opcode source selected repeated first debug before)
    (unfold_step_traced hosts safety owner meaning allocators usizeBits budgets queries depth)
  exact prepared_miss_map outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits _ _ debug target
    (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])) prepared _ _ _
    (mapReturn (Publication.Effects.mapAllocator Prod.fst)) (mapReturn_outcome _) (fun leading => congrFun forwarded leading)
    (local_miss_projected ops allocate safety owner meaning base growth usizeBits depth outerOps outerAllocate outerBase outerGrowth
      debug opcode source target left right repeated selected first before prepared shape good inside ran)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
