/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorPreparedMiss
import Compiler.Extraction.InternerRecursiveProtocolTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Caller.ProtocolTrace ConstructorItem.ProtocolTrace

attribute [local irreducible] unfold ItemMiss PreparedMiss ConstructorItem.ProtocolTrace.item
  ConstructorItem.ProtocolTrace.literal ConstructorItem.ProtocolTrace.namedLocal

variable (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety : Bool) (owner : Nat) (meaning : Meaning) (base : PairInput.Context (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ)) (usizeBits depth : Nat)
    (outerOps : Insertion.Operations (ChildTrace.Recorded σ ProtocolEvent))
    (outerAllocate : Backing.Registry.Allocate (ChildTrace.Recorded σ ProtocolEvent))
    (outerBase : PairInput.Context (Publication.Effects (ChildTrace.Recorded σ ProtocolEvent)))
    (outerGrowth : Option (Growth.Registered.Callbacks (ChildTrace.Recorded σ ProtocolEvent)))
    (debug : AssemblyItem.Fields.Values)

/-- The borrowed constructor field consumes the full item/caller return proof
with the actual finite children and their computed observations. Parent host
bindings and proper-child preservation remain the same explicit obligations. -/
theorem borrowed_miss_projected (opcode : Opcode) (source : ArgumentSlice) :
    ItemMiss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug (view source)
      (Interner.constructorCode.operationRequest opcode source.items)
      ((step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
        (children ops allocate safety owner meaning base growth usizeBits depth)
        (ChildTrace.liftObservations (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))).borrowedOperation
          source.address opcode source.items debug) :=
  item_miss_traced outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug (view source)
    (Interner.constructorCode.operationRequest opcode source.items)

/-- Constant construction uses the same complete item return. No literal
argument allocation or supplied child event list is inserted into this route. -/
theorem constant_miss_projected (value : Contract.Yul.Word) :
    ItemMiss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value)
      ((step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
        (children ops allocate safety owner meaning base growth usizeBits depth)
        (ChildTrace.liftObservations (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))).constant value debug) :=
  item_miss_traced outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug ⟨0, 0, 0⟩
    (Interner.constructorCode.constantRequest value)

/-- The source materializer forwards to the same constant field; its old ID
cannot replace the new value, debug fields or constructor-local input. -/
theorem materialize_miss_projected (id : NodeId) (value : Contract.Yul.Word) :
    ItemMiss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug ⟨0, 0, 0⟩
      (Interner.constructorCode.constantRequest value)
      ((step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
        (children ops allocate safety owner meaning base growth usizeBits depth)
        (ChildTrace.liftObservations (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))).materialize id value debug) :=
  constant_miss_projected ops allocate safety owner meaning base growth usizeBits depth outerOps outerAllocate outerBase outerGrowth debug value

/-- The literal field now consumes the full miss after its actual argument
initializer. The existing preparation proof discharges its input contract. -/
theorem operation_miss_projected (opcode : Opcode) (values : List NodeId)
    (before prepared : ChildTrace.TracedWorld σ ProtocolEvent) (source : View)
    (valid : Valid before.memory) (ran : Arguments.prepare values before = (.ok source, prepared)) :
    PreparedMiss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug source
      (Interner.constructorCode.operationRequest opcode values) prepared
      ((step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
        (children ops allocate safety owner meaning base growth usizeBits depth)
        (ChildTrace.liftObservations (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))).operation
          opcode values debug before)
      (fun result => if values.isEmpty then result else retire before.memory.memory.nextId result) :=
  literal_miss_traced outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug opcode values before prepared source valid ran

/-- The named-local field selects its actual two-word source branch, derives
copy/optional-write preparation and returns the complete miss through the local
allocation's original mark. No prepared Good or wrapper projection is supplied. -/
theorem local_miss_projected (opcode : Opcode) (source : ArgumentSlice) (target : View)
    (left right repeated : NodeId) (selected : Nat) (first : Bool)
    (before prepared : ChildTrace.TracedWorld σ ProtocolEvent)
    (shape : source.items = [left, right]) (good : Good (view source) source.items before)
    (inside : first = true → selected < 2)
    (ran : LocalArguments.zigLocal (view source) selected repeated first before = (.ok target, prepared)) :
    PreparedMiss outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
      (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
      (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug target
      (Interner.constructorCode.operationRequest opcode (if first then [left, right].set selected repeated else [left, right])) prepared
      ((step outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
        (children ops allocate safety owner meaning base growth usizeBits depth)
        (ChildTrace.liftObservations (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)))).localOperation
          opcode source selected repeated first debug before)
      (retire before.memory.memory.nextId) := by
  have traced := local_miss_traced outerOps outerAllocate safety owner meaning outerBase outerGrowth usizeBits
    (NativeRecursion.unfold (callerContext ops allocate safety owner meaning base growth) owner usizeBits depth)
    (observe (unfold ops allocate safety owner meaning base growth usizeBits depth)) debug opcode (view source) target
    left right repeated selected first before prepared (by simpa only [shape] using good) inside ran
  simpa only [step, stepWith, atDebug, ConstructorItem.ProtocolTrace.constructors, shape] using traced

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion.ProtocolTrace
