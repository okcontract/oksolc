/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerConstructorItemReturnTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native
open CallerGrowingChainTests (parent cells startId ops growth)
open CallerInputTests (values)

theorem operation_fields (opcode : Opcode) (arguments : List NodeId) (metadata : AssemblyItem.Fields.Values) :
    AssemblyClone.NativeFields.values (input (Interner.constructorCode.operationRequest opcode arguments).item metadata) =
      AssemblyItem.Initializers.operation opcode metadata := input_fields _ _

theorem constant_fields (word : Contract.Yul.Word) (metadata : AssemblyItem.Fields.Values) :
    AssemblyClone.NativeFields.values (input (Interner.constructorCode.constantRequest word).item metadata) =
      AssemblyItem.Initializers.constant word metadata := input_fields _ _

theorem materialize_forwarded (external : External σ) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives σ)
    (q : Caller.Queries) (id : NodeId) (word : Contract.Yul.Word) (metadata : AssemblyItem.Fields.Values) :
    materialize external budget allocator p q id word metadata =
      invoke external budget allocator p q ⟨0, 0, 0⟩ (Interner.constructorCode.constantRequest word) metadata := rfl

def blank : World Nat := ⟨Interner.observedHeap [] (fun _ => none), ⟨fun _ => none, {}, 17⟩⟩
def allocatedBlank : World Nat := { blank with memory := { blank.memory with memory :=
  ⟨[(0, ⟨16, AssemblyItem.viewType, [], true, true⟩)], 1, 240⟩ } }
def exhausted : World Nat := { blank with memory := { blank.memory with memory :=
  { blank.memory.memory with nextAddress := Compiler.ZigAir.Memory.addressLimit - 8 } } }

/-- Rejected debug metadata retains the allocated, uninitialized local. Stack
exhaustion retains the original state. Neither path evaluates caller callbacks. -/
theorem preparation_rejections :
    prepare (request true).item AssemblyItem.Initializers.Tests.invalidDebug blank =
      (.error (.memory (.preparation (.memory .malformed))), allocatedBlank) ∧
    prepare (request true).item debug exhausted =
      (.error (.memory (.preparation (.memory .outOfMemory))), exhausted) := by
  exact ⟨by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem rejected_before_call (external : External Nat) (budget allocator : Nat)
    (p : Compiler.ZigAir.Memory.Address → AssemblyClone.NativeFields.ItemValue → Primitives Nat)
    (q : Caller.Queries) :
    operation external budget allocator p q ⟨99, 8, 0⟩ 254 [] AssemblyItem.Initializers.Tests.invalidDebug blank =
      (.error (.memory (.preparation (.memory .malformed))), ⟨allocatedBlank, { lookup := none }⟩) ∧
    operation external budget allocator p q ⟨99, 8, 0⟩ 254 [] debug exhausted =
      (.error (.memory (.preparation (.memory .outOfMemory))), ⟨exhausted, { lookup := none }⟩) :=
  ⟨invoke_rejected _ _ _ _ _ _ _ _ _ _ _ preparation_rejections.1,
    invoke_rejected _ _ _ _ _ _ _ _ _ _ _ preparation_rejections.2⟩

def missingContainer (safety empty : Bool) := (taken safety empty).2.world.memory.memory.nextId
theorem missing_owner (safety empty : Bool) :
    checkedCount (taken safety empty).2.world.memory.memory (missingContainer safety empty) (cells safety empty 4) =
      .error (.memory .unallocated) := by
  cases safety <;> cases empty <;> insertion_kernel_rfl

def rejected (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :=
  operation (Publication.external ops.arguments) 160 7
    (fun address input => callerPrimitives ops reserve safety 7 (missingContainer safety empty) (parent empty) address
      Insertion.Tests.model input (seed empty find) (some growth))
    Interner.Queries.queries (parent empty) 254 (values empty) debug (before safety empty)

/-- Native count rejection after the actual dispatcher retains both constructor
and callee frames, detached lookup and normalized owner. -/
theorem rejection_retains_frames (safety empty : Bool) (find : Recursive.Find (Publication.Effects Nat)) :
    rejected safety empty find = (.error (.language .safetyFault),
      ⟨(taken safety empty).2.world, ⟨some (lookup empty), some (normalized empty), true⟩⟩) ∧
    Memory.SliceValid 7 (rejected safety empty find).2.world.memory.heap (normalized empty) ∧
    AssemblyClone.NativeFields.Represents (rejected safety empty find).2.world.memory.memory (itemSource empty) (native empty) ∧
    ordinary (rejected safety empty find).1 = false := by
  have incoming := entry safety empty
  have prior := CallerGrowingChainTests.initialized_prefix safety empty 4 (by decide)
  have calls := prefix_results safety empty
  have facts := constructed_graph safety empty
  have room : Interner.Queries.queries.atCapacity (constructed safety empty).graph = false := by
    rw [Interner.Queries.capacity_exact _ _ facts.projected, prior.count]; decide
  have initialized : Caller.initLookup (Publication.external ops.arguments) 160 7 (parent empty)
      ⟨(constructed safety empty).memory.memory.nextId, 0, 2⟩ (request empty)
      ⟨{ constructed safety empty with memory := { (constructed safety empty).memory with memory := stack safety empty } }, { lookup := none }⟩ =
        (.ok (values empty), (prepared safety empty).2) := by
    rw [calls.2.1]; exact Prod.ext calls.2.2.2.1 rfl
  have finished := incoming.rejected_completed ops reserve safety 7 (missingContainer safety empty) (parent empty) (itemSource empty)
    Insertion.Tests.model (request empty) (values empty) (native empty) (key empty) (normalized empty) (lookup empty)
    (constructed safety empty) (taken safety empty).2 true (cells safety empty 4) (some growth)
    facts.projected (.memory .unallocated) (missing_owner safety empty)
  have routed := incoming.find_after_simplify ops reserve safety 160 7 (missingContainer safety empty) (parent empty) (itemSource empty)
    Insertion.Tests.model (native empty) (seed empty find) Interner.Queries.queries (request empty) (constructed safety empty)
    (taken safety empty).2.world (stack safety empty) _ (values empty) (prepared safety empty).2 (taken safety empty).2
    (key empty) (normalized empty) (lookup empty) (some growth) room calls.2.2.1 initialized rfl (made_key empty)
    (by rw [(construction safety empty).graph]; exact calls.2.2.2.2.2.2) (Prod.ext calls.2.2.2.2.1 rfl) rfl (simplified safety empty find)
  rw [finished] at routed
  have outer := invoke_prepared (Publication.external ops.arguments) 160 7
    (fun address input => callerPrimitives ops reserve safety 7 (missingContainer safety empty) (parent empty) address
      Insertion.Tests.model input (seed empty find) (some growth))
    Interner.Queries.queries (parent empty) (request empty) debug (before safety empty) (constructed safety empty) (itemSource empty) calls.1
  simp only [native] at routed
  rw [routed] at outer
  change rejected safety empty find = _ at outer
  refine ⟨outer, ?_, ?_, ?_⟩
  · rw [outer]; exact incoming.origin.held.2.1
  · rw [outer]; exact incoming.item
  · rw [outer]; rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.Tests
