/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeAllocationTrace
import Compiler.Extraction.InternerInsertionCheckpoint
import Compiler.Extraction.InternerNativeFrameInductionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeAllocationTraceTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open NativeRecursion Recursive Insertion.Native
open RecursiveTests (debug)
open Caller.ProtocolTrace (ProtocolEvent)

def captures (safety : Bool) (depth : Nat) :=
  AllocationTrace.unfold NativeAllocationAdmissionTests.ops ReachablePrefixTests.allocate safety 6 Insertion.Tests.model
    (ReachablePrefixTests.base safety) (some CallerGrowingChainTests.growth) 64 depth

def capture (safety : Bool) := (captures safety 1).constant 1 debug
def recorded (safety : Bool) := ChildTrace.record (ConstructorItem.ProtocolTrace.eraseCapture [] (capture safety))
  (fun before => (capture safety before []).2.events)
abbrev before := NativeResourceAdmissionTests.before
def events (safety permitted : Bool) := (capture safety (NativeAllocationAdmissionTests.before safety permitted) []).2.events

theorem marked (safety : Bool) : AllocationTrace.Begins (capture safety) :=
  (AllocationTrace.unfold_marked NativeAllocationAdmissionTests.ops ReachablePrefixTests.allocate safety 6 Insertion.Tests.model
    (ReachablePrefixTests.base safety) (some CallerGrowingChainTests.growth) 64 1).constant 1 debug

theorem capture_native (safety : Bool) (world : World (Publication.Effects Nat)) :
    ((capture safety world []).1, (capture safety world []).2.native.world) = NativeAllocationAdmissionTests.child safety world :=
  congrArg (fun family => family.constant 1 debug world)
    (AllocationTrace.unfold_erases NativeAllocationAdmissionTests.ops ReachablePrefixTests.allocate safety 6 Insertion.Tests.model
      (ReachablePrefixTests.base safety) (some CallerGrowingChainTests.growth) 64 1 [])

theorem recorded_result (safety permitted : Bool) :
    (recorded safety (before safety permitted)).1 = if permitted then .ok 5 else .error (.language .outOfMemory) := by
  change (capture safety (ChildTrace.erase (before safety permitted)) []).1 = _
  rw [show ChildTrace.erase (before safety permitted) = NativeAllocationAdmissionTests.before safety permitted
    from ChildTrace.erase_restore _ _]
  rw [show (capture safety (NativeAllocationAdmissionTests.before safety permitted) []).1 =
    (NativeAllocationAdmissionTests.child safety (NativeAllocationAdmissionTests.before safety permitted)).1 from
      congrArg Prod.fst (capture_native safety _)]
  cases permitted
  · exact NativeAllocationAdmissionTests.refused safety
  · exact NativeAllocationAdmissionTests.successful safety

theorem recorded_admitted (safety permitted : Bool) (trailing : List ProtocolEvent) :
    Resource.Admitted ChildTrace.history (events safety permitted ++ trailing) (recorded safety) (before safety permitted) := by
  simpa only [recorded, before, NativeResourceAdmissionTests.before, ChildTrace.record, ChildTrace.history,
    ChildTrace.erase_restore, ChildTrace.restore, List.nil_append, events] using
    Resource.Admitted.captured ChildTrace.history (recorded safety) (before safety permitted) trailing

/-- Richer observation keeps the previously derived native parent frame on
both allocation outcomes. -/
theorem parent_retained (safety permitted : Bool) :
    NativeAllocationAdmissionTests.frame safety
      (capture safety (NativeAllocationAdmissionTests.before safety permitted) []).2.native.world := by
  rw [show (capture safety (NativeAllocationAdmissionTests.before safety permitted) []).2.native.world =
    (NativeAllocationAdmissionTests.child safety (NativeAllocationAdmissionTests.before safety permitted)).2 from
      congrArg Prod.snd (capture_native safety _)]
  exact NativeFrameInductionTests.parent_retained safety permitted

/-- Adding identity slots does not admit the opposite allocation outcome. -/
theorem wrong_stream_rejected (safety permitted : Bool) :
    ¬ Resource.Admitted ChildTrace.history (events safety (!permitted)) (recorded safety) (before safety permitted) := by
  change ¬ (events safety permitted <+: events safety (!permitted))
  cases safety <;> cases permitted <;> decide +kernel

/-- Replay consumes the actual entry on both successful creation and OOM. -/
theorem replay_entry (safety permitted : Bool) (trailing : List ProtocolEvent) :
    AllocationTrace.enter (events safety permitted ++ trailing) (cursorGraph (fun world => (ChildTrace.history world).length) (before safety permitted)) =
      (.ok ((before safety permitted).memory.memory.nextId, (before safety permitted).memory.memory.nextAddress),
        { (before safety permitted).graph with allocationCursor := 1 }) :=
  AllocationTrace.enter_admitted (capture safety) (marked safety) _ _ (recorded_admitted safety permitted trailing)

/-- The existing real extra stack allocation is rejected by the original
entry stream, although the old protocol-only histories agree. -/
theorem shifted_rejected (safety : Bool) :
    ¬ Resource.Admitted ChildTrace.history (events safety true) (recorded safety)
      (NativeAllocationIdentityTests.before safety true) := by
  intro admitted
  have ids := AllocationTrace.admitted_identity (capture safety) (capture safety) (marked safety) (marked safety)
    (events safety true) (before safety true) (NativeAllocationIdentityTests.before safety true) rfl
    (by simpa only [List.append_nil] using recorded_admitted safety true []) admitted
  have shifted := (Arguments.prepare_success [0] (NativeAllocationAdmissionTests.before safety true)
    (NativeAllocationIdentityTests.extra safety) _ (NativeAllocationAdmissionTests.admitted_frame safety true).1.2.1.1
    (NativeAllocationIdentityTests.extra_prepared safety)).counter
  have same := ids.1
  change (NativeAllocationAdmissionTests.before safety true).memory.memory.nextId =
    (NativeAllocationIdentityTests.extra safety).memory.memory.nextId at same
  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at shifted
  omega

def isEntry : ProtocolEvent → Bool
  | .nativeEntry _ _ => true
  | _ => false

/-- The existing ISZERO request reaches a real constant child. The marked
recursive observer retains both entries, not only the outer wrapper. -/
theorem nested_entries (safety : Bool) :
    (((captures safety 2).operation (Interner.buildOpcode .ISZERO) [4] debug (NativeAllocationAdmissionTests.before safety true) []).2.events.filter isEntry).length = 2 := by
  cases safety <;> insertion_kernel_rfl

def insertionIds (observed : List ProtocolEvent) : List Nat := observed.filterMap fun
  | .nativeInsertion id _ => some id
  | _ => none

/-- The checkpoint sees the allocation state after item/scratch preparation,
on both successful creation and actual allocator refusal. -/
theorem reached_insertion (safety permitted : Bool) : insertionIds (events safety permitted) = [30] := by
  cases safety <;> cases permitted <;> decide +kernel

/-- The real extra stack allocation shifts the reached insertion checkpoint.
The model cannot reuse the old identity even though protocol decisions agree. -/
theorem shifted_insertion (safety : Bool) :
    insertionIds (capture safety (NativeAllocationIdentityTests.extra safety) []).2.events = [31] := by
  cases safety <;> decide +kernel

theorem insertion_is_foreign (id address : Nat) :
    Interner.InvocationTrace.normalization (.nativeInsertion id address : ProtocolEvent) = .foreign ∧
    Interner.InvocationTrace.insertion (.nativeInsertion id address : ProtocolEvent) = .foreign := ⟨rfl, rfl⟩

/-- Constructor and insertion checkpoints are distinct, and cannot consume
each other's stream positions. Missing checkpoints also reject explicitly. -/
theorem checkpoint_kind_rejected (heap : Interner.Heap) (id address : Nat) :
    (AllocationTrace.insertionRead [.nativeEntry id address] { heap with allocationCursor := 0 }).1 = .error .safetyFault ∧
    (AllocationTrace.enter [.nativeInsertion id address] { heap with allocationCursor := 0 }).1 = .error .safetyFault ∧
    AllocationTrace.insertionRead [] heap = (.error .safetyFault, { heap with allocationCursor := 1 }) := by
  simp only [AllocationTrace.insertionRead, AllocationTrace.enter, List.getElem?_cons_zero,
    List.getElem?_nil, List.length_nil, Nat.zero_add, and_self]

theorem entry_is_foreign (id address : Nat) :
    Interner.InvocationTrace.normalization (.nativeEntry id address : ProtocolEvent) = .foreign ∧
    Interner.InvocationTrace.insertion (.nativeEntry id address : ProtocolEvent) = .foreign := ⟨rfl, rfl⟩

theorem replay_rejects_foreign (heap : Interner.Heap) (key : Key) :
    (AllocationTrace.enter [.publicationProbe key true] { heap with allocationCursor := 0 }).1 = .error .safetyFault := rfl

theorem replay_rejects_missing (heap : Interner.Heap) :
    AllocationTrace.enter [] heap = (.error .safetyFault, { heap with allocationCursor := 1 }) := by
  simp only [AllocationTrace.enter, List.getElem?_nil, List.length_nil, Nat.zero_add]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeAllocationTraceTests
