/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerAllocationResourceMiss
import Compiler.Extraction.InternerNativeAllocationTraceTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeAllocationEntryTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open NativeRecursion Recursive NativeAllocationTraceTests Insertion.Native
open Caller.ProtocolTrace (ProtocolEvent)
open RecursiveTests (debug)

def atHistory (safety permitted : Bool) (earlier : List ProtocolEvent) :=
  ChildTrace.restore earlier (NativeAllocationAdmissionTests.before safety permitted)

/-- Both actual outcomes retain their results under arbitrary earlier native
history, including a caller prefix unrelated to that history's length. -/
theorem history_retains_outcome (safety permitted : Bool) (earlier : List ProtocolEvent) :
    (recorded safety (atHistory safety permitted earlier)).1 =
      if permitted then .ok 5 else .error (.language .outOfMemory) := by
  have same : (recorded safety (atHistory safety permitted earlier)).1 =
      (recorded safety (before safety permitted)).1 := by
    simp only [recorded, ChildTrace.record, atHistory, before, NativeResourceAdmissionTests.before,
      ChildTrace.erase_restore]
  rw [same]
  exact recorded_result safety permitted

/-- Replay can begin after an arbitrary amount of prior native history and
then reach a later child. Neither prefix is assumed empty or equal in length. -/
theorem later_entry (safety permitted : Bool) (earlier between leading trailing : List ProtocolEvent) :
    AllocationTrace.enter (AllocationTrace.rebase leading earlier.length
      (earlier ++ between ++ events safety permitted ++ trailing))
      (cursorGraph (MissStream.childCursor leading.length (atHistory safety permitted earlier))
        (atHistory safety permitted (earlier ++ between))) =
      (.ok ((before safety permitted).memory.memory.nextId, (before safety permitted).memory.memory.nextAddress),
        { (before safety permitted).graph with allocationCursor := leading.length + between.length + 1 }) := by
  have admitted : Resource.Admitted ChildTrace.history
      (earlier ++ between ++ events safety permitted ++ trailing) (recorded safety)
      (atHistory safety permitted (earlier ++ between)) := by
    change (earlier ++ between) ++ events safety permitted <+: _
    exact ⟨trailing, rfl⟩
  have projected := AllocationTrace.enter_relative_admitted (capture safety) (marked safety)
    leading (earlier ++ between ++ events safety permitted ++ trailing)
    (atHistory safety permitted earlier) (atHistory safety permitted (earlier ++ between))
    (by change earlier.length ≤ (earlier ++ between).length; simp only [List.length_append]; omega) admitted
  simpa only [MissStream.childCursor, atHistory, ChildTrace.history, ChildTrace.restore,
    World.mapEffects, Session.mapEffects, Publication.Effects.mapAllocator, List.length_append,
    Nat.add_sub_assoc (Nat.le_add_right _ _), Nat.add_sub_cancel_left] using projected

/-- The real constant capture factors through the same entry/body bind used
by the all-five-route source contract; its native allocation is unchanged. -/
theorem split_real_capture (safety : Bool) :
    recorded safety = (AllocationTrace.enterNative >>= fun _ => AllocationTrace.record
      ((AllocationTrace.body NativeAllocationAdmissionTests.ops ReachablePrefixTests.allocate safety 6 Insertion.Tests.model
        (ReachablePrefixTests.base safety) (some CallerGrowingChainTests.growth) 64 0).constant 1 debug)) := by
  have prefixed : AllocationTrace.Prefixes
      (AllocationTrace.body NativeAllocationAdmissionTests.ops ReachablePrefixTests.allocate safety 6 Insertion.Tests.model
        (ReachablePrefixTests.base safety) (some CallerGrowingChainTests.growth) 64 0) :=
    AllocationTrace.step_prefix _ _ _ _ _ _ _ _ _ _
  apply AllocationTrace.record_mark
  intro world earlier leading
  exact congrArg (fun family => family.constant 1 debug world) (prefixed earlier leading)

/-- A caller-relative cursor cannot be used against raw history. The common
rebase is observable even when every native entry value is otherwise correct. -/
theorem raw_stream_rejected (heap : Interner.Heap) (key : Key) (id address : Nat) :
    (AllocationTrace.enter [.publicationProbe key true, .publicationProbe key false, .nativeEntry id address]
      { heap with allocationCursor := 1 }).1 = .error .safetyFault ∧
    (AllocationTrace.enter (AllocationTrace.rebase [.publicationProbe key true] 2
      [.publicationProbe key true, .publicationProbe key false, .nativeEntry id address])
      { heap with allocationCursor := 1 }).1 = .ok (id, address) := ⟨rfl, rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeAllocationEntryTests
