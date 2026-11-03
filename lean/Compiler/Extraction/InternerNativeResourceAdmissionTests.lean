/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeResourceDispatch
import Compiler.Extraction.InternerNativeAllocationAdmissionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeResourceAdmissionTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open NativeRecursion Recursive Insertion.Native
open RecursiveTests (debug)
open Caller.ProtocolTrace (ProtocolEvent)

abbrev prior := NativeAllocationAdmissionTests.before
abbrev child := NativeAllocationAdmissionTests.child

/-- Observe the same actual constant constructor used by the allocation
counterexample. Its protocol events come from the existing recursive recorder. -/
def capture (safety : Bool) :=
  (ProtocolTrace.unfold NativeAllocationAdmissionTests.ops ReachablePrefixTests.allocate safety 6 Insertion.Tests.model
    (ReachablePrefixTests.base safety) (some CallerGrowingChainTests.growth) 64 1).constant 1 debug

theorem capture_native (safety : Bool) (before : World (Publication.Effects Nat)) :
    ((capture safety before []).1, (capture safety before []).2.native.world) = child safety before := by
  have same := congrArg (fun family => family.constant 1 debug before)
    (ProtocolTrace.unfold_erases NativeAllocationAdmissionTests.ops ReachablePrefixTests.allocate safety 6 Insertion.Tests.model
      (ReachablePrefixTests.base safety) (some CallerGrowingChainTests.growth) 64 1 [])
  exact same

def recorded (safety : Bool) := ChildTrace.record (child safety) (fun before => (capture safety before []).2.events)
def before (safety permitted : Bool) := ChildTrace.restore ([] : List ProtocolEvent) (prior safety permitted)
def events (safety permitted : Bool) := (capture safety (prior safety permitted) []).2.events

theorem recorded_grows (safety : Bool) : Resource.Grows ChildTrace.history (recorded safety) := by
  intro world
  exact ⟨(capture safety (ChildTrace.erase world) []).2.events, rfl⟩

theorem recorded_history (safety permitted : Bool) :
    ChildTrace.history (recorded safety (before safety permitted)).2 = events safety permitted := by
  change ChildTrace.history (before safety permitted) ++
    (capture safety (ChildTrace.erase (before safety permitted)) []).2.events = events safety permitted
  rw [show ChildTrace.erase (before safety permitted) = prior safety permitted from ChildTrace.erase_restore _ _]
  rfl

theorem recorded_result (safety permitted : Bool) :
    (recorded safety (before safety permitted)).1 = if permitted then .ok 5 else .error (.language .outOfMemory) := by
  simp only [recorded, before, ChildTrace.record, ChildTrace.erase_restore]
  cases permitted
  · exact NativeAllocationAdmissionTests.refused safety
  · exact NativeAllocationAdmissionTests.successful safety

/-- Both actual allocation outcomes have admission, with no success premise. -/
theorem recorded_admitted (safety permitted : Bool) (trailing : List ProtocolEvent) :
    Resource.Admitted ChildTrace.history (events safety permitted ++ trailing) (recorded safety) (before safety permitted) := by
  simpa only [recorded_history] using Resource.Admitted.captured ChildTrace.history (recorded safety) (before safety permitted) trailing

def itemDecision : ProtocolEvent → Option Bool
  | .insertion (.attempt .item _ (.ok accepted)) => some accepted
  | _ => none

theorem actual_item_decision (safety permitted : Bool) :
    (events safety permitted).filterMap itemDecision = [permitted] := by
  cases safety <;> cases permitted <;> insertion_kernel_rfl

/-- A fixed stream cannot admit both hidden allocation outcomes at the same
position. An OOM event is distinct from the successful event, not omitted. -/
theorem wrong_stream_rejected (safety permitted : Bool) :
    ¬ Resource.Admitted ChildTrace.history (events safety (!permitted)) (recorded safety) (before safety permitted) := by
  intro admitted
  have included : ChildTrace.history (recorded safety (before safety permitted)).2 <+: events safety (!permitted) := admitted
  rw [recorded_history] at included
  obtain ⟨tail, same⟩ := included
  have decisions := congrArg (List.filterMap itemDecision) same
  rw [List.filterMap_append, actual_item_decision, actual_item_decision] at decisions
  cases permitted <;> cases (List.cons.inj decisions).1

/-- The old structural counterexample is retained: choosing a fixed resource
stream separates its inputs without claiming that the structural frame did. -/
theorem same_graph_both_outcomes (safety : Bool) :
    (prior safety true).graph = (prior safety false).graph ∧
    (recorded safety (before safety true)).1 = .ok 5 ∧
    (recorded safety (before safety false)).1 = .error (.language .outOfMemory) :=
  ⟨NativeAllocationAdmissionTests.same_graph safety, recorded_result safety true, recorded_result safety false⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeResourceAdmissionTests
