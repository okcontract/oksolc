/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeResourceAdmissionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeAllocationIdentityTests
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open NativeRecursion Recursive Insertion.Native
open Caller.ProtocolTrace (ProtocolEvent)

/- Finite protocol equality is used by the closed kernel check below. -/
deriving instance DecidableEq for NormalizationOwnership.Trace.Event
deriving instance DecidableEq for Storage.Trace.Event
deriving instance DecidableEq for Interner.InvocationTrace.Event

abbrev prior := NativeAllocationAdmissionTests.before
abbrev child := NativeAllocationAdmissionTests.child
abbrev capture := NativeResourceAdmissionTests.capture
abbrev recorded := NativeResourceAdmissionTests.recorded

/-- One real, unrelated stack initializer shifts fresh typed allocation IDs.
The native child and every host callback remain the same. -/
def extra (safety : Bool) := (Arguments.prepare [0] (prior safety true)).2
def native (safety shifted : Bool) := if shifted then extra safety else prior safety true
def before (safety shifted : Bool) := ChildTrace.restore ([] : List ProtocolEvent) (native safety shifted)
def frame (safety : Bool) (world : ChildTrace.TracedWorld Nat ProtocolEvent) :=
  NativeAllocationAdmissionTests.frame safety (ChildTrace.erase world)
def events (safety : Bool) := (capture safety (prior safety true) []).2.events
def lastAddress (graph : Interner.Heap) :=
  graph.representatives.bind (fun cells => cells.getLast?.map Storage.Cell.itemAddress)

theorem extra_prepared (safety : Bool) : Arguments.prepare [0] (prior safety true) =
    (.ok ⟨(prior safety true).memory.memory.nextId, 0, 1⟩, extra safety) := by
  cases safety <;> insertion_kernel_rfl

/-- The extra initializer preserves the actual parent through the existing
allocation frame, including source provenance and normalized ownership. -/
theorem before_frame (safety shifted : Bool) : frame safety (before safety shifted) := by
  simp only [frame, before, ChildTrace.erase_restore]
  cases shifted with
  | false => exact NativeAllocationAdmissionTests.admitted_frame safety true
  | true =>
    have initial := NativeAllocationAdmissionTests.admitted_frame safety true
    exact initial.arguments (Arguments.prepare_success [0] _ _ _ initial.1.2.1.1 (extra_prepared safety)) trivial

theorem initial_graph (safety shifted : Bool) : (native safety shifted).graph = (prior safety true).graph := by
  cases shifted
  · rfl
  · exact (Arguments.prepare_success [0] _ _ _
      (NativeAllocationAdmissionTests.admitted_frame safety true).1.2.1.1 (extra_prepared safety)).graph

/-- Full protocol events agree, including reached ownership states and
results. Equality is checked by the kernel, not a native evaluator. -/
theorem histories_equal (safety shifted : Bool) :
    (capture safety (native safety shifted) []).2.events = events safety := by
  cases shifted
  · rfl
  · cases safety <;> decide +kernel

theorem native_result (safety shifted : Bool) : (child safety (native safety shifted)).1 = .ok 5 := by
  cases shifted
  · exact NativeAllocationAdmissionTests.successful safety
  · cases safety <;> insertion_kernel_rfl

/-- Successful native results retain different fresh allocation identities
in the observed representative graph, despite equal protocol decisions. -/
theorem native_address (safety shifted : Bool) :
    lastAddress (child safety (native safety shifted)).2.graph = some (if shifted then 31 else 30) := by
  cases shifted <;> cases safety <;> insertion_kernel_rfl

theorem recorded_history (safety shifted : Bool) :
    ChildTrace.history (recorded safety (before safety shifted)).2 = events safety := by
  simp only [recorded, NativeResourceAdmissionTests.recorded, before, ChildTrace.record, ChildTrace.erase_restore]
  exact histories_equal safety shifted

theorem both_admitted (safety shifted : Bool) :
    Resource.Admitted ChildTrace.history (events safety) (recorded safety) (before safety shifted) := by
  change ChildTrace.history (recorded safety (before safety shifted)).2 <+: events safety
  rw [recorded_history]
  exact List.prefix_refl _

theorem recorded_result (safety shifted : Bool) :
    (recorded safety (before safety shifted)).1 = .ok 5 := by
  simp only [recorded, NativeResourceAdmissionTests.recorded, before, ChildTrace.record, ChildTrace.erase_restore]
  exact native_result safety shifted

/-- Protocol-stream admission plus the structural frame still cannot supply
an exact shared child model. The same actual child succeeds on both admitted
inputs, but its reached graphs differ at a native item address. This is an
obstruction to an unrestricted proof interface, not a compiler bug. A stronger
admission domain must derive allocation-identity agreement as well. -/
theorem no_cursor_model (safety : Bool) (position : Nat) :
    ¬ ∃ model : Interner.Action NodeId,
      Resource.Projects ChildTrace.history (events safety)
        (cursorGraph (MissStream.childCursor position (before safety false)))
        (frame safety) (recorded safety) model := by
  rintro ⟨model, coupled⟩
  have first := coupled.run (before safety false) (before_frame safety false) (both_admitted safety false)
    (by rw [recorded_result]; rfl)
  have second := coupled.run (before safety true) (before_frame safety true) (both_admitted safety true)
    (by rw [recorded_result]; rfl)
  have same : cursorGraph (MissStream.childCursor position (before safety false)) (before safety false) =
      cursorGraph (MissStream.childCursor position (before safety false)) (before safety true) := by
    change { (native safety false).graph with allocationCursor := position + 0 - 0 } =
      { (native safety true).graph with allocationCursor := position + 0 - 0 }
    rw [initial_graph, initial_graph]
  rw [same] at first
  have reached := first.2.2.trans second.2.2.symm
  have addresses := congrArg lastAddress reached
  change lastAddress (child safety (native safety false)).2.graph =
    lastAddress (child safety (native safety true)).2.graph at addresses
  rw [native_address, native_address] at addresses
  cases addresses

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeAllocationIdentityTests
