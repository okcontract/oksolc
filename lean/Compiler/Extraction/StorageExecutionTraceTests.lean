/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.StorageExecutionTrace
import Compiler.Extraction.StorageExecutionTests

namespace Compiler.Extraction.Storage.Trace.Tests
open ExecutionTests

/-- Reuse every outcome of the existing insertion family, including native OOM,
capacity, nondeterministic transfer and semantic allocation/cleanup faults. -/
theorem existing_family (deterministic room : Bool) (failure : Option Allocation)
    (attemptFault : Bool) (releaseFault : Option Release) (leading trailing : List (Trace.Event Fault)) :
    let input : Input := ⟨deterministic, room, fun _ => false⟩
    let captured := insertProgram.execute input (record (operations failure attemptFault releaseFault)) {} ⟨[], []⟩
    (captured.1, captured.2.effects) = run deterministic room failure attemptFault releaseFault ∧
    insertProgram.execute input (replay (leading ++ captured.2.events ++ trailing) .cleanup) {} leading.length =
      ((run deterministic room failure attemptFault releaseFault).1, leading.length + captured.2.events.length) := by
  have checked := execute_recorded (operations failure attemptFault releaseFault) .cleanup
    ⟨deterministic, room, fun _ => false⟩ insertProgram {} [] [] leading trailing
  exact ⟨checked.1, checked.2.2⟩

/-- Cleanup effects choose the later allocation result. An allocation-only
oracle or a recorder that rewinds private effects cannot establish this trace. -/
theorem cleanup_before_attempt :
    let captured := continuationProgram.execute ⟨true, true, fun _ => true⟩ (record dependentOperations) {} ⟨0, []⟩
    captured.1.1 = .ok (some .allocationFailure) ∧ captured.2.effects = 11 ∧
    captured.2.events = [.release .normalized {} (.ok ()),
      .attempt .item (Release.normalized.run {}) (.ok false)] := ⟨rfl, rfl, rfl⟩

theorem ordinary_oom_cleans :
    let captured := insertProgram.execute ⟨true, true, fun _ => false⟩
      (record (operations (some .arguments))) {} ⟨[], []⟩
    captured.1.1 = .ok (some .allocationFailure) ∧ captured.2.events.length = 2 ∧
    captured.1.2.owner .normalized = .freed := ⟨by rfl', by rfl', by rfl'⟩

theorem semantic_fault_stops :
    let captured := insertProgram.execute ⟨true, true, fun _ => false⟩
      (record (operations none true)) {} ⟨[], []⟩
    captured.1.1 = .error .allocation ∧ captured.2.events.length = 1 ∧
    captured.1.2.owner .normalized = .local := ⟨by rfl', by rfl', by rfl'⟩

theorem wrong_site :
    (replay [.attempt .arguments {} (.ok true)] Fault.cleanup).attempt .item {} 0 = (.error .cleanup, 2) := by rfl

theorem wrong_owner :
    (replay [.attempt .item {} (.ok true)] Fault.cleanup).attempt .item { appended := true } 0 =
      (.error .cleanup, 2) := by rfl

theorem wrong_kind :
    (replay [.release .normalized {} (.ok ())] Fault.cleanup).attempt .arguments {} 0 = (.error .cleanup, 2) := rfl

theorem wrong_release :
    (replay [.release .normalized {} (.ok ())] Fault.cleanup).release .arguments {} 0 = (.error .cleanup, 2) := by rfl

theorem wrong_release_owner :
    (replay [.release .normalized {} (.ok ())] Fault.cleanup).release .normalized { invalid := true } 0 =
      (.error .cleanup, 2) := by rfl

theorem exhausted :
    (replay [] Fault.cleanup).attempt .arguments {} 0 = (.error .cleanup, 1) ∧
    (replay [] Fault.cleanup).release .normalized {} 1 = (.error .cleanup, 1) := ⟨rfl, rfl⟩

theorem fault_is_not_oom :
    (replay [.attempt .item {} (.error .allocation)] Fault.cleanup).attempt .item {} 0 = (.error .allocation, 1) := by rfl

end Compiler.Extraction.Storage.Trace.Tests
