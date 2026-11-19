/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionRecursionEffects
import Compiler.Extraction.InternerItemPreparationEffectsTests
import Compiler.Extraction.StorageExecutionTests
import Compiler.Extraction.InternerInsertionCountTests

namespace Compiler.Extraction.Storage.ControlEffectTests
open Compiler.Algebraic

/-- Test-only primitive-call counter. It is deliberately separate from native
host events: one primitive can make zero, one or several allocation requests. -/
def tick (call : Effect σ ε α) (before : σ × Nat) : Except ε α × (σ × Nat) :=
  let (result, reached) := call before.1
  (result, (reached, before.2 + 1))

def decorate (calls : Operations σ ε) : Operations (σ × Nat) ε :=
  ⟨fun site owner => tick (calls.attempt site owner), fun action owner => tick (calls.release action owner)⟩

theorem decorated_transport (calls : Operations σ ε) :
    Operations.Transport (decorate calls) calls Prod.fst := ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem program_erases (calls : Operations σ ε) (input : Input) (program : Program)
    (owner : State) (before : σ × Nat) :
    program.execute input calls owner before.1 =
      ((program.execute input (decorate calls) owner before).1, (program.execute input (decorate calls) owner before).2.1) :=
  (decorated_transport calls).execute input program owner before

def run (deterministic := true) (room := true) (failure : Option Allocation := none)
    (attemptFault := false) (releaseFault : Option Release := none) (count := 0) :=
  insertProgram.execute ⟨deterministic, room, fun _ => false⟩
    (decorate (ExecutionTests.operations failure attemptFault releaseFault)) {} ([], count)

theorem fixtures_erase (deterministic room : Bool) (failure : Option Allocation)
    (attemptFault : Bool) (releaseFault : Option Release) (count : Nat) :
    ExecutionTests.run deterministic room failure attemptFault releaseFault =
      ((run deterministic room failure attemptFault releaseFault count).1,
       (run deterministic room failure attemptFault releaseFault count).2.1) :=
  program_erases _ _ insertProgram {} ([], count)

theorem success_preserves_history (count : Nat) :
    (run true true none false none count).1.1 = .ok (some .success) ∧
    (run true true none false none count).2.2 = count + 5 := by
  constructor
  · rfl'
  · rfl'

theorem allocation_fault_stops : (run true true none true).1.1 = .error .allocation ∧
    (run true true none true).2.2 = 1 ∧
    (run true true none true).1.2.owner .normalized = .local := ⟨by rfl', by rfl', by rfl'⟩

theorem cleanup_fault_stops : (run true true (some .publish) false (some .pop)).1.1 = .error .cleanup ∧
    (run true true (some .publish) false (some .pop)).2.2 = 7 ∧
    (run true true (some .publish) false (some .pop)).1.2.appended = true ∧
    (run true true (some .publish) false (some .pop)).1.2.owner .value = .freed ∧
    (run true true (some .publish) false (some .pop)).1.2.owner .normalized = .local :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem publication_refusal_unwinds : (run true true (some .publish)).1.1 = .ok (some .allocationFailure) ∧
    (run true true (some .publish)).2.2 = 8 ∧
    (run true true (some .publish)).1.2.appended = false := ⟨by rfl', by rfl', by rfl'⟩

theorem capacity_release_fault : (run false false none false (some .normalized)).1.1 = .error .cleanup ∧
    (run false false none false (some .normalized)).2.2 = 1 := ⟨by rfl', by rfl'⟩

/-- Reuse the existing continuation whose allocation decision depends on the
preceding release. Erasure cannot restart it from the earlier private effects. -/
theorem reached_continuation :
    let ran := ExecutionTests.continuationProgram.execute ⟨true, true, fun _ => true⟩
      (decorate ExecutionTests.dependentOperations) {} (0, 0)
    ran.1.1 = .ok (some .allocationFailure) ∧ ran.2 = (11, 2) := ⟨rfl, rfl⟩

theorem pure_command_skips_host :
    let ran := (Program.command .captureId .ret).execute ⟨true, true, fun _ => true⟩
      (decorate ExecutionTests.dependentOperations) {} (0, 9)
    ran.1.1 = .ok (some .success) ∧ ran.2 = (0, 9) := ⟨rfl, rfl⟩

end Compiler.Extraction.Storage.ControlEffectTests
