/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneInsertion
import Compiler.Extraction.AssemblyClonePhysicalTests
import Compiler.Extraction.AssemblyCloneTests

namespace Compiler.Extraction.AssemblyClone.Physical.Insertion.Tests
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization
open Physical.Tests (initial initial_valid input request bytes objects external initial_item)

def incoming := ExpressionDeinit.Lifetime.Tests.incoming
def handle := ExpressionDeinit.Lifetime.Tests.inputHandle
def target (_ : Storage.State) (_ : State Nat Nat) : ExpressionDeinit.Descriptor := ⟨4, ⟨5, incoming.items⟩⟩

/-- Object creation and vector/table mutation remain fixture operations. The
actual normalization duplicate, source clone, payload cleanup, item release
and both argument frees execute in the same typed registry. -/
def rest (failure : Option Storage.Allocation) : Storage.Operations (State Nat Nat) Fault where
  attempt site _ before := match site with
    | .arguments =>
      let (result, memory) := takeOwned Cache.normalizationOwnershipCode external 7 handle before.execution.memory
      let after := { before with execution := { before.execution with memory } }
      match result with
      | .ok _ => (.ok true, after)
      | .error .outOfMemory => (.ok false, after)
      | .error fault => (.error (.destroy (.arguments fault)), after)
    | .item | .append | .publish =>
      let digit := match site with | .item => 5 | .append => 7 | _ => 8
      (.ok (failure != some site), { before with execution := { before.execution with memory :=
        { before.execution.memory with effects := before.execution.memory.effects * 10 + digit } } })
    | .clone => (.error .missingValue, before)
  release action ownership before := match action with
    | .normalized | .arguments =>
      let slice := if action = .normalized || ownership.aliasesNormalized then incoming else (target ownership before).arguments
      let (result, memory) := free external 7 slice before.execution.memory
      (result.mapError (fun fault => Fault.destroy (.arguments fault)),
        { before with execution := { before.execution with memory } })
    | .allocation =>
      let (result, memory) := AssemblyItem.destroy objects 7 (target ownership before).item before.execution.memory
      (result.mapError (fun fault => Fault.destroy (.item (.inr fault))),
        { before with execution := { before.execution with memory } })
    | .pop => (.ok (), { before with execution := { before.execution with memory :=
        { before.execution.memory with effects := before.execution.memory.effects * 10 + 9 } } })
    | _ => (.error .missingValue, before)

def callbacks (failure : Option Storage.Allocation := none) :=
  operations (request (if failure = some .clone then none else some 320)) bytes objects external 7 input target (rest failure)
def execute (failure : Option Storage.Allocation := none) :=
  insertProgram.execute ⟨true, true, fun _ => false⟩ (callbacks failure) {} ⟨⟨initial, false⟩, none⟩

def taken := takeOwned Cache.normalizationOwnershipCode external 7 handle initial
def beforeClone : Session Nat := { taken.2 with effects := 15 }
def cloned := run (request) 7 input beforeClone
def copied : Value Nat := { input with verbatim := some ⟨1, 2, ⟨6, Physical.Tests.source.contents, 0⟩⟩ }
def reached : State Nat Nat := ⟨⟨{ cloned.2 with effects := 15678 }, false⟩, some copied⟩

theorem taken_ready : Valid beforeClone ∧ SliceValid 7 beforeClone.heap (target {} reached).arguments ∧
    AssemblyItem.Owned 7 4 beforeClone := by
  have contents : Compiler.ZigAir.Memory.WordArray.Represents initial.memory (Arguments.view incoming) incoming.items :=
    (initial_valid.related 7 0 [0] (by decide) (by rfl')).2
  have ready : Ready 7 (Arguments.view incoming) incoming.items handle initial :=
    ⟨initial_valid, contents, contents, (by intro _ impossible; cases impossible), (by intro _ _ impossible; cases impossible)⟩
  obtain ⟨result, after, executed, post⟩ := take_refines external 7 (Arguments.view incoming) incoming.items handle initial ready
    ExpressionDeinit.Tests.external_admitted
  have returned : taken.1 = .ok ((target {} reached).arguments, handle) := by rfl'
  have same : result = .ok ((target {} reached).arguments, handle) := (congrArg Prod.fst executed).symm.trans returned
  rw [same] at post
  have memory := congrArg Prod.snd executed
  have valid : Valid taken.2 ∧ SliceValid 7 taken.2.heap (target {} reached).arguments := memory.symm ▸ ⟨post.ready.valid, post.live⟩
  exact ⟨⟨valid.1.memory, valid.1.related, valid.1.injected⟩, valid.2,
    ⟨⟨_, by rfl'⟩, ExpressionDeinit.Lifetime.Tests.object, by rfl', rfl, rfl, rfl⟩⟩

theorem clone_result : cloned.1 = .ok copied := by rfl'
theorem clone_contract : Cloned 7 input copied beforeClone cloned.2 :=
  run_valid (request) 7 input copied beforeClone cloned.2 taken_ready.1 (Prod.ext clone_result rfl)

theorem reached_rollback (ownership : Storage.State) : ∃ after,
    (callbacks (some .publish)).release .lastValue ownership reached = (.ok (), after) ∧ after.value = none ∧
    ExpressionDeinit.Lifetime.Post (payload copied) (target ownership reached) reached.execution.memory after.execution :=
  last_value_callback (request) bytes objects external 7 input copied target (rest (some .publish)) ownership reached rfl rfl
    ⟨clone_contract.valid.memory, clone_contract.valid.related, clone_contract.valid.injected⟩
    (clone_contract.item taken_ready.1 4 taken_ready.2.2)
    (clone_contract.arguments taken_ready.1 _ taken_ready.2.1) clone_contract.owned

theorem publication_rollback : (execute (some .publish)).1.1 = .ok (some .allocationFailure) ∧
    (execute (some .publish)).2.execution.memory.effects = 1567823494 ∧
    (execute (some .publish)).2.value = none ∧ (execute (some .publish)).1.2.appended = false ∧
    (execute (some .publish)).2.execution.invalidated = true ∧
    (execute (some .publish)).2.execution.memory.heap 0 = none ∧
    (execute (some .publish)).2.execution.memory.heap 4 = none ∧
    (execute (some .publish)).2.execution.memory.heap 5 = none ∧
    (execute (some .publish)).2.execution.memory.heap 6 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem physical_rollback : (execute (some .publish)).2.execution.memory.memory.heap.lookup 0 = none ∧
    (execute (some .publish)).2.execution.memory.memory.heap.lookup 4 = none ∧
    (execute (some .publish)).2.execution.memory.memory.heap.lookup 5 = none ∧
    (execute (some .publish)).2.execution.memory.memory.heap.lookup 6 = none ∧
    readable (execute (some .publish)).2.execution.memory.memory Physical.Tests.source = true :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem append_rollback : (execute (some .append)).1.1 = .ok (some .allocationFailure) ∧
    (execute (some .append)).2.execution.memory.effects = 15672344 ∧
    (execute (some .append)).2.value = none ∧
    (execute (some .append)).2.execution.memory.memory.heap.lookup 6 = none ∧
    (execute (some .append)).2.execution.memory.memory.heap.lookup 4 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem clone_oom_cleanup : (execute (some .clone)).1.1 = .ok (some .allocationFailure) ∧
    (execute (some .clone)).2.execution.memory.effects = 156344 ∧
    (execute (some .clone)).2.execution.memory.memory.nextId = 6 ∧
    (execute (some .clone)).2.value = none ∧
    (execute (some .clone)).2.execution.memory.memory.heap.lookup 4 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem success_keeps_clone : execute.1.1 = .ok (some .success) ∧ execute.2.value = some copied ∧
    execute.2.execution.memory.memory.heap.lookup 6 = some (cell 3 320 (copiedCells Physical.Tests.source)) ∧
    execute.2.execution.memory.effects = 15678 := ⟨by rfl', by rfl', by rfl', by rfl'⟩

def sourceFault := insertProgram.execute ⟨true, true, fun _ => false⟩ (callbacks) {}
  ⟨⟨ExpressionDeinit.Lifetime.Tests.initial, false⟩, none⟩
theorem source_fault_stops : sourceFault.1.1 = .error (.clone .sourceMismatch) ∧
    sourceFault.2.execution.memory.effects = 156 ∧ sourceFault.2.value = none ∧
    sourceFault.2.execution.memory.memory.nextId = 7 ∧
    sourceFault.2.execution.memory.memory.heap.lookup 6 = some (cell 3 320 []) ∧
    sourceFault.2.execution.memory.memory.heap.lookup 4 = some ExpressionDeinit.Lifetime.Tests.object ∧
    sourceFault.1.2.owner .normalized = .local ∧ sourceFault.1.2.owner .arguments = .local :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def invalidated : State Nat Nat := { reached with execution := { reached.execution with invalidated := true } }
theorem invalidated_rejects : (callbacks).release .lastValue {} invalidated =
    (.error (.destroy .invalidDescriptor), invalidated) ∧
    (callbacks).release .value {} invalidated = (.error (.destroy .invalidDescriptor), invalidated) := ⟨by rfl', by rfl'⟩

open Compiler.Extraction.Interner
open ObservedTests (model caller callerHeap caller_valid)
open ObservedStorageTests (key)
def storedCell := { ExpressionDeinit.Lifetime.Tests.storedCell with item := copied.item }

theorem insertion_words :
    Interner.Invariant model (Interner.InsertionExecution.project [caller] (fun _ => none) storedCell key
      (execute (some .publish)).1.2) ∧
    Interner.Stable callerHeap (Interner.InsertionExecution.project [caller] (fun _ => none) storedCell key
      (execute (some .publish)).1.2) := by
  have binding : Cache.keyCode.run storedCell.item storedCell.arguments storedCell.sequence = some key := by
    change Cache.keyCode.run copied.item _ _ = _
    rw [clone_contract.same.1]
    exact ObservedStorageTests.binding
  have denotation : key.eval model (readValue [caller]) = some storedCell.value := ObservedStorageTests.denotation
  have checked := Interner.InsertionExecution.verified model [caller] (fun _ => none) storedCell key true
    (callbacks (some .publish)) ⟨⟨initial, false⟩, none⟩ (some .allocationFailure) caller_valid binding denotation publication_rollback.1
  exact ⟨checked.2.1, checked.2.2.1⟩

end Compiler.Extraction.AssemblyClone.Physical.Insertion.Tests
