/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemInitializationTests
import Compiler.Extraction.AssemblyItemCreationInsertion
import Compiler.Extraction.AssemblyCloneInsertionTests

namespace Compiler.Extraction.AssemblyItem.Creation.Insertion.Tests
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization
open AssemblyClone.Physical.Tests (input source bytes objects external)

/-- No live item object at entry. The retired extent can be reused, but its
lifetime ID cannot: arguments, object and cloned bytes get IDs 5, 6 and 7. -/
def initial : Session Nat :=
  { AssemblyClone.Physical.Tests.initial with
    heap := write AssemblyClone.Physical.Tests.initial.heap 4 none
    memory := Compiler.ZigAir.Memory.erase AssemblyClone.Physical.Tests.initial.memory 4 }

theorem initial_valid : Valid initial :=
  ⟨Compiler.ZigAir.Memory.erase_preserves_valid _ _ AssemblyClone.Physical.Tests.initial_valid.memory,
    Arguments.related_erase _ _ _ AssemblyClone.Physical.Tests.initial_valid.related,
    AssemblyClone.Physical.Tests.initial_valid.injected.erased _⟩
theorem no_initial_object : initial.heap 4 = none ∧ initial.memory.heap.lookup 4 = none ∧ initial.heap 6 = none ∧
    initial.memory.heap.lookup 6 = none := ⟨by rfl', by rfl', by rfl', by rfl'⟩

def incoming := ExpressionDeinit.Lifetime.Tests.incoming
def handle := ExpressionDeinit.Lifetime.Tests.inputHandle
def arguments : ArgumentSlice := ⟨5, incoming.items⟩
def allocate (response : Option Nat := some 80) : Creation.Allocate Nat := fun wanted before =>
  (if wanted = ⟨224, 16⟩ then response else none, before.effects * 10 + 5)
def copy (response : Option Nat := some 320) := AssemblyClone.Physical.Tests.request response

/-- Only vector/table mutation remains framed here. Argument duplication,
object creation, clone and every allocation cleanup use the same typed session. -/
def rest (failure : Option Storage.Allocation) (destination : ArgumentSlice := arguments) : Storage.Operations (State Metadata Nat) Fault where
  attempt site _ before := match site with
    | .arguments =>
      let (result, memory) := takeOwned Cache.normalizationOwnershipCode external 7 handle before.clone.execution.memory
      let after := { before with clone := { before.clone with execution := { before.clone.execution with memory } } }
      match result with
      | .ok _ => (.ok true, after)
      | .error .outOfMemory => (.ok false, after)
      | .error fault => (.error (.insertion (.destroy (.arguments fault))), after)
    | .append | .publish =>
      let digit := if site = .append then 7 else 8
      (.ok (failure != some site), { before with clone := { before.clone with execution := { before.clone.execution with memory :=
        { before.clone.execution.memory with effects := before.clone.execution.memory.effects * 10 + digit } } } })
    | _ => (.error .missingObject, before)
  release action ownership before := match action with
    | .normalized | .arguments =>
      let slice := if action = .normalized || ownership.aliasesNormalized then incoming else destination
      let (result, memory) := free external 7 slice before.clone.execution.memory
      (result.mapError (fun fault => Fault.insertion (.destroy (.arguments fault))),
        { before with clone := { before.clone with execution := { before.clone.execution with memory } } })
    | .pop => (.ok (), { before with clone := { before.clone with execution := { before.clone.execution with memory :=
        { before.clone.execution.memory with effects := before.clone.execution.memory.effects * 10 + 9 } } } })
    | _ => (.error .missingObject, before)

def callbacks (failure : Option Storage.Allocation := none) :=
  operations (allocate (if failure = some .item then none else some 80))
    (copy (if failure = some .clone then none else some 320)) bytes objects external 7 input (fun _ _ => arguments) (rest failure)
def start : State Nat Nat := ⟨⟨⟨initial, false⟩, none⟩, none⟩
def execute (failure : Option Storage.Allocation := none) :=
  insertProgram.execute ⟨true, true, fun _ => false⟩ (callbacks failure) {} start

def taken := takeOwned Cache.normalizationOwnershipCode external 7 handle initial
def made := create (allocate) 7 input.item taken.2
def cloned := AssemblyClone.Physical.run (copy) 7 input made.2
def copied : AssemblyClone.Value Nat := { input with verbatim := some ⟨1, 2, ⟨7, source.contents, 0⟩⟩ }
def filled : State Nat Nat := ⟨⟨⟨cloned.2, false⟩, some copied⟩, some 6⟩

theorem taken_ready : Valid taken.2 ∧ SliceValid 7 taken.2.heap arguments := by
  have contents : Compiler.ZigAir.Memory.WordArray.Represents initial.memory (Arguments.view incoming) incoming.items :=
    (initial_valid.related 7 0 [0] (by decide) (by rfl')).2
  have ready : Ready 7 (Arguments.view incoming) incoming.items handle initial :=
    ⟨initial_valid, contents, contents, (by intro _ impossible; cases impossible), (by intro _ _ impossible; cases impossible)⟩
  obtain ⟨result, after, executed, post⟩ := take_refines external 7 (Arguments.view incoming) incoming.items handle initial ready
    ExpressionDeinit.Tests.external_admitted
  have returned : taken.1 = .ok (arguments, handle) := by rfl'
  have same : result = .ok (arguments, handle) := (congrArg Prod.fst executed).symm.trans returned
  rw [same] at post
  exact (congrArg Prod.snd executed).symm ▸ ⟨post.ready.valid, post.live⟩

theorem create_result : made.1 = .ok 6 := by rfl'
theorem creation_contract : Created 7 6 taken.2 made.2 :=
  create_verified (allocate) 7 6 input.item taken.2 made.2 taken_ready.1 (Prod.ext create_result rfl)
theorem clone_result : cloned.1 = .ok copied := by rfl'
theorem clone_contract : AssemblyClone.Physical.Cloned 7 input copied made.2 cloned.2 :=
  AssemblyClone.Physical.run_valid (copy) 7 input copied made.2 cloned.2 creation_contract.valid (Prod.ext clone_result rfl)

theorem composed_rollback (ownership : Storage.State) : ∃ after,
    (callbacks).release .lastValue ownership filled = (.ok (), after) ∧ after.object = none ∧ after.clone.value = none ∧
    ExpressionDeinit.Lifetime.Post (AssemblyClone.Physical.payload copied) ⟨6, arguments⟩ cloned.2 after.clone.execution :=
  (create_clone_rollback (allocate) (copy) bytes objects external 7 6 input copied arguments (rest none) ownership
    taken.2 made.2 cloned.2 taken_ready.1 taken_ready.2 (Prod.ext create_result rfl) (Prod.ext clone_result rfl)).2.2.2

def failedClone := AssemblyClone.Physical.run (copy none) 7 input made.2
theorem clone_oom_contract (ownership : Storage.State) : ∃ after,
    (callbacks (some .clone)).release .allocation ownership ⟨⟨⟨failedClone.2, false⟩, none⟩, some 6⟩ = (.ok (), after) ∧
    after.object = none ∧ Released 6 failedClone.2 after.clone.execution.memory ∧
    after.clone.execution.memory.effects = objects 6 failedClone.2 :=
  clone_oom_release (allocate) (copy none) bytes objects external 7 6 input (fun _ _ => arguments) (rest (some .clone)) ownership
    taken.2 made.2 failedClone.2 taken_ready.1 (Prod.ext create_result rfl) (by rfl')

theorem publication_rollback : (execute (some .publish)).1.1 = .ok (some .allocationFailure) ∧
    (execute (some .publish)).2.clone.execution.memory.effects = 1567823494 ∧
    (execute (some .publish)).2.object = none ∧ (execute (some .publish)).2.clone.value = none ∧
    (execute (some .publish)).1.2.appended = false ∧ (execute (some .publish)).2.clone.execution.invalidated = true ∧
    (execute (some .publish)).2.clone.execution.memory.heap 0 = none ∧
    (execute (some .publish)).2.clone.execution.memory.heap 5 = none ∧
    (execute (some .publish)).2.clone.execution.memory.heap 6 = none ∧
    (execute (some .publish)).2.clone.execution.memory.heap 7 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem physical_rollback : (execute (some .publish)).2.clone.execution.memory.memory.heap.lookup 0 = none ∧
    (execute (some .publish)).2.clone.execution.memory.memory.heap.lookup 5 = none ∧
    (execute (some .publish)).2.clone.execution.memory.memory.heap.lookup 6 = none ∧
    (execute (some .publish)).2.clone.execution.memory.memory.heap.lookup 7 = none ∧
    AssemblyClone.Physical.readable (execute (some .publish)).2.clone.execution.memory.memory source = true :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem append_rollback : (execute (some .append)).1.1 = .ok (some .allocationFailure) ∧
    (execute (some .append)).2.clone.execution.memory.effects = 15672344 ∧ (execute (some .append)).2.object = none ∧
    (execute (some .append)).2.clone.value = none ∧
    (execute (some .append)).2.clone.execution.memory.memory.heap.lookup 6 = none ∧
    (execute (some .append)).2.clone.execution.memory.memory.heap.lookup 7 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem clone_oom_cleanup : (execute (some .clone)).1.1 = .ok (some .allocationFailure) ∧
    (execute (some .clone)).2.clone.execution.memory.effects = 156344 ∧ (execute (some .clone)).2.object = none ∧
    (execute (some .clone)).2.clone.execution.memory.memory.nextId = 7 ∧
    (execute (some .clone)).2.clone.execution.memory.memory.heap.lookup 6 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem create_oom_cleanup : (execute (some .item)).1.1 = .ok (some .allocationFailure) ∧
    (execute (some .item)).2.clone.execution.memory.effects = 1544 ∧ (execute (some .item)).2.object = none ∧
    (execute (some .item)).2.clone.execution.memory.memory.nextId = 6 ∧
    (execute (some .item)).2.clone.execution.memory.memory.heap.lookup 5 = none ∧
    (execute (some .item)).2.clone.execution.memory.heap 0 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem success_keeps_allocations : execute.1.1 = .ok (some .success) ∧ execute.2.object = some 6 ∧
    execute.2.clone.value = some copied ∧ execute.2.clone.execution.memory.memory.heap.lookup 6 = some (cell 80) ∧
    execute.2.clone.execution.memory.memory.heap.lookup 7 = some (AssemblyClone.Physical.cell 3 320 (AssemblyClone.Physical.copiedCells source)) ∧
    execute.2.clone.execution.memory.effects = 15678 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem request_oom_keeps_effects : create (allocate none) 7 input.item initial =
    (.error .outOfMemory, { initial with effects := 5 }) := by rfl'
theorem misaligned_rejected : create (allocate (some 81)) 7 input.item initial =
    (.error (.memory .memoryValidity), { initial with effects := 5 }) := by rfl'
theorem overlap_rejected : create (allocate (some 64)) 7 input.item initial =
    (.error (.memory .memoryValidity), { initial with effects := 5 }) := by rfl'
theorem overflow_rejected : create (allocate (some (2^64 - 16))) 7 input.item initial =
    (.error (.memory .memoryValidity), { initial with effects := 5 }) := by rfl'
def collision : Session Nat := { initial with heap := write initial.heap 5 (some ⟨9, .bytes 8⟩) }
theorem collision_retains_allocation : (create (allocate) 7 input.item collision).1 = .error .registryCollision ∧
    (create (allocate) 7 input.item collision).2.memory.heap.lookup 5 = some (cell 80) ∧
    (create (allocate) 7 input.item collision).2.heap 5 = some ⟨9, .bytes 8⟩ ∧
    (create (allocate) 7 input.item collision).2.effects = 5 := ⟨by rfl', by rfl', by rfl', by rfl'⟩

def badRegion := insertProgram.execute ⟨true, true, fun _ => false⟩
  (operations (allocate (some 64)) (copy) bytes objects external 7 input (fun _ _ => arguments) (rest none)) {} start
theorem bad_region_stops : badRegion.1.1 = .error (.creation (.memory .memoryValidity)) ∧
    badRegion.2.clone.execution.memory.effects = 15 ∧ badRegion.2.object = none ∧
    badRegion.2.clone.execution.memory.memory.nextId = 6 ∧ badRegion.1.2.owner .arguments = .local ∧
    badRegion.2.clone.execution.memory.heap 5 = some ⟨7, .arguments incoming.items⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem missing_object_rejects : (callbacks).attempt .clone {} start = (.error .missingObject, start) ∧
    (callbacks).release .allocation {} start = (.error .missingObject, start) ∧
    (callbacks).release .lastValue {} start = (.error .missingObject, start) := ⟨by rfl', by rfl', by rfl'⟩
theorem repeated_creation_rejects : (callbacks).attempt .item {} filled = (.error .alreadyCreated, filled) := by rfl'

theorem failed_destroy_retains_object :
    (operations (allocate) (copy) bytes objects external 9 input (fun _ _ => arguments) (rest none)).release .allocation {} filled =
      (.error (.insertion (.destroy (.item (.inr (.ownership .wrongAllocator))))), filled) := by rfl'
def malformed : Session Nat := { initial with memory := { initial.memory with nextId := 0 } }
theorem invalid_input_skips_request : create (allocate) 7 input.item malformed =
    (.error (.memory .malformed), malformed) := by rfl'
theorem null_region_rejects : create (allocate (some 0)) 7 input.item initial =
    (.error (.memory .memoryValidity), { initial with effects := 5 }) := by rfl'

def unreadable : State Nat Nat := { start with clone := { start.clone with execution := { start.clone.execution with memory :=
  { initial with memory := { initial.memory with heap := initial.memory.heap.replace 3 AssemblyItemDeinit.Tests.cell } } } } }
def sourceFault := insertProgram.execute ⟨true, true, fun _ => false⟩ (callbacks) {} unreadable
theorem source_fault_retains_object : sourceFault.1.1 = .error (.insertion (.clone .sourceMismatch)) ∧
    sourceFault.2.object = some 6 ∧ sourceFault.2.clone.value = none ∧ sourceFault.2.clone.execution.memory.effects = 156 ∧
    sourceFault.2.clone.execution.memory.memory.heap.lookup 6 = some (cell 80) ∧
    sourceFault.2.clone.execution.memory.memory.heap.lookup 7 = some (AssemblyClone.Physical.cell 3 320 []) ∧
    sourceFault.1.2.owner .allocation = .local ∧ sourceFault.1.2.owner .value = .absent :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

def transferred (failure : Option Storage.Allocation := none) :=
  insertProgram.execute ⟨false, true, fun _ => false⟩
    (operations (allocate (if failure = some .item then none else some 80))
      (copy (if failure = some .clone then none else some 320)) bytes objects external 7 input (fun _ _ => incoming) (rest failure)) {} start
theorem transferred_success : transferred.1.1 = .ok (some .success) ∧ transferred.2.object = some 5 ∧
    transferred.2.clone.execution.memory.effects = 567 ∧ transferred.2.clone.execution.memory.memory.nextId = 7 ∧
    transferred.2.clone.execution.memory.heap 0 = some ⟨7, .arguments incoming.items⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem transferred_append_cleanup : (transferred (some .append)).1.1 = .ok (some .allocationFailure) ∧
    (transferred (some .append)).2.clone.execution.memory.effects = 567234 ∧ (transferred (some .append)).2.object = none ∧
    (transferred (some .append)).2.clone.execution.memory.memory.heap.lookup 0 = none ∧
    (transferred (some .append)).2.clone.execution.memory.memory.heap.lookup 5 = none ∧
    (transferred (some .append)).2.clone.execution.memory.memory.heap.lookup 6 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem transferred_create_oom : (transferred (some .item)).1.1 = .ok (some .allocationFailure) ∧
    (transferred (some .item)).2.clone.execution.memory.effects = 54 ∧ (transferred (some .item)).2.object = none ∧
    (transferred (some .item)).2.clone.execution.memory.memory.heap.lookup 0 = none := ⟨by rfl', by rfl', by rfl', by rfl'⟩
theorem transferred_clone_oom : (transferred (some .clone)).1.1 = .ok (some .allocationFailure) ∧
    (transferred (some .clone)).2.clone.execution.memory.effects = 5634 ∧ (transferred (some .clone)).2.object = none ∧
    (transferred (some .clone)).2.clone.execution.memory.memory.heap.lookup 5 = none := ⟨by rfl', by rfl', by rfl', by rfl'⟩

open Compiler.Extraction.Interner
open ObservedTests (model caller callerHeap caller_valid)
open ObservedStorageTests (key)
def storedCell := { ExpressionDeinit.Lifetime.Tests.storedCell with item := copied.item }
theorem insertion_words :
    Interner.Invariant model (Interner.InsertionExecution.project [caller] (fun _ => none) storedCell key (execute (some .publish)).1.2) ∧
    Interner.Stable callerHeap (Interner.InsertionExecution.project [caller] (fun _ => none) storedCell key (execute (some .publish)).1.2) := by
  have binding : Cache.keyCode.run storedCell.item storedCell.arguments storedCell.sequence = some key := by
    change Cache.keyCode.run copied.item _ _ = _
    rw [clone_contract.same.1]
    exact ObservedStorageTests.binding
  have checked := Interner.InsertionExecution.verified model [caller] (fun _ => none) storedCell key true (callbacks (some .publish)) start
    (some .allocationFailure) caller_valid binding ObservedStorageTests.denotation publication_rollback.1
  exact ⟨checked.2.1, checked.2.2.1⟩

end Compiler.Extraction.AssemblyItem.Creation.Insertion.Tests
