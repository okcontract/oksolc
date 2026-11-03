/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneFieldFixtures

namespace Compiler.Extraction.AssemblyItem.Creation.NativeFields.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Extraction.Storage
open AssemblyClone.NativeFields
open Fields
open AssemblyClone.Physical.Tests (bytes objects external)

def arguments : ArgumentSlice := ⟨6, Insertion.Tests.incoming.items⟩
def copy (response : Option Nat := some 320) : AssemblyClone.Physical.Allocate Nat := fun length before =>
  (if length = 2 then response else none, before.effects * 10 + 6)
def callbacks (failure : Option Storage.Allocation := none) := operations
  (Insertion.Tests.allocate (if failure = some .item then none else some 80))
  (copy (if failure = some .clone then none else some 320)) bytes objects external 7 source input
  (fun _ _ => arguments) (Insertion.Tests.rest failure arguments)
def start : State Nat := ⟨⟨⟨initial, false⟩, none⟩, none⟩
def execute (failure : Option Storage.Allocation := none) :=
  insertProgram.execute ⟨true, true, fun _ => false⟩ (callbacks failure) {} start
def taken := takeOwned Cache.normalizationOwnershipCode external 7 Insertion.Tests.handle initial
def made := create (Insertion.Tests.allocate) 7 input.item taken.2
def cloned := AssemblyClone.Physical.run (copy) 7 input made.2
def copied : ItemValue := { input with verbatim := some ⟨2, 3, ⟨8, [8, 9], 0⟩⟩ }
def filled := execute.2

theorem complete_execution : execute.1.1 = .ok (some .success) ∧ filled.object = some 7 ∧
    filled.clone.execution.memory.memory.heap.lookup 7 = some { Creation.cell 80 with cells := expectedCells 8 0 } ∧
    filled.clone.execution.memory.effects = 15678 := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem every_member : ∀ selected, member filled.clone.execution.memory.memory ⟨7, 0⟩ selected =
    .ok (AssemblyClone.NativeFields.values copied selected) := by
  intro selected; cases selected <;> decide +kernel

theorem source_and_payload_frame : filled.clone.execution.memory.memory.heap.lookup 5 = some sourceCell ∧
    filled.clone.execution.memory.memory.heap.lookup 3 = some AssemblyClone.Physical.Tests.sourceCell ∧
    filled.clone.execution.memory.memory.heap.lookup 8 =
      some (AssemblyClone.Physical.cell 2 320 [(0, .scalar (.int false 8 8)), (1, .scalar (.int false 8 9))]) ∧
    filled.clone.execution.memory.memory.nextId = 9 := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem borrowed_metadata : sourceName filled.clone.execution.memory.memory ⟨7, 0⟩ false =
    .ok (some (.leaf (.slice (.slice false (.scalar (.int false 8))) ⟨99, 2⟩ 3))) ∧
    sourceName filled.clone.execution.memory.memory ⟨7, 0⟩ true =
    .ok (some (.leaf (.slice (.slice false (.scalar (.int false 8))) ⟨100, 7⟩ 0))) := ⟨by decide +kernel, by decide +kernel⟩

theorem publication_rollback : (execute (some .publish)).1.1 = .ok (some .allocationFailure) ∧
    (execute (some .publish)).2.object = none ∧ (execute (some .publish)).2.clone.value = none ∧
    (execute (some .publish)).2.clone.execution.memory.effects = 1567823494 ∧
    (execute (some .publish)).2.clone.execution.memory.memory.heap.lookup 7 = none ∧
    (execute (some .publish)).2.clone.execution.memory.memory.heap.lookup 8 = none ∧
    (execute (some .publish)).2.clone.execution.memory.memory.heap.lookup 5 = some sourceCell :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem append_rollback : (execute (some .append)).1.1 = .ok (some .allocationFailure) ∧
    (execute (some .append)).2.clone.execution.memory.effects = 15672344 ∧
    (execute (some .append)).2.clone.execution.memory.memory.heap.lookup 7 = none ∧
    (execute (some .append)).2.clone.execution.memory.memory.heap.lookup 8 = none := ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem clone_oom_cleanup : (execute (some .clone)).1.1 = .ok (some .allocationFailure) ∧
    (execute (some .clone)).2.clone.execution.memory.effects = 156344 ∧
    (execute (some .clone)).2.object = none ∧
    (execute (some .clone)).2.clone.execution.memory.memory.nextId = 8 ∧
    (execute (some .clone)).2.clone.execution.memory.memory.heap.lookup 7 = none :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem source_mismatch_rejects : checkSource initial.memory source { input with item := { input.item with data := 988 } } =
    .error (.mismatch .data) ∧
    checkSource initial.memory source { input with metadata := fun selected => if selected = .astId then MemberTests.astValue none else metadata selected } =
    .error (.mismatch .astId) := ⟨by decide +kernel, by decide +kernel⟩

theorem source_fault_keeps_state :
    (operations (Insertion.Tests.allocate) (copy) bytes objects external 7 ⟨999, 0⟩ input
      (fun _ _ => arguments) (Insertion.Tests.rest none arguments)).attempt .clone {} { start with object := some 7 } =
      (.error (.source (.memory .kind .unallocated)), { start with object := some 7 }) := by rfl'

def directMade := create (Insertion.Tests.allocate) 7 input.item initial
def directClone := AssemblyClone.Physical.run (copy) 7 input directMade.2
def directCopied : ItemValue := { input with verbatim := some ⟨2, 3, ⟨7, [8, 9], 0⟩⟩ }
def directStart : State Nat := ⟨⟨⟨initial, false⟩, none⟩, none⟩
def directReady : State Nat := ⟨⟨⟨directMade.2, false⟩, none⟩, some 6⟩

theorem returned_pair (result : α × β) (value : α) (returned : result.1 = value) : result = (value, result.2) :=
  Prod.ext returned rfl

theorem composed_rollback :
    let callbacks := operations (Insertion.Tests.allocate) (copy) bytes objects external 7 source input
      (fun _ _ => Insertion.Tests.incoming) (Insertion.Tests.rest none)
    callbacks.attempt .item {} directStart = (.ok true, directReady) ∧
    ∃ installed, callbacks.attempt .clone {} directReady =
      (.ok true, ⟨⟨⟨installed, false⟩, some directCopied⟩, some 6⟩) ∧
      Installed 7 6 directCopied directClone.2 installed ∧
      ∃ after, callbacks.release .lastValue {} ⟨⟨⟨installed, false⟩, some directCopied⟩, some 6⟩ = (.ok (), after) ∧
        after.object = none ∧ after.clone.value = none ∧
        ExpressionDeinit.Lifetime.Post (AssemblyClone.Physical.payload directCopied) ⟨6, Insertion.Tests.incoming⟩ installed after.clone.execution := by
  have created : create (Insertion.Tests.allocate) 7 input.item initial = (.ok 6, directMade.2) :=
    returned_pair directMade (.ok 6) (by decide +kernel)
  have cloned : AssemblyClone.Physical.run (copy) 7 input directMade.2 = (.ok directCopied, directClone.2) := by
    let duplicated := AssemblyClone.Physical.duplicate (copy) 7 ⟨3, [8, 9], 1⟩ directMade.2
    have copiedBytes : duplicated = (.ok ⟨7, [8, 9], 0⟩, duplicated.2) :=
      returned_pair duplicated (.ok ⟨7, [8, 9], 0⟩) (by decide +kernel)
    have ran := AssemblyClone.Physical.run_duplicate (copy) 7 input ⟨2, 3, ⟨3, [8, 9], 1⟩⟩ ⟨7, [8, 9], 0⟩
      directMade.2 duplicated.2 rfl copiedBytes
    exact returned_pair directClone (.ok directCopied) (congrArg Prod.fst ran)
  have composed := create_clone_rollback (Insertion.Tests.allocate) (copy) bytes objects external 7 6 source input directCopied
    Insertion.Tests.incoming (Insertion.Tests.rest none) {} initial directMade.2 directClone.2 initial_valid
    (Or.inr (by rfl')) source_represented
    created cloned
  simpa only [directStart, directReady] using composed

def unreadable : State Nat :=
  let memory := { directMade.2.memory with heap := directMade.2.memory.heap.replace 3 { AssemblyClone.Physical.Tests.sourceCell with cells := [] } }
  { directReady with clone := { directReady.clone with execution := { directReady.clone.execution with memory := { directMade.2 with memory } } } }

theorem oom_precedes_payload_reads :
    ((callbacks (some .clone)).attempt .clone {} unreadable).1 = .ok false ∧
    ((callbacks (some .clone)).attempt .clone {} unreadable).2.clone.execution.memory.effects = 56 ∧
    ((callbacks (some .clone)).attempt .clone {} unreadable).2.clone.execution.memory.memory.heap.lookup 6 = some (Creation.cell 80) ∧
    ((callbacks).attempt .clone {} unreadable).1 = .error (.base (.insertion (.clone .sourceMismatch))) ∧
    ((callbacks).attempt .clone {} unreadable).2.clone.execution.memory.memory.heap.lookup 7 = some (AssemblyClone.Physical.cell 2 320 []) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def cloneReached : State Nat := ⟨⟨⟨directClone.2, false⟩, some directCopied⟩, some 6⟩
theorem failed_assignment_retains_clone :
    (finish 999 (.ok true) cloneReached).1 = .error (.assignment .unallocated) ∧
    (finish 999 (.ok true) cloneReached).2.clone.execution.memory.effects = 56 ∧
    (finish 999 (.ok true) cloneReached).2.clone.execution.memory.memory.heap.lookup 7 =
      some (AssemblyClone.Physical.cell 2 320 [(0, .scalar (.int false 8 8)), (1, .scalar (.int false 8 9))]) ∧
    ((finish 999 (.ok true) cloneReached).2.clone.value.map fun value => value.verbatim.map fun payload => payload.data.address) = some (some 7) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def variant (payload : Option AssemblyClone.Verbatim) : ItemValue := { input with verbatim := payload }
def variantSource (value : Compiler.ZigAir.Memory.Value) : State Nat :=
  let cell := { sourceCell with cells := (expectedCells 3 1).map fun (offset, old) => (offset, if offset = 80 then value else old) }
  let memory := { directMade.2.memory with heap := directMade.2.memory.heap.replace 5 cell }
  { directReady with clone := { directReady.clone with execution := { directReady.clone.execution with memory := { directMade.2 with memory } } } }
def variantCallback (input : ItemValue) := operations (Insertion.Tests.allocate) (copy none) bytes objects external 7 source input
  (fun _ _ => Insertion.Tests.incoming) (Insertion.Tests.rest none)
def plainResult := (variantCallback (variant none)).attempt .clone {}
  (variantSource (MemberTests.verbatimValue none))
def emptyResult := (variantCallback (variant (some ⟨4, 5, ⟨999, [], 11⟩⟩))).attempt .clone {}
  (variantSource (MemberTests.verbatimValue (some (MemberTests.payload 4 5 ⟨999, 11⟩ 0))))

theorem absent_and_empty_payloads : plainResult.1 = .ok true ∧ emptyResult.1 = .ok true ∧
    plainResult.2.clone.execution.memory.effects = 5 ∧ emptyResult.2.clone.execution.memory.effects = 5 ∧
    plainResult.2.clone.execution.memory.memory.nextId = 7 ∧ emptyResult.2.clone.execution.memory.memory.nextId = 7 ∧
    member plainResult.2.clone.execution.memory.memory ⟨6, 0⟩ .verbatim = .ok (MemberTests.verbatimValue none) ∧
    member emptyResult.2.clone.execution.memory.memory ⟨6, 0⟩ .verbatim =
      .ok (MemberTests.verbatimValue (some (MemberTests.payload 4 5 ⟨7, 0⟩ 0))) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem overwritten_target : AssemblyClone.NativeFields.install copied 7 filled.clone.execution.memory =
    .ok filled.clone.execution.memory := by
  have assigned : assign (AssemblyClone.NativeFields.values copied) 7 filled.clone.execution.memory.memory =
      .ok filled.clone.execution.memory.memory := by decide +kernel
  exact AssemblyClone.NativeFields.install_unchanged copied 7 filled.clone.execution.memory assigned

end Compiler.Extraction.AssemblyItem.Creation.NativeFields.Tests
