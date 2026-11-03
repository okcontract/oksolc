/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNative
import Compiler.Extraction.InternerNativeStep
import Compiler.Extraction.InternerNativeSpareInsertionTests
import Compiler.Extraction.InternerNativeGrowingInsertionTests
import Compiler.Extraction.InternerNativeFirstInsertionTests
import Compiler.Extraction.InternerNativeBackingFailureTests
import Compiler.Extraction.InternerNativeGrowingRollbackTests
import Compiler.Extraction.InternerNativeUnrelocatedRollbackTests
import Compiler.Extraction.InternerNativeCacheHitTests
import Compiler.Extraction.InternerConstructorTakeFailureTests
import Compiler.Extraction.InternerConstructorClassificationTests
import Compiler.Extraction.InternerConstructorEntryFailureTests
import Compiler.Extraction.InternerNativePreparationFailure
import Compiler.Extraction.InternerNativeCapacityFailure
import Compiler.Extraction.ObservedInsertionFailureTests
import Compiler.Extraction.StorageExecutionPolicyTests
import Compiler.Extraction.InternerInsertionNativeControls
import Compiler.Extraction.ExpressionInvalidationTests
import Compiler.Extraction.InternerInsertionNativeDeinitTests
import Compiler.Extraction.ExpressionDeinitNativeTests
import Compiler.Extraction.InternerInsertionLastTests
import Compiler.Extraction.InternerInsertionPopTests
import Compiler.Extraction.InternerInsertionRollbackTests
import Compiler.Extraction.InternerInsertionOuterCleanupTests
import Compiler.Extraction.InternerInsertionAppendOwnershipTests
import Compiler.Extraction.InternerInsertionPreparationTests
import Compiler.Extraction.InternerInsertionPreparationFailureTests
import Compiler.Extraction.InternerInsertionFirstTests
import Compiler.Extraction.InternerInsertionGrowingTests
import Compiler.Extraction.InternerInsertionGrowingSuccessTests
import Compiler.Extraction.InternerCallerOriginTests
import Compiler.Extraction.InternerCallerPublicationCompletionTests
import Compiler.Extraction.InternerCallerInsertionInputTests
import Compiler.Extraction.InternerCallerInsertionFirstSuccessTests
import Compiler.Extraction.InternerPublicationGraphTests
import Compiler.Extraction.InternerCallerInsertionSpareSuccessTests
import Compiler.Extraction.InternerCallerInsertionGrowingSuccessTests
import Compiler.Extraction.InternerCallerInsertionGrowingRollbackTests
import Compiler.Extraction.InternerCallerInsertionGrowthAllocationFailureTests
import Compiler.Extraction.InternerCallerInsertionTransferredGrowthTests
import Compiler.Extraction.InternerCallerInsertionTransferredAllocationFailureTests
import Compiler.Extraction.InternerCallerTransferredPreparationFailureTests
import Compiler.Extraction.InternerInsertionCountTests
import Compiler.Extraction.InternerCallerInsertionCapacityTests
import Compiler.Extraction.InternerCallerInsertionCapacityCompletionTests
import Compiler.Extraction.InternerCallerCustodyTests
import Compiler.Extraction.InternerCallerNativeRoutingTests
import Compiler.Extraction.InternerConstructorItemTests
import Compiler.Extraction.InternerRecursiveChildTests
import Compiler.Extraction.InternerConstructorArgumentsTests
import Compiler.Extraction.InternerShiftInputTests
import Compiler.Extraction.InternerRecursiveNonemptyTests
import Compiler.Extraction.InternerAlgebraicInputTests
import Compiler.Extraction.InternerPairInputTests
import Compiler.Extraction.InternerLiteralInputTests
import Compiler.Extraction.InternerViewInputTests
import Compiler.Extraction.InternerRecursiveBorrowedTests
import Compiler.Extraction.InternerNativeRecursionTests
import Compiler.Extraction.InternerNativeGraphTests
import Compiler.Extraction.InternerNativeLocalTests
import Compiler.Extraction.InternerNativeConstantTests
import Compiler.Extraction.InternerNativeWordConstantTests
import Compiler.Extraction.InternerNativeConstantFoldTests
import Compiler.Extraction.InternerNativeConstantFoldGrowthTests
import Compiler.Extraction.InternerNativeConstantNegationTests
import Compiler.Extraction.InternerRecursiveGrowthTests
import Compiler.Extraction.RepresentativeRemapGrowthTests
import Compiler.Extraction.InternerInsertionGrowthTests
import Compiler.Extraction.InsertionKernelTestSupport
import Compiler.Extraction.InternerInsertionTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray
open AssemblyClone.NativeFields.QueryTests (old logical copied ready ownerCell incoming request)
open AssemblyItem.Creation.NativeFields.Tests (input source)

def rows (first : Bool) : List Storage.Cell := if first then [] else [old]
def key : Key := ⟨input.item.kind, 254, input.item.data, incoming.items, 31⟩
def lift (state : Session Nat) : Session (Publication.Effects Nat) :=
  ⟨state.heap, state.memory, ⟨fun _ => none, state.effects⟩⟩

theorem registered_run (safety first : Bool) :
    Append.Registered.run safety (fun _ => request) 7 6 (rows first) logical (ready safety first) =
      (.ok true, AssemblyClone.NativeFields.RegistryTests.reached safety first) := by
  have native : AssemblyClone.NativeFields.QueryTests.append safety first =
      ((.ok (some ()), (AssemblyClone.NativeFields.RegistryTests.reached safety first).memory), (AssemblyClone.NativeFields.RegistryTests.reached safety first).effects) :=
    Prod.ext (Prod.ext (AssemblyClone.NativeFields.RegistryTests.registered_execution safety first).1 rfl) rfl
  cases first with
  | true =>
    exact Append.Registered.completed safety (fun _ => request) 7 6 10 5 [] logical (ready safety true) (AssemblyClone.NativeFields.RegistryTests.reached safety true)
      native rfl (by cases safety <;> decide +kernel)
      (by have fresh := Append.Registered.admit_first 7 (ready safety true) (AssemblyClone.NativeFields.QueryTests.installed safety true).valid
          have next : (ready safety true).memory.nextId = 10 := by cases safety <;> decide +kernel
          rw [next] at fresh
          exact fresh)
  | false =>
    exact Append.Registered.completed safety (fun _ => request) 7 6 7 2 [old] logical (ready safety false) (AssemblyClone.NativeFields.RegistryTests.reached safety false)
      native rfl (by cases safety <;> decide +kernel)
      (Append.Registered.admit_vector 7 7 [old] (ready safety false) (AssemblyClone.NativeFields.RegistryTests.ready_registered safety false 7 _ (by rfl')))

/-- Fixed region responses reuse the independently proved create/clone/query
fixture. The old Boolean append callback deliberately fails: this execution
must reach the native append instead. -/
def fixed : Operations Nat :=
  { Insertion.Tests.ops with
    create := AssemblyItem.Creation.Insertion.Tests.allocate
    copy := AssemblyItem.Creation.NativeFields.Tests.copy
    append := fun _ state => (false, state.effects + 1000000) }
def world (safety first : Bool) : World (Publication.Effects Nat) :=
  ⟨Interner.observedHeap (rows first) (fun _ => none), lift (AssemblyClone.NativeFields.QueryTests.initial safety first)⟩
def execute (safety first : Bool) := execution fixed (fun _ => request) safety 7 6 ⟨1, 0, 1⟩ source
  Insertion.Tests.model input key incoming false (rows first) (world safety first)
def filled (safety first : Bool) : Frame Nat :=
  ⟨⟨⟨⟨lift (AssemblyClone.NativeFields.RegistryTests.reached safety first), false⟩, some copied⟩, some 8⟩, none⟩

theorem same_execution (safety first : Bool) :
    (execute safety first).1.1 = .ok (some .success) ∧ (execute safety first).2 = filled safety first := by
  cases safety <;> cases first <;> exact ⟨by decide +kernel, by insertion_kernel_rfl⟩

/-- Actual item creation, complete clone assignment, native append and the
ownership handoff run in one source-bound insertion execution. Its accepted
queries follow from residency and native correspondence, not final Good. -/
theorem accepted_queries (safety first : Bool) :
    BorrowedQuery.Native.AcceptedQueries 7 (Owner.headerAddress ⟨6, 0⟩) (AssemblyClone.NativeFields.RegistryTests.cells first)
      (memory (execute safety first).2) := by
  rw [(same_execution safety first).2]
  have previous := AssemblyClone.NativeFields.RegistryTests.registered_execution safety first
  exact BorrowedQuery.Native.of_resident 7 (Owner.headerAddress ⟨6, 0⟩) (AssemblyClone.NativeFields.RegistryTests.cells first) _
    ⟨previous.2.1.memory, previous.2.1.related, previous.2.1.injected⟩ previous.2.2.2.1 previous.2.2.2.2.1

theorem transferred_borrow (safety first : Bool) :
    BorrowedQuery.observe 7 (if first then 0 else 1) 254
      (⟨Interner.observedHeap (AssemblyClone.NativeFields.RegistryTests.cells first) (fun _ => none), memory (execute safety first).2⟩ : World (Publication.Effects Nat)) =
      .ok (some incoming) ∧
    Good (view incoming) incoming.items
      (⟨Interner.observedHeap (AssemblyClone.NativeFields.RegistryTests.cells first) (fun _ => none), memory (execute safety first).2⟩ : World (Publication.Effects Nat)) := by
  rw [(same_execution safety first).2]
  have previous := AssemblyClone.NativeFields.RegistryTests.accepted_borrow safety first
  refine ⟨?_, ⟨⟨previous.2.1.memory, previous.2.1.related, previous.2.1.injected⟩, previous.2.2⟩⟩
  have observed := ((accepted_queries safety first).2
    (Interner.observedHeap (AssemblyClone.NativeFields.RegistryTests.cells first) (fun _ => none)) rfl).1
    (if first then 0 else 1) 254
  rw [(same_execution safety first).2] at observed
  rw [observed]
  cases first <;> decide +kernel

def allocate (failure : Option Storage.Allocation) : Backing.Registry.Allocate Nat :=
  fun _ _ _ effects => (if failure = some .append then none else some 4096, effects * 10 + 7)
def dynamic (safety first deterministic : Bool) (failure : Option Storage.Allocation := none) :=
  execution (Insertion.Tests.ops failure) (allocate failure) safety 7 6 ⟨1, 0, 1⟩ source
    Insertion.Tests.model input key incoming deterministic (rows first) (world safety first)

theorem deterministic_success (safety first : Bool) :
    (dynamic safety first true).1.1 = .ok (some .success) ∧
    (dynamic safety first true).2.item.object = some 9 ∧
    ownsArguments 7 ⟨8, incoming.items⟩ (memory (dynamic safety first true).2).heap = true ∧
    (memory (dynamic safety first true).2).effects.keys key = some ⟨0, if first then 0 else 1⟩ ∧
    readItems (memory (dynamic safety first true).2).memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨if first then 11 else 7, 0⟩ (if first then 1 else 2)) := by
  cases safety <;> cases first <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem actual_descriptor (safety first deterministic : Bool) :
    representativeFields (memory (dynamic safety first deterministic).2).memory (Owner.headerAddress ⟨6, 0⟩)
      (if first then 0 else 1) = .ok (.ok [
        .pointer (.pointer true false AssemblyItem.allocationType) ⟨if deterministic then 9 else 8, 0⟩,
        .slice Expression.argumentsType ⟨if deterministic then 8 else incoming.address, 0⟩ incoming.items.length,
        .scalar (.int false 32 (if first then 0 else 1)), .scalar (.int false 32 31)]) := by
  cases safety <;> cases first <;> cases deterministic <;> decide +kernel

theorem append_oom (safety deterministic : Bool) :
    (dynamic safety true deterministic (some .append)).1.1 = .ok (some .allocationFailure) ∧
    (dynamic safety true deterministic (some .append)).2.item.object = none ∧
    (memory (dynamic safety true deterministic (some .append)).2).heap 0 = none ∧
    (memory (dynamic safety true deterministic (some .append)).2).memory.heap.lookup (if deterministic then 10 else 9) = none ∧
    (memory (dynamic safety true deterministic (some .append)).2).effects.allocator = (if deterministic then 15672344 else 567234) ∧
    readItems (memory (dynamic safety true deterministic (some .append)).2).memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨999, 19⟩ 0) := by
  cases safety <;> cases deterministic <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem publication_result (safety first : Bool) :
    (dynamic safety first true (some .publish)).1.1 = .ok (some .allocationFailure) := by
  cases safety <;> cases first <;> decide +kernel

theorem publication_object (safety first : Bool) :
    (dynamic safety first true (some .publish)).2.item.object = none := by
  cases safety <;> cases first <;> decide +kernel

theorem publication_arguments (safety first : Bool) :
    (memory (dynamic safety first true (some .publish)).2).heap 8 = none := by
  cases safety <;> cases first <;> decide +kernel

theorem publication_item (safety first : Bool) :
    (memory (dynamic safety first true (some .publish)).2).memory.heap.lookup 9 = none := by
  cases safety <;> cases first <;> decide +kernel

theorem publication_marker (safety first : Bool) :
    (dynamic safety first true (some .publish)).2.item.clone.execution.invalidated = true := by
  cases safety <;> cases first <;> decide +kernel

theorem publication_row (safety first : Bool) :
    ExpressionDeinit.Native.Fields.item (memory (dynamic safety first true (some .publish)).2).memory
      ⟨if first then 11 else 7, if first then 0 else 32⟩ = .error (.memory .uninitialized) := by
  cases safety <;> cases first <;> decide +kernel

theorem publication_header (safety first : Bool) :
    readItems (memory (dynamic safety first true (some .publish)).2).memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨if first then 11 else 7, 0⟩ (if first then 0 else 1)) := by
  cases safety <;> cases first <;> decide +kernel

theorem publication_scope (safety first : Bool) :
    (dynamic safety first true (some .publish)).1.1 = .ok (some .allocationFailure) ∧
    (dynamic safety first true (some .publish)).2.item.object = none ∧
    (memory (dynamic safety first true (some .publish)).2).heap 8 = none ∧
    (memory (dynamic safety first true (some .publish)).2).memory.heap.lookup 9 = none ∧
    (dynamic safety first true (some .publish)).2.item.clone.execution.invalidated = true ∧
    ExpressionDeinit.Native.Fields.item (memory (dynamic safety first true (some .publish)).2).memory
      ⟨if first then 11 else 7, if first then 0 else 32⟩ = .error (.memory .uninitialized) ∧
    readItems (memory (dynamic safety first true (some .publish)).2).memory (Owner.headerAddress ⟨6, 0⟩) =
      .ok (.slice itemsType ⟨if first then 11 else 7, 0⟩ (if first then 0 else 1)) :=
  ⟨publication_result safety first, publication_object safety first, publication_arguments safety first, publication_item safety first, publication_marker safety first, publication_row safety first, publication_header safety first⟩

theorem publication_normalized (safety first : Bool) :
    (memory (dynamic safety first true (some .publish)).2).memory.heap.lookup incoming.address = none ∧
    (memory (dynamic safety first true (some .publish)).2).heap incoming.address = none := by
  cases safety <;> cases first <;> exact ⟨by decide +kernel, by insertion_kernel_rfl⟩

theorem publication_vector (safety first : Bool) :
    (match (memory (dynamic safety first true (some .publish)).2).heap (if first then 11 else 7) with
      | some ⟨7, .representatives cells⟩ => some cells.length
      | _ => none) = some (if first then 0 else 1) := by
  cases safety <;> cases first <;> decide +kernel

theorem publication_capacity (safety first : Bool) :
    readField (memory (dynamic safety first true (some .publish)).2).memory (Owner.headerAddress ⟨6, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 (if first then 5 else 2))) := by
  cases safety <;> cases first <;> decide +kernel

theorem publication_old_row (safety : Bool) :
    representativeFields (memory (dynamic safety false true (some .publish)).2).memory (Owner.headerAddress ⟨6, 0⟩) 0 =
      representativeFields (world safety false).memory.memory (Owner.headerAddress ⟨6, 0⟩) 0 := by
  cases safety <;> decide +kernel

def changedRegistry (safety : Bool) (allocation : Option Memory.Allocation) : Session Nat :=
  { ready safety false with heap := Memory.write (ready safety false).heap 7 allocation }
def registryRun (safety : Bool) (allocation : Option Memory.Allocation) :=
  Append.Registered.run safety (fun _ => request) 7 6 [old] logical (changedRegistry safety allocation)

theorem registry_rejections (safety : Bool) :
    (registryRun safety (some ⟨8, .representatives [old]⟩)).1 = .error (.registry .wrongAllocator) ∧
    (registryRun safety (some ⟨7, .bytes 64⟩)).1 = .error (.registry .wrongType) ∧
    (registryRun safety none).1 = .error (.registry .unallocated) ∧
    readItems (registryRun safety none).2.memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨7, 0⟩ 2) ∧
    (registryRun safety none).2.heap 7 = none := by
  cases safety <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def readonly (safety : Bool) : Session Nat := { ready safety false with memory := { (ready safety false).memory with
  heap := (ready safety false).memory.heap.replace 7 { AssemblyClone.NativeFields.QueryTests.backing with writable := false } } }
def readonlyRun (safety : Bool) := Append.Registered.run safety (fun _ => request) 7 6 [old] logical (readonly safety)

theorem partial_store_retained (safety : Bool) :
    (readonlyRun safety).1 = .error (.memory .readOnly) ∧
    readItems (readonlyRun safety).2.memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨7, 0⟩ 2) ∧
    (readonlyRun safety).2.effects = (ready safety false).effects ∧
    (readonlyRun safety).2.heap = (ready safety false).heap := by
  cases safety <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by insertion_kernel_rfl⟩

theorem header_mismatch_rejected (safety : Bool) :
    (Append.Registered.run safety (fun _ => request) 7 6 [] logical (ready safety false)).1 = .error (.memory .malformed) := by
  cases safety <;> decide +kernel

theorem missing_locals (safety : Bool) :
    (append safety (fun _ => request) 7 6 [] input key incoming 0 { aliasesNormalized := true }
      (⟨⟨⟨⟨lift (ready safety true), false⟩, none⟩, none⟩, none⟩ : Frame Nat)).1 = .error (.base .missingValue) := by
  cases safety <;> decide +kernel

theorem early_oom (safety deterministic : Bool) :
    (dynamic safety true deterministic (some .item)).1.1 = .ok (some .allocationFailure) ∧
    (dynamic safety true deterministic (some .clone)).1.1 = .ok (some .allocationFailure) ∧
    (dynamic safety true true (some .arguments)).1.1 = .ok (some .allocationFailure) ∧
    (dynamic safety true deterministic (some .clone)).2.item.object = none ∧
    (memory (dynamic safety true deterministic (some .clone)).2).heap 0 = none := by
  cases safety <;> cases deterministic <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def wrongSource (safety : Bool) := execution fixed (fun _ => request) safety 7 6 ⟨1, 0, 1⟩ source
  Insertion.Tests.model { input with item := { input.item with data := 988 } } { key with data := 988 }
  incoming false [] (world safety true)

theorem source_rejection_retained (safety : Bool) :
    (wrongSource safety).1.1 = .error (.item (.source (.mismatch .data))) ∧
    (wrongSource safety).2.item.object = some 8 ∧
    (memory (wrongSource safety).2).effects.allocator = 5 ∧
    (memory (wrongSource safety).2).memory.heap.lookup 8 = some (AssemblyItem.Creation.cell 80) := by
  cases safety <;> exact ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

def full (safety : Bool) : Session Nat := { ready safety false with memory := { (ready safety false).memory with
  heap := ((ready safety false).memory.heap.replace 6 { ownerCell safety false with cells := (Growth.Tests.nativeCells safety [(16, .pointer RepresentativeArray.Publication.pointerType ⟨7, 0⟩),
     (24, .scalar (.int false 64 1)), (32, .scalar (.int false 64 1))]) }).replace 7
    { AssemblyClone.NativeFields.QueryTests.backing with type := .array 1 Expression.allocationType } } }

theorem nonempty_growth_scope (safety : Bool) :
    (full safety).memory.valid = true ∧
    Append.Registered.run safety (fun _ => request) 7 6 [old] logical (full safety) =
      (.error (.memory .unsupported), full safety) := by
  cases safety <;> exact ⟨by decide +kernel, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.Tests
