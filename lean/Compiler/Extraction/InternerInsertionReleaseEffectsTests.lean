/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReleaseRecursionEffects
import Compiler.Extraction.AssemblyReleaseTrace
import Compiler.Extraction.InternerInsertionSharedEffectsTests
import Compiler.Extraction.InternerInsertionPopTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.ReleaseEffectTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray Normalization.HostTrace

/-- Only release ports are exercised. Reuse the existing fixture constructor
for unused ports; no append or complete-invocation recording is claimed. -/
def observed (ops : Operations σ) : Operations (Recorded σ) :=
  { ItemEffectTests.operations (fun _ before => (none, before.effects)) (fun _ before => (none, before.effects)) with
    arguments := record ops.arguments, bytes := recordBytes ops.bytes, objects := recordObject ops.objects }

def calls (ops : Operations σ) := callbacks ops (fun _ _ _ effects => (none, effects)) false 7 6 ⟨0, 0, 0⟩
  AssemblyItem.Creation.NativeFields.Tests.source AssemblyItem.Creation.NativeFields.Tests.input
  ⟨1, 0, 0, [], 0⟩ ⟨0, []⟩ [] 0 (fun _ _ => Interner.observedHeap [] (fun _ => none))

theorem releases_erase (ops : Operations Nat) (action : Storage.Release) (owner : Storage.State) :
    Effect.Transport (State.mapEffects Recorded.effects) ((calls (observed ops)).release action owner) ((calls ops).release action owner) :=
  release_callbacks_transport (left := observed ops) (right := ops)
    (bytes_transport ops.bytes) (object_transport ops.objects) (HostTrace.transport ops.arguments)
    _ _ false 7 6 ⟨0, 0, 0⟩ AssemblyItem.Creation.NativeFields.Tests.source AssemblyItem.Creation.NativeFields.Tests.input
    _ _ none none [] 0 _ _ action owner

def run (ops : Operations Nat) (action : Storage.Release) (before : Frame Nat) :=
  (calls (observed ops)).release action {} (ItemEffectTests.capture before)

def allocation := (calls (observed Insertion.Tests.ops)).release .allocation {} (ItemEffectTests.cloned none).2
theorem allocation_cleanup : allocation.1 = .ok () ∧ allocation.2.item.object = none ∧
    (memory allocation.2).memory.heap.lookup 6 = none ∧
    (memory allocation.2).effects.allocator =
      (⟨563, [.itemAllocate 224 16 (some 80), .payloadAllocate 2 none, .itemFree 6]⟩ : Recorded Nat) :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def wrongOwner := (calls (observed Insertion.Tests.ops)).release .allocation {}
  (withMemory ItemEffectTests.created.2 { memory ItemEffectTests.created.2 with
    heap := Memory.write (memory ItemEffectTests.created.2).heap 6 (some ⟨8, .item AssemblyItem.Creation.NativeFields.Tests.input.item⟩) })

theorem allocation_rejected_before_host : wrongOwner.1 = .error (.base (.creation (.insertion (.destroy (.item (.inr (.ownership .wrongAllocator))))))) ∧
    wrongOwner.2.item.object = some 6 ∧
    (memory wrongOwner.2).effects.allocator.events = [.itemAllocate 224 16 (some 80)] :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def value := run Insertion.Tests.ops .value CleanupTests.before
theorem native_payload_cleanup : value.1 = .ok () ∧ value.2.item.clone.value = none ∧ value.2.item.object = some 4 ∧
    (memory value.2).effects.allocator = (⟨12, [.payloadFree 3 3 0]⟩ : Recorded Nat) ∧
    (memory value.2).effects.keys Insertion.Tests.key = some ⟨5, 6⟩ :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def readonlyValue := run Insertion.Tests.ops .value (CleanupTests.frame
  (AssemblyItemDeinit.Native.Tests.withItem { AssemblyItemDeinit.Native.Tests.itemCell with writable := false }))

theorem failed_invalidation_retains_release : readonlyValue.1 = .error (.cleanup (.memory .readOnly)) ∧
    readonlyValue.2.item.clone.value.isSome = true ∧ readonlyValue.2.item.object = some 4 ∧
    (memory readonlyValue.2).memory.heap.lookup 3 = none ∧
    (memory readonlyValue.2).effects.allocator = (⟨12, [.payloadFree 3 3 0]⟩ : Recorded Nat) :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem absent_payload_skips_host :
    (memory (run Insertion.Tests.ops .value (CleanupTests.frame (AssemblyItemDeinit.Native.Tests.variant none))).2).effects.allocator.events = [] :=
  by insertion_kernel_rfl

theorem missing_object_skips_host :
    let before := { CleanupTests.before with item := { CleanupTests.before.item with object := none } }
    run Insertion.Tests.ops .value before = (.error (.base (.creation .missingObject)), ItemEffectTests.capture before) := by rfl'

def last := run LastTests.ops .lastValue LastTests.before
theorem last_cleanup_order : last.1 = .ok () ∧ last.2.item.object = none ∧ last.2.item.clone.value = none ∧
    last.2.item.clone.execution.invalidated = true ∧
    (memory last.2).effects.allocator = (⟨1334, [.payloadFree 3 3 0, .itemFree 4, .free ⟨0, [3, 1, 2]⟩]⟩ : Recorded Nat) :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def lateFault := run LastTests.ops .lastValue (LastTests.withAllocation 5 { ExpressionDeinit.Native.Tests.rowCell with
  cells := ExpressionDeinit.Native.Tests.rowCell.cells.filter (fun entry => entry.1 != 48) })

theorem late_read_retains_prior_frees : lateFault.1 = .error (.expression (.fields (.memory .uninitialized))) ∧
    lateFault.2.item.object = some 999 ∧ lateFault.2.item.clone.value.isSome = true ∧
    (memory lateFault.2).effects.allocator = (⟨133, [.payloadFree 3 3 0, .itemFree 4]⟩ : Recorded Nat) :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def finalFault := run LastTests.ops .lastValue (LastTests.withAllocation 5 { ExpressionDeinit.Native.Tests.rowCell with writable := false })
theorem final_write_retains_all_frees : finalFault.1 = .error (.expression (.invalidation .readOnly)) ∧
    finalFault.2.item.clone.execution.invalidated = false ∧ finalFault.2.item.object = some 999 ∧
    (memory finalFault.2).effects.allocator = (⟨1334, [.payloadFree 3 3 0, .itemFree 4, .free ⟨0, [3, 1, 2]⟩]⟩ : Recorded Nat) :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def popped := run LastTests.ops .pop PopTests.cleaned.2
theorem pop_skips_host : popped.1 = .ok () ∧
    (memory popped.2).effects.allocator = (⟨1334, []⟩ : Recorded Nat) ∧
    readItems (memory popped.2).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 1) :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def popFault := run LastTests.ops .pop (withMemory PopTests.cleaned.2 { memory PopTests.cleaned.2 with
  heap := Memory.write (memory PopTests.cleaned.2).heap 5 none })
theorem registry_fault_retains_decrement : popFault.1 = .error (.pop (.registry .unallocated)) ∧
    readItems (memory popFault.2).memory (Owner.headerAddress ⟨6, 0⟩) = .ok (.slice itemsType ⟨5, 0⟩ 1) ∧
    (memory popFault.2).effects.allocator = (⟨1334, []⟩ : Recorded Nat) :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.ReleaseEffectTests
