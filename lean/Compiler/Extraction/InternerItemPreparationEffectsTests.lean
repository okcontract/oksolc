/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerItemPreparationEffects
import Compiler.Extraction.AssemblyPreparationTrace
import Compiler.Extraction.InsertionKernelTestSupport
import Compiler.Extraction.AssemblyItemCreationFieldTests
import Compiler.Extraction.InternerNativeRecursionEffectsTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.ItemEffectTests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Normalization.HostTrace
open AssemblyItem.Creation.NativeFields.Tests (input source directStart directReady directCopied)

/-- Only item preparation is exercised here. Unused ports refuse requests;
this fixture makes no complete-insertion or cleanup-recording claim. -/
def operations (create : AssemblyItem.Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ) : Operations σ where
  arguments := { allocate := fun _ _ _ effects => (none, effects), free := fun _ before => before.effects }
  create := create
  copy := copy
  bytes := fun _ before => before.effects
  objects := fun _ before => before.effects
  append := fun _ before => (false, before.effects)
  probe := fun _ before => (false, before.effects)

def ordinary (item copy : Option Nat) := operations
  (AssemblyItem.Creation.Insertion.Tests.allocate item) (AssemblyItem.Creation.NativeFields.Tests.copy copy)
def observed (item copy : Option Nat) := operations
  (recordCreate (AssemblyItem.Creation.Insertion.Tests.allocate item)) (recordCopy (AssemblyItem.Creation.NativeFields.Tests.copy copy))

def callback (ops : Operations σ) (site : Storage.Allocation) (address : Compiler.ZigAir.Memory.Address) :
    Frame σ → Except Fault Bool × Frame σ :=
  (callbacks ops (fun _ _ _ effects => (none, effects)) false 7 0 ⟨0, 0, 0⟩ address input ⟨1, 0, 0, [], 0⟩ ⟨0, []⟩ [] 0
    (fun _ _ => Interner.observedHeap [] (fun _ => none))).attempt site {}

theorem native_callbacks_erase (item copy : Option Nat) (site : Storage.Allocation)
    (preparation : site = .item ∨ site = .clone) (address : Compiler.ZigAir.Memory.Address) :
    Effect.Transport (State.mapEffects Recorded.effects)
      (callback (observed item copy) site address) (callback (ordinary item copy) site address) :=
  preparation_callback_transport (HostTrace.create_transport _) (HostTrace.copy_transport _)
    _ _ false 7 0 ⟨0, 0, 0⟩ address input _ _ [] 0 _ _ none none site preparation {}

def lift (state : AssemblyItem.Creation.NativeFields.State Nat) : Frame Nat :=
  ⟨state.mapEffects (fun effects => (⟨fun _ => none, effects⟩ : Publication.Effects Nat)), none⟩
def capture (state : Frame Nat) := state.mapEffects (fun effects => (⟨effects, []⟩ : Recorded Nat))
def initial := capture (lift directStart)
def created (response : Option Nat := some 80) := callback (observed response (some 320)) .item source initial
def cloned (response : Option Nat := some 320) := callback (observed (some 80) response) .clone source created.2

-- Reuse kernel reflexivity for closed native states containing heap functions.
theorem actual_creation_and_clone :
    created.1 = .ok true ∧ cloned.1 = .ok true ∧ cloned.2.item.object = some 6 ∧
    cloned.2.item.clone.value = some directCopied ∧ (memory cloned.2).memory.nextId = 8 ∧
    (memory cloned.2).effects.allocator.effects = 56 ∧
    (memory cloned.2).effects.allocator.events = [.itemAllocate 224 16 (some 80), .payloadAllocate 2 (some 320)] :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem item_refusal : (created none).1 = .ok false ∧ (created none).2.item.object = none ∧
    (memory (created none).2).memory = (memory initial).memory ∧
    (memory (created none).2).effects.allocator = (⟨5, [.itemAllocate 224 16 none]⟩ : Recorded Nat) :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem clone_refusal_keeps_item : (cloned none).1 = .ok false ∧ (cloned none).2.item.object = some 6 ∧
    (cloned none).2.item.clone.value = none ∧ (memory (cloned none).2).memory = (memory created.2).memory ∧
    (memory (cloned none).2).effects.allocator =
      (⟨56, [.itemAllocate 224 16 (some 80), .payloadAllocate 2 none]⟩ : Recorded Nat) :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem invalid_item_response : (created (some 64)).1 = .error (.item (.base (.creation (.memory .memoryValidity)))) ∧
    (memory (created (some 64)).2).memory = (memory initial).memory ∧
    (memory (created (some 64)).2).effects.allocator.events = [.itemAllocate 224 16 (some 64)] :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem source_fault_precedes_copy : callback (observed (some 80) (some 320)) .clone ⟨999, 0⟩ created.2 =
    (.error (.item (.source (.memory .kind .unallocated))), created.2) := by insertion_kernel_rfl

def unreadable := capture (lift AssemblyItem.Creation.NativeFields.Tests.unreadable)
def readFailed := callback (observed (some 80) (some 320)) .clone source unreadable

theorem failed_read_retains_allocation :
    readFailed.1 = .error (.item (.base (.insertion (.clone .sourceMismatch)))) ∧
    (memory readFailed.2).memory.nextId = 8 ∧
    (memory readFailed.2).memory.heap.lookup 7 = some (AssemblyClone.Physical.cell 2 320 []) ∧
    (memory readFailed.2).effects.allocator = (⟨56, [.payloadAllocate 2 (some 320)]⟩ : Recorded Nat) :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem refusal_skips_payload_read :
    (callback (observed (some 80) none) .clone source unreadable).1 = .ok false ∧
    (memory (callback (observed (some 80) none) .clone source unreadable).2).memory = (memory unreadable).memory ∧
    (memory (callback (observed (some 80) none) .clone source unreadable).2).effects.allocator.events = [.payloadAllocate 2 none] :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def invalidTarget := { created.2 with item := { created.2.item with object := some 999 } }
def assignmentFailed := callback (observed (some 80) (some 320)) .clone source invalidTarget

theorem assignment_fault_retains_clone : assignmentFailed.1 = .error (.item (.assignment .unallocated)) ∧
    assignmentFailed.2.item.clone.value = some directCopied ∧ (memory assignmentFailed.2).memory.nextId = 8 ∧
    (memory assignmentFailed.2).effects.allocator.events = [.itemAllocate 224 16 (some 80), .payloadAllocate 2 (some 320)] :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

def collision : Frame (Recorded Nat) := { initial with item := { initial.item with clone := { initial.item.clone with
  execution := { initial.item.clone.execution with memory := { memory initial with
    heap := Memory.write (memory initial).heap 6 (some ⟨9, .bytes 8⟩) } } } } }
def collisionResult := callback (observed (some 80) (some 320)) .item source collision

theorem collision_retains_typed_allocation : collisionResult.1 = .error (.item (.base (.creation .registryCollision))) ∧
    (memory collisionResult.2).memory.heap.lookup 6 = some (AssemblyItem.Creation.cell 80) ∧
    (memory collisionResult.2).heap 6 = some ⟨9, .bytes 8⟩ ∧
    (memory collisionResult.2).effects.allocator.events = [.itemAllocate 224 16 (some 80)] :=
  ⟨by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl, by insertion_kernel_rfl⟩

theorem absent_payload_skips_host :
    let before := AssemblyClone.Physical.Tests.initial.mapEffects (fun effects => (⟨effects, []⟩ : Recorded Nat))
    AssemblyClone.Physical.run (recordCopy (AssemblyClone.Physical.Tests.request none)) 7
      { AssemblyClone.Physical.Tests.input with verbatim := none } before =
      (.ok { AssemblyClone.Physical.Tests.input with verbatim := none }, before) := rfl

theorem empty_payload_skips_host :
    let before := AssemblyClone.Physical.Tests.initial.mapEffects (fun effects => (⟨effects, []⟩ : Recorded Nat))
    (AssemblyClone.Physical.run (recordCopy (AssemblyClone.Physical.Tests.request none)) 7 AssemblyClone.Physical.Tests.emptyInput before).2 = before := by rfl'

theorem history_retained (leading : List Event) :
    let before := AssemblyClone.Physical.Tests.initial.mapEffects (fun effects => (⟨effects, leading⟩ : Recorded Nat))
    (AssemblyClone.Physical.run (recordCopy (AssemblyClone.Physical.Tests.request none)) 7 AssemblyClone.Physical.Tests.input before).2.effects.events =
      leading ++ [.payloadAllocate 3 none] := by rfl'

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native.ItemEffectTests
