/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionLifetime
import Compiler.Extraction.ExpressionPayloadTests
import Compiler.ZigAir.MemoryInvariant

namespace Compiler.Extraction.ExpressionDeinit.Lifetime.Tests
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.ZigAir.Memory.WordArray

/-- The caller supplies an already-owned object with the complete declaration. Item creation/clone and
native field contents are still outside this fixture's implementation claim. -/
def itemValue := Payload.Tests.storedCell.item
def object : Compiler.ZigAir.Memory.Allocation := ⟨80, AssemblyItem.viewType, [], true, false⟩
def initial : Session Nat := ⟨write Payload.Tests.initial.heap 4 (some ⟨7, .item itemValue⟩),
  ⟨(4, object) :: Payload.Tests.initial.memory.heap, 5, 304⟩, 0⟩
def incoming := Payload.Tests.incoming
def inputHandle := Payload.Tests.inputHandle
def external := Payload.Tests.external
def payloads : Nat → Option AssemblyItemDeinit.Bytes := fun id =>
  if id = 4 then some AssemblyItemDeinit.Tests.payload else none

def bytes := Payload.Tests.release
def objects : AssemblyItem.Release Nat := fun id before =>
  if id = 4 ∧ before.memory.heap.lookup 3 = none then before.effects * 10 + 3 else 999

theorem initial_valid : Valid initial := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro allocator id values nonempty stored
    by_cases same : id = 4
    · subst id; simp [initial, write] at stored
    · obtain ⟨⟨old, found, typed, writable, stack⟩, represented⟩ := Payload.Tests.initial_valid.related
        allocator id values nonempty (by simpa [initial, write, same] using stored)
      have framed : initial.memory.heap.lookup id = Payload.Tests.initial.memory.heap.lookup id := by
        simp [initial, Compiler.ZigAir.Memory.Heap.lookup_cons, Ne.symm same]
      exact ⟨⟨old, framed.trans found, typed, writable, stack⟩, represented_frame _ _ represented framed⟩
  · intro id allocation stored
    by_cases same : id = 4
    · subst id; exact ⟨object, rfl, rfl⟩
    · obtain ⟨old, found, _persistent⟩ := Payload.Tests.initial_valid.injected id allocation (by simpa [initial, write, same] using stored)
      exact ⟨old, by simpa [initial, Compiler.ZigAir.Memory.Heap.lookup_cons, Ne.symm same] using found, _persistent⟩

theorem object_owned : AssemblyItem.Owned 7 4 initial := ⟨⟨itemValue, rfl⟩, object, rfl, rfl, rfl, rfl⟩
theorem payload_owned : ∀ slice, payloads 4 = some slice → AssemblyItemDeinit.Owned 7 slice initial := by
  intro slice selected
  have same : AssemblyItemDeinit.Tests.payload = slice := by simpa [payloads] using selected
  subst slice
  exact Or.inr ⟨rfl, AssemblyItemDeinit.Tests.cell, rfl, rfl, rfl, rfl, rfl⟩

def taken := takeOwned Cache.normalizationOwnershipCode external 7 inputHandle initial
def duplicate : Descriptor := ⟨4, ⟨5, incoming.items⟩⟩
theorem taken_result : taken.1 = .ok (duplicate.arguments, inputHandle) := by rfl'

theorem taken_contract : Valid taken.2 ∧ SliceValid 7 taken.2.heap duplicate.arguments ∧
    AssemblyItem.Owned 7 4 taken.2 ∧
    (∀ slice, payloads 4 = some slice → AssemblyItemDeinit.Owned 7 slice taken.2) := by
  have contents : Represents initial.memory (view incoming) incoming.items :=
    (initial_valid.related 7 0 [0] (by decide) (by rfl')).2
  have ready : Ready 7 (view incoming) incoming.items inputHandle initial :=
    ⟨initial_valid, contents, contents, (by intro _ impossible; cases impossible), (by intro _ _ impossible; cases impossible)⟩
  obtain ⟨result, after, executed, post⟩ := take_refines external 7 (view incoming) incoming.items inputHandle initial ready
    ExpressionDeinit.Tests.external_admitted
  have same : result = .ok (duplicate.arguments, inputHandle) := (congrArg Prod.fst executed).symm.trans taken_result
  rw [same] at post
  have memory := congrArg Prod.snd executed
  have valid : Valid taken.2 ∧ SliceValid 7 taken.2.heap duplicate.arguments := memory.symm ▸ ⟨post.ready.valid, post.live⟩
  refine ⟨valid.1, valid.2, ⟨⟨itemValue, by rfl'⟩, object, by rfl', rfl, rfl, rfl⟩, ?_⟩
  intro slice selected
  have same : AssemblyItemDeinit.Tests.payload = slice := by simpa [payloads] using selected
  subst slice
  exact Or.inr ⟨by rfl', AssemblyItemDeinit.Tests.cell, by rfl', rfl, rfl, rfl, rfl⟩

/-- Adapt only the fault type of the existing non-destructor fixture operations. -/
def rest : Storage.Operations (State Nat) (Fault ItemFault) where
  attempt site ownership before :=
    let (result, after) := Payload.Tests.rest.attempt site ownership before
    (result.mapError fun fault => match fault with
      | .arguments reason => .arguments reason
      | _ => .invalidDescriptor, after)
  release action ownership before :=
    let (result, after) := Payload.Tests.rest.release action ownership before
    (result.mapError fun fault => match fault with
      | .arguments reason => .arguments reason
      | _ => .invalidDescriptor, after)

def callbacks := insertionOperations bytes objects external 7 payloads (fun _ _ => duplicate) rest
def insertion := insertProgram.execute ⟨true, true, fun _ => false⟩ callbacks {} ⟨initial, false⟩
def rollbackState : State Nat := ⟨{ taken.2 with effects := 15678 }, false⟩

theorem rollback_contract (ownership : Storage.State) :
    let executed := Storage.Release.lastValue.execute callbacks ownership rollbackState
    executed.1.1 = .ok () ∧ Post (payloads duplicate.item) duplicate rollbackState.memory executed.2 :=
  last_value_preserved bytes objects external 7 payloads (fun _ _ => duplicate) rest ownership rollbackState rfl
    ⟨taken_contract.1.memory, taken_contract.1.related, taken_contract.1.injected⟩ taken_contract.2.2.1
    taken_contract.2.1 taken_contract.2.2.2

theorem complete_rollback : insertion.1.1 = .ok (some .allocationFailure) ∧
    insertion.2.memory.effects = 1567823494 ∧
    insertion.2.memory.heap 0 = none ∧ insertion.2.memory.heap 3 = none ∧ insertion.2.memory.heap 4 = none ∧ insertion.2.memory.heap 5 = none ∧
    insertion.2.memory.memory.heap.lookup 0 = none ∧ insertion.2.memory.memory.heap.lookup 3 = none ∧
    insertion.2.memory.memory.heap.lookup 4 = none ∧ insertion.2.memory.memory.heap.lookup 5 = none ∧
    insertion.1.2.appended = false ∧ insertion.2.invalidated = true :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem borrowed_cells_and_history : insertion.2.memory.memory.heap.lookup 1 = some Arguments.Tests.secondCell ∧
    insertion.2.memory.memory.heap.lookup 2 = some Arguments.Tests.scratchCell ∧
    insertion.2.memory.memory.nextId = 6 ∧ insertion.2.memory.memory.nextAddress = 312 :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

def objectPointer : Compiler.ZigAir.Memory.Value := .pointer (.pointer true false AssemblyItem.allocationType) ⟨4, 0⟩
theorem object_alias_dead : Compiler.ZigAir.Memory.load insertion.2.memory.memory objectPointer = .error .unallocated := by
  obtain ⟨_, _, _, _, _, _, _, _, dead, _, _, _⟩ := complete_rollback
  simp [Compiler.ZigAir.Memory.load, objectPointer, AssemblyItem.allocationType,
    Compiler.ZigAir.Memory.Ty.layout, Compiler.ZigAir.Memory.access, dead, bind, Except.bind]
theorem fields_unsupported : Compiler.ZigAir.Memory.load initial.memory objectPointer = .error .unsupported ∧
    Compiler.ZigAir.Memory.load initial.memory (.pointer (.pointer true false word) ⟨4, 0⟩) = .error .unsupported :=
  ⟨by rfl', by rfl'⟩
theorem scalar_store_unsupported : Compiler.ZigAir.Memory.store initial.memory
    (.pointer (.pointer true false word) ⟨4, 0⟩) (number 0) = .error .unsupported := by
  have access : Compiler.ZigAir.Memory.access initial.memory ⟨4, 0⟩ ⟨4, 4⟩ true = .ok object := by rfl'
  have unsupported : Compiler.ZigAir.Memory.acceptsView object.type 0 (number 0).type = false := rfl
  have write : Compiler.ZigAir.Memory.writeCell object 0 (number 0) = .error .unsupported := by
    simp only [Compiler.ZigAir.Memory.writeCell, Compiler.ZigAir.Memory.Cells.write, number_valid, unsupported,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, bind, Except.bind]
  simp only [Compiler.ZigAir.Memory.store, number_typed, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, show word.layout = some ⟨4, 4⟩ from rfl, access, write, bind, Except.bind]
theorem zero_alignment_rejects : (Compiler.ZigAir.Memory.Ty.record "invalid" ⟨224, 0⟩).layout = none := rfl

def withObject (updated : Compiler.ZigAir.Memory.Allocation) : Session Nat :=
  { initial with memory := { initial.memory with heap := (4, updated) :: initial.memory.heap.tail } }

theorem wrong_allocator : AssemblyItem.destroy objects 8 4 initial = (.error (.ownership .wrongAllocator), initial) := by rfl'
theorem wrong_block : (AssemblyItem.destroy objects 7 3 initial).1 = .error (.ownership .wrongType) := by rfl'
theorem wrong_extent : (AssemblyItem.destroy objects 7 4 (withObject { object with
    type := .record "src/libevmasm/assembly_item.zig::AssemblyItem" ⟨208, 16⟩ })).1 = .error (.memory .memoryValidity) := by rfl'
theorem wrong_identity : (AssemblyItem.destroy objects 7 4 (withObject { object with
    type := .record "OtherItem" ⟨224, 16⟩ })).1 = .error (.memory .memoryValidity) := by rfl'
theorem array_is_not_object : (AssemblyItem.destroy objects 7 4 (withObject { object with type := .array 56 word })).1 =
    .error (.memory .memoryValidity) := by rfl'
theorem stack_rejected : (AssemblyItem.destroy objects 7 4 (withObject { object with stack := true })).1 = .error (.memory .memoryValidity) := by rfl'
theorem readonly_rejected : (AssemblyItem.destroy objects 7 4 (withObject { object with writable := false })).1 = .error (.memory .memoryValidity) := by rfl'
theorem malformed_rejected : (AssemblyItem.destroy objects 7 4 (withObject { object with base := 0 })).1 = .error (.memory .malformed) := by rfl'
theorem dead_rejected : (AssemblyItem.destroy objects 7 4 insertion.2.memory).1 = .error (.ownership .unallocated) := by rfl'

def badOwner : Session Nat := { initial with heap := write initial.heap 4 (some ⟨8, .item itemValue⟩) }
def rejected := run bytes objects external 7 payloads ⟨4, incoming⟩ badOwner

theorem later_fault_retains_payload_release : rejected.1 = .error (.item (.inr (.ownership .wrongAllocator))) ∧
    rejected.2.memory.effects = 2 ∧ rejected.2.memory.heap 3 = none ∧ rejected.2.memory.memory.heap.lookup 3 = none ∧
    rejected.2.memory.heap 4 = some ⟨8, .item itemValue⟩ ∧ rejected.2.memory.heap 0 = some ⟨7, .arguments [0]⟩ ∧
    rejected.2.invalidated = false := ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem empty_argument_sentinel : (run bytes objects external 7 payloads ⟨4, ⟨4, []⟩⟩ initial).1 = .ok () ∧
    (run bytes objects external 7 payloads ⟨4, ⟨4, []⟩⟩ initial).2.memory.heap 4 = none ∧
    (run bytes objects external 7 payloads ⟨4, ⟨4, []⟩⟩ initial).2.memory.effects = 23 := ⟨by rfl', by rfl', by rfl'⟩

theorem absent_payload : (run bytes objects external 7 (fun _ => none) ⟨4, incoming⟩ initial).1 = .ok () ∧
    (run bytes objects external 7 (fun _ => none) ⟨4, incoming⟩ initial).2.memory.heap 3 = some ⟨7, .bytes 3⟩ ∧
    (run bytes objects external 7 (fun _ => none) ⟨4, incoming⟩ initial).2.memory.heap 4 = none := ⟨by rfl', by rfl', by rfl'⟩

open Compiler.Extraction.Interner
open ObservedTests (model caller callerHeap caller_valid)
open ObservedStorageTests (cell key binding denotation)
def storedCell := { cell with itemAddress := 4, argumentsAddress := 5 }
theorem exact_descriptors : storedCell.arguments = incoming.items ∧ storedCell.itemAddress = duplicate.item ∧
    storedCell.argumentSlice = duplicate.arguments ∧ initial.heap duplicate.item = some ⟨7, .item storedCell.item⟩ := ⟨rfl, rfl, rfl, rfl⟩

theorem insertion_words :
    Interner.Invariant model (Interner.InsertionExecution.project [caller] (fun _ => none) storedCell key insertion.1.2) ∧
    Interner.Stable callerHeap (Interner.InsertionExecution.project [caller] (fun _ => none) storedCell key insertion.1.2) := by
  have checked := insertion_verified model [caller] (fun _ => none) storedCell key true bytes objects external 7 payloads
    (fun _ _ => duplicate) rest ⟨initial, false⟩ (some .allocationFailure) caller_valid binding denotation complete_rollback.1
  exact ⟨checked.1.2.1, checked.1.2.2.1⟩

end Compiler.Extraction.ExpressionDeinit.Lifetime.Tests
