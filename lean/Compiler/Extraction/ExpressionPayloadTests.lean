/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionPayload
import Compiler.Extraction.AssemblyItemDeinitTests

namespace Compiler.Extraction.ExpressionDeinit.Payload.Tests
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.ZigAir.Memory.WordArray

/-- One registry: incoming unary arguments, a borrowed argument and scratch,
then an owned byte payload. Typed duplication will allocate lifetime 4. -/
def initial : Session Nat :=
  ⟨write ExpressionDeinit.Tests.insertionInitial.heap 3 (some ⟨7, .bytes 3⟩),
    ⟨(3, AssemblyItemDeinit.Tests.cell) :: ExpressionDeinit.Tests.insertionInitial.memory.heap, 4, 67⟩, 0⟩
def incoming := ExpressionDeinit.Tests.incoming
def inputHandle := ExpressionDeinit.Tests.inputHandle
def external := ExpressionDeinit.Tests.external
def payloads : Nat → Option AssemblyItemDeinit.Bytes := fun id =>
  if id = 42 then some AssemblyItemDeinit.Tests.payload else none

def release : AssemblyItemDeinit.Release Nat := fun _ before => before.effects * 10 + 2

/-- Allocation destruction is still framed. This fixture observes the registry
left by payload cleanup, so a dropped memory update fails even before free. -/
def destroy (fail : Bool := false) : Destroy Nat Bool := fun id before =>
  (if fail || id != 42 || before.memory.heap.lookup 3 != none then .error true else .ok (), before.effects * 10 + 3)

theorem initial_valid : Valid initial := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro allocator id values nonempty stored
    by_cases same : id = 3
    · subst id; simp [initial, write] at stored
    · obtain ⟨⟨old, found, typed, writable, stack⟩, represented⟩ := ExpressionDeinit.Tests.insertion_initial_valid.related
        allocator id values nonempty (by simpa [initial, write, same] using stored)
      have framed : initial.memory.heap.lookup id = ExpressionDeinit.Tests.insertionInitial.memory.heap.lookup id := by
        simp [initial, Compiler.ZigAir.Memory.Heap.lookup_cons, Ne.symm same]
      exact ⟨⟨old, framed.trans found, typed, writable, stack⟩, represented_frame _ _ represented framed⟩
  · intro id allocation stored
    by_cases same : id = 3
    · subst id; exact ⟨AssemblyItemDeinit.Tests.cell, rfl, rfl⟩
    · obtain ⟨old, found, _persistent⟩ := ExpressionDeinit.Tests.insertion_initial_valid.injected id allocation
        (by simpa [initial, write, same] using stored)
      exact ⟨old, by simpa [initial, Compiler.ZigAir.Memory.Heap.lookup_cons, Ne.symm same] using found, _persistent⟩

def taken := takeOwned Cache.normalizationOwnershipCode external 7 inputHandle initial
def duplicate : Descriptor := ⟨42, ⟨4, incoming.items⟩⟩

theorem taken_result : taken.1 = .ok (duplicate.arguments, inputHandle) := by rfl'

theorem taken_valid : Valid taken.2 ∧ SliceValid 7 taken.2.heap duplicate.arguments := by
  have contents : Represents initial.memory (view incoming) incoming.items :=
    (initial_valid.related 7 0 [0] (by decide) (by rfl')).2
  have ready : Ready 7 (view incoming) incoming.items inputHandle initial :=
    ⟨initial_valid, contents, contents, (by intro _ impossible; cases impossible),
      (by intro _ _ impossible; cases impossible)⟩
  obtain ⟨result, after, executed, post⟩ := take_refines external 7 (view incoming) incoming.items inputHandle
    initial ready ExpressionDeinit.Tests.external_admitted
  have same : result = .ok (duplicate.arguments, inputHandle) := (congrArg Prod.fst executed).symm.trans taken_result
  rw [same] at post
  have memory := congrArg Prod.snd executed
  exact memory.symm ▸ ⟨post.ready.valid, post.live⟩

theorem taken_payload : ∀ slice, payloads duplicate.item = some slice → AssemblyItemDeinit.Owned 7 slice taken.2 := by
  intro slice selected
  have same : AssemblyItemDeinit.Tests.payload = slice := by simpa [payloads, duplicate] using selected
  subst slice
  exact Or.inr ⟨by rfl', AssemblyItemDeinit.Tests.cell, by rfl', rfl, rfl, rfl, rfl⟩

def rest : Storage.Operations (State Nat) (Fault (ItemFault Bool)) where
  attempt site _ before := match site with
    | .arguments =>
      let (result, memory) := takeOwned Cache.normalizationOwnershipCode external 7 inputHandle before.memory
      let after := { before with memory }
      match result with
      | .error .outOfMemory => (.ok false, after)
      | .error fault => (.error (.arguments fault), after)
      | .ok _ => (.ok true, after)
    | .item => (.ok true, { before with memory := { before.memory with effects := before.memory.effects * 10 + 5 } })
    | .clone => (.ok true, { before with memory := { before.memory with effects := before.memory.effects * 10 + 6 } })
    | .append => (.ok true, { before with memory := { before.memory with effects := before.memory.effects * 10 + 7 } })
    | .publish => (.ok false, { before with memory := { before.memory with effects := before.memory.effects * 10 + 8 } })
  release action _ before := match action with
    | .normalized =>
      let (result, memory) := free external 7 incoming before.memory
      (result.mapError Fault.arguments, { before with memory })
    | .pop => (.ok (), { before with memory := { before.memory with effects := before.memory.effects * 10 + 9 } })
    | _ => (.error .invalidDescriptor, before)

def callbacks (fail : Bool := false) := insertionOperations release external 7 payloads (destroy fail) (fun _ _ => duplicate) rest
def insertion (fail : Bool := false) :=
  insertProgram.execute ⟨true, true, fun _ => false⟩ (callbacks fail) {} ⟨initial, false⟩
def rollbackState : State Nat := ⟨{ taken.2 with effects := 15678 }, false⟩

theorem rollback_contract (ownership : Storage.State) (fail : Bool) :
    let executed := Storage.Release.lastValue.execute (callbacks fail) ownership rollbackState
    Post 7 (payloads duplicate.item) duplicate rollbackState.memory (executed.1.1, executed.2) :=
  last_value_preserved release external 7 payloads (destroy fail) (fun _ _ => duplicate) rest ownership rollbackState rfl
    ⟨taken_valid.1.memory, taken_valid.1.related, taken_valid.1.injected⟩ taken_valid.2 taken_payload

theorem complete_rollback : (insertion).1.1 = .ok (some .allocationFailure) ∧
    (insertion).2.memory.effects = 1567823494 ∧
    (insertion).2.memory.heap 0 = none ∧ (insertion).2.memory.heap 3 = none ∧ (insertion).2.memory.heap 4 = none ∧
    (insertion).2.memory.memory.heap.lookup 0 = none ∧ (insertion).2.memory.memory.heap.lookup 3 = none ∧
    (insertion).2.memory.memory.heap.lookup 4 = none ∧
    (insertion).1.2.appended = false ∧ (insertion).2.invalidated = true :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem allocation_fault_retains_payload_release : (insertion true).1.1 = .error (.item (.inr true)) ∧
    (insertion true).2.memory.effects = 1567823 ∧
    (insertion true).2.memory.heap 3 = none ∧ (insertion true).2.memory.memory.heap.lookup 3 = none ∧
    (insertion true).1.2.appended = true ∧ (insertion true).2.invalidated = false ∧
    (insertion true).2.memory.heap 0 = some ⟨7, .arguments [0]⟩ ∧
    (insertion true).2.memory.heap 4 = some ⟨7, .arguments [0]⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem payload_fault_stops : (run release external 8 payloads (destroy) duplicate taken.2).1 =
    .error (.item (.inl (.release (.ownership .wrongAllocator)))) ∧
    (run release external 8 payloads (destroy) duplicate taken.2).2.memory.effects = taken.2.effects ∧
    (run release external 8 payloads (destroy) duplicate taken.2).2.memory.memory = taken.2.memory ∧
    (run release external 8 payloads (destroy) duplicate taken.2).2.invalidated = false :=
  ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem empty_argument_sentinel : (run release external 7 payloads (destroy) ⟨42, ⟨3, []⟩⟩ initial).1 = .ok () ∧
    (run release external 7 payloads (destroy) ⟨42, ⟨3, []⟩⟩ initial).2.memory.heap 3 = none ∧
    (run release external 7 payloads (destroy) ⟨42, ⟨3, []⟩⟩ initial).2.memory.effects = 23 :=
  ⟨by rfl', by rfl', by rfl'⟩

theorem borrowed_cells (fail : Bool) : (insertion fail).2.memory.memory.heap.lookup 1 = some Arguments.Tests.secondCell ∧
    (insertion fail).2.memory.memory.heap.lookup 2 = some Arguments.Tests.scratchCell := by
  cases fail <;> exact ⟨by rfl', by rfl'⟩

theorem allocation_history (fail : Bool) : (insertion fail).2.memory.memory.nextId = 5 ∧
    (insertion fail).2.memory.memory.nextAddress = 72 := by
  cases fail <;> exact ⟨by rfl', by rfl'⟩

open Compiler.Extraction.Interner
open ObservedTests (model caller callerHeap caller_valid)
open ObservedStorageTests (cell key binding denotation)
def storedCell := { cell with itemAddress := 42, argumentsAddress := 4 }

theorem exact_descriptors : storedCell.arguments = incoming.items ∧ storedCell.itemAddress = duplicate.item ∧
    storedCell.argumentSlice = duplicate.arguments := ⟨rfl, rfl, rfl⟩

theorem insertion_words :
    Interner.Invariant model (Interner.InsertionExecution.project [caller] (fun _ => none) storedCell key (insertion).1.2) ∧
    Interner.Stable callerHeap (Interner.InsertionExecution.project [caller] (fun _ => none) storedCell key (insertion).1.2) := by
  have checked := insertion_verified model [caller] (fun _ => none) storedCell key true release external 7 payloads (destroy)
    (fun _ _ => duplicate) rest ⟨initial, false⟩ (some .allocationFailure) caller_valid binding denotation complete_rollback.1
  exact ⟨checked.1.2.1, checked.1.2.2.1⟩

end Compiler.Extraction.ExpressionDeinit.Payload.Tests
