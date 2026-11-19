/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionDeinitInsertion
import Compiler.Extraction.ArgumentMemoryTests
import Compiler.Extraction.StorageExecutionTests

namespace Compiler.Extraction.ExpressionDeinit.Tests
open Compiler.Extraction.Storage Compiler.Extraction.Memory
open Compiler.Extraction.Memory.Arguments
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.ZigAir.Memory.WordArray

def initial : Session Nat := ⟨Arguments.Tests.logical, Arguments.Tests.bytes, 0⟩
def descriptor : Descriptor := ⟨42, Arguments.Tests.first⟩

def items (fail : Option Stage := none) : Items Nat Stage where
  deinit item before :=
    (if fail = some .itemValue ∨ item ≠ 42 then .error .itemValue else .ok (), before.effects * 10 + 2)
  destroy item before :=
    (if fail = some .itemAllocation ∨ item ≠ 42 then .error .itemAllocation else .ok (), before.effects * 10 + 3)

def external : External Nat where
  allocate _ before bytes effects :=
    let base := (before.memory.nextAddress / 4 + 1) * 4
    (if Compiler.ZigAir.Memory.addressLimit < base + bytes then none else some base, effects * 10 + 1)
  free _ before := before.effects * 10 + 4

theorem external_admitted : Admitted external := by
  intro site before values base effects valid _ response
  dsimp only [external] at response
  split at response
  · cases (Prod.mk.inj response).1
  · cases (Prod.mk.inj response).1
    rename_i bound
    refine ⟨by omega, by dsimp only; omega, by dsimp only; omega, ?_⟩
    intro entry present layout shaped
    simp only [Compiler.ZigAir.Memory.State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid
    have checked := valid.1.2 entry present
    simp only [shaped, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact Or.inr (by omega)

def observed (fail : Option Stage := none) := run (items fail) external 7 descriptor initial

theorem initial_valid : Valid initial := by
  refine ⟨Arguments.Tests.valid, Arguments.Tests.related, ?_⟩
  intro id block stored
  by_cases zero : id = 0
  · subst id; exact ⟨Arguments.Tests.firstCell, rfl, rfl⟩
  · by_cases one : id = 1
    · subst id; exact ⟨Arguments.Tests.secondCell, rfl, rfl⟩
    · simp [initial, Arguments.Tests.logical, zero, one] at stored

theorem complete_contract (fail : Option Stage) : Post descriptor initial (observed fail) :=
  run_verified (items fail) external 7 descriptor initial initial_valid Arguments.Tests.first_live

theorem source_order : observed = (.ok (), ⟨⟨Arguments.Tests.remaining, Arguments.Tests.after, 234⟩, true⟩) := by rfl'
theorem argument_dead : (observed).2.memory.heap 0 = none ∧
    (observed).2.memory.memory.heap.lookup 0 = none := ⟨by rfl', by rfl'⟩
theorem borrowed_cells_preserved : (observed).2.memory.memory.heap.lookup 1 = some Arguments.Tests.secondCell ∧
    (observed).2.memory.memory.heap.lookup 2 = some Arguments.Tests.scratchCell := ⟨by rfl', by rfl'⟩
theorem allocation_history : (observed).2.memory.memory.nextId = 3 ∧
    (observed).2.memory.memory.nextAddress = 56 := ⟨by rfl', by rfl'⟩

theorem item_value_fault : (observed (some .itemValue)).1 = .error (.item .itemValue) ∧
    (observed (some .itemValue)).2.memory.effects = 2 ∧
    (observed (some .itemValue)).2.memory.memory = initial.memory ∧
    (observed (some .itemValue)).2.invalidated = false := ⟨by rfl', by rfl', by rfl', by rfl'⟩
theorem item_allocation_fault : (observed (some .itemAllocation)).1 = .error (.item .itemAllocation) ∧
    (observed (some .itemAllocation)).2.memory.effects = 23 ∧
    (observed (some .itemAllocation)).2.memory.memory = initial.memory ∧
    (observed (some .itemAllocation)).2.invalidated = false := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem wrong_allocator :
    (run (items) external 8 descriptor initial).1 = .error (.arguments (.release (.ownership .wrongAllocator))) ∧
    (run (items) external 8 descriptor initial).2.memory.effects = 23 ∧
    (run (items) external 8 descriptor initial).2.invalidated = false := ⟨by rfl', by rfl', by rfl'⟩
theorem wrong_extent :
    (run (items) external 7 ⟨42, ⟨0, [3, 1]⟩⟩ initial).1 = .error (.arguments (.release (.memory .memoryValidity))) := by rfl'
theorem dead_descriptor : execute (items).operations external 7 descriptor expressionDeinitCode (observed).2 =
    (.error .invalidDescriptor, (observed).2) := by rfl'
theorem empty_arguments : run (items) external 999 ⟨42, ⟨999, []⟩⟩ initial =
    (.ok (), ⟨{ initial with effects := 23 }, true⟩) := by rfl'

/-- The argument duplicate is real typed allocation/copy. Item construction,
append and publication outcomes are framed fixtures, not native implementations. -/
def incoming : ArgumentSlice := ⟨0, [0]⟩
def insertionInitial : Session Nat := { initial with
  heap := write initial.heap 0 (some ⟨7, .arguments incoming.items⟩)
  memory := { initial.memory with heap := (0, ⟨16, .array 1 word, [(0, number 0)], true, false⟩) :: initial.memory.heap.tail } }

theorem insertion_initial_valid : Valid insertionInitial := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro allocator id values _ stored
    by_cases zero : id = 0
    · subst id
      have same : 7 = allocator ∧ [0] = values := by simpa [insertionInitial, write, incoming] using stored
      rcases same with ⟨rfl, rfl⟩
      refine ⟨⟨_, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
      intro index inside
      have only : index = 0 := by simpa using inside
      subst index; rfl'
    · by_cases one : id = 1
      · subst id
        have same : 11 = allocator ∧ [99] = values := by
          simpa [insertionInitial, initial, write, Arguments.Tests.logical] using stored
        rcases same with ⟨rfl, rfl⟩
        refine ⟨⟨_, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
        intro index inside
        have only : index = 0 := by simpa using inside
        subst index; rfl'
      · simp [insertionInitial, initial, write, Arguments.Tests.logical, zero, one] at stored
  · intro id block stored
    by_cases zero : id = 0
    · subst id; exact ⟨_, rfl, rfl⟩
    · by_cases one : id = 1
      · subst id; exact ⟨_, rfl, rfl⟩
      · simp [insertionInitial, initial, write, Arguments.Tests.logical, zero, one] at stored

def inputHandle : Handle := ⟨view incoming, incoming.items, none⟩
def taken := takeOwned Cache.normalizationOwnershipCode external 7 inputHandle insertionInitial

def rest : Storage.Operations (State Nat) (Fault Stage) where
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

def duplicate : Descriptor := ⟨42, ⟨3, incoming.items⟩⟩

theorem taken_result : taken.1 = .ok (duplicate.arguments, inputHandle) := by rfl'

theorem taken_valid : Valid taken.2 ∧ SliceValid 7 taken.2.heap duplicate.arguments := by
  have contents : Represents insertionInitial.memory (view incoming) incoming.items :=
    (insertion_initial_valid.related 7 0 [0] (by decide) (by rfl')).2
  have ready : Ready 7 (view incoming) incoming.items inputHandle insertionInitial :=
    ⟨insertion_initial_valid, contents, contents, (by intro _ impossible; cases impossible),
      (by intro _ _ impossible; cases impossible)⟩
  obtain ⟨result, after, executed, post⟩ := take_refines external 7 (view incoming) incoming.items inputHandle
    insertionInitial ready external_admitted
  have same : result = .ok (duplicate.arguments, inputHandle) := (congrArg Prod.fst executed).symm.trans taken_result
  rw [same] at post
  have memory := congrArg Prod.snd executed
  exact memory.symm ▸ ⟨post.ready.valid, post.live⟩

def rollbackState : State Nat := ⟨{ taken.2 with effects := 15678 }, false⟩

theorem rollback_contract (ownership : Storage.State) :
    let executed := Storage.Release.lastValue.execute (insertionOperations (items) external 7 (fun _ _ => duplicate) rest)
      ownership rollbackState
    Post duplicate rollbackState.memory (executed.1.1, executed.2) :=
  last_value_preserved (items) external 7 (fun _ _ => duplicate) rest ownership rollbackState rfl
    ⟨taken_valid.1.memory, taken_valid.1.related, taken_valid.1.injected⟩ taken_valid.2
def callbacks (fail : Option Stage := none) := insertionOperations (items fail) external 7 (fun _ _ => duplicate) rest
def insertion (fail : Option Stage := none) :=
  insertProgram.execute ⟨true, true, fun _ => false⟩ (callbacks fail) {} ⟨insertionInitial, false⟩

theorem insertion_rollback : (insertion).1.1 = .ok (some .allocationFailure) ∧
    (insertion).2.memory.effects = 1567823494 ∧
    (insertion).2.memory.heap 0 = none ∧ (insertion).2.memory.heap 3 = none ∧
    (insertion).2.memory.memory.heap.lookup 0 = none ∧ (insertion).2.memory.memory.heap.lookup 3 = none ∧
    (insertion).1.2.appended = false ∧ (insertion).2.invalidated = true :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem insertion_fault_stops : (insertion (some .itemAllocation)).1.1 = .error (.item .itemAllocation) ∧
    (insertion (some .itemAllocation)).2.memory.effects = 1567823 ∧
    (insertion (some .itemAllocation)).1.2.appended = true ∧
    (insertion (some .itemAllocation)).2.memory.heap 0 = some ⟨7, .arguments [0]⟩ ∧
    (insertion (some .itemAllocation)).2.memory.heap 3 = some ⟨7, .arguments [0]⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

open Compiler.Extraction.Interner
open ObservedTests (model caller callerHeap caller_valid)
open ObservedStorageTests (cell key binding denotation)

def storedCell := { cell with itemAddress := 42, argumentsAddress := 3 }

theorem exact_descriptors : storedCell.arguments = incoming.items ∧ storedCell.itemAddress = duplicate.item ∧
    storedCell.argumentSlice = duplicate.arguments := ⟨rfl, rfl, rfl⟩

theorem insertion_words :
    Interner.Invariant model (Interner.InsertionExecution.project [caller] (fun _ => none) storedCell key (insertion).1.2) ∧
    Interner.Stable callerHeap (Interner.InsertionExecution.project [caller] (fun _ => none) storedCell key (insertion).1.2) := by
  have checked := insertion_verified model [caller] (fun _ => none) storedCell key true (items) external 7
    (fun _ _ => duplicate) rest ⟨insertionInitial, false⟩ (some .allocationFailure) caller_valid binding denotation insertion_rollback.1
  exact ⟨checked.1.2.1, checked.1.2.2.1⟩

end Compiler.Extraction.ExpressionDeinit.Tests
