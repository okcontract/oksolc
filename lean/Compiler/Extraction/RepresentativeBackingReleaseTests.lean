/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingReleaseFrame
import Compiler.Extraction.RepresentativeArrayTests

namespace Compiler.Extraction.RepresentativeArray.Backing.Release.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

abbrev Effects := List (Nat × Nat × Nat × Nat)
def external : External Effects := fun allocator base bytes alignment effects => effects ++ [(allocator, base, bytes, alignment)]
def registry : Registry := fun id => if id = 2 then some ⟨7, .representatives []⟩ else none
def backing : Allocation := ⟨512, Backing.type 5, RepresentativeArray.Tests.descriptorCells, true, false⟩
def headerCells : Cells := (RepresentativeArray.Tests.items).leaves 0 ++ (Value.scalar (.int false 64 5)).leaves 16
def memory (storage : Allocation := backing) (header : Cells := headerCells) : State :=
  ⟨[(3, ⟨704, allocationType, header, true, false⟩), (2, storage),
    (1, Expression.Tests.argumentsAllocation), (0, Expression.Tests.itemAllocation)], 4, 728⟩
def before : Session Effects := ⟨registry, memory, [(9, 16, 8, 8)]⟩
def after : Session Effects := ⟨Compiler.Extraction.Memory.write registry 2 none, erase memory 2,
  [(9, 16, 8, 8), (7, 512, 160, 8)]⟩

theorem initial_valid : Valid before := by
  refine ⟨by decide, ?_, ?_⟩
  · intro allocator id values nonempty stored
    by_cases same : id = 2 <;> simp [before, registry, same] at stored
  · intro id block stored
    by_cases same : id = 2
    · subst id; exact ⟨backing, rfl, rfl⟩
    · simp [before, registry, same] at stored

theorem initial_owned : Owned 7 ⟨2, 0⟩ 5 before :=
  ⟨rfl, ⟨[], rfl⟩, backing, rfl, rfl, rfl, rfl⟩

theorem actual_release : run external 7 ⟨2, 0⟩ 5 before = (.ok (), after) := rfl

theorem without_final_premises : ∃ cell finalState, before.memory.heap.lookup 2 = some cell ∧
    run external 7 ⟨2, 0⟩ 5 before = (.ok (), finalState) ∧ Post 2 before finalState ∧
    finalState.effects = external 7 cell.base 160 8 before.effects ∧
    0 < cell.base ∧ cell.base % 8 = 0 ∧ cell.base + 160 ≤ addressLimit :=
  verified external 7 ⟨2, 0⟩ 5 before initial_valid initial_owned (by decide)

theorem checked_post : Post 2 before after := by
  obtain ⟨cell, finalState, _, execution, post, _⟩ := without_final_premises
  rw [actual_release] at execution
  rw [← (Prod.mk.inj execution).2] at post
  exact post

theorem header_uses_capacity : fromHeader external 7 ⟨3, 0⟩ before = (.ok (), after) := rfl

def missingLength : Session Effects := { before with memory := memory backing (headerCells.filter (fun entry => entry.1 != 8)) }
theorem length_is_not_read : (fromHeader external 7 ⟨3, 0⟩ missingLength).1 = .ok () ∧
    (fromHeader external 7 ⟨3, 0⟩ missingLength).2.effects = after.effects := by decide

def noDescriptors : Session Effects := { before with memory := memory { backing with cells := [] } }
theorem uninitialized_capacity_can_be_freed : (run external 7 ⟨2, 0⟩ 5 noDescriptors).1 = .ok () ∧
    (run external 7 ⟨2, 0⟩ 5 noDescriptors).2.effects = after.effects := by decide

theorem initialized_prefix_is_not_extent : run external 7 ⟨2, 0⟩ 2 before = (.error (.memory .memoryValidity), before) := rfl
theorem oversized_extent_rejects : run external 7 ⟨2, 0⟩ 6 before = (.error (.memory .memoryValidity), before) := rfl
theorem interior_pointer_rejects : run external 7 ⟨2, 32⟩ 4 before = (.error (.memory .memoryValidity), before) := rfl
theorem wrong_allocator_rejects : run external 8 ⟨2, 0⟩ 5 before = (.error (.ownership .wrongAllocator), before) := rfl
theorem stale_registry_rejects : run external 7 ⟨2, 0⟩ 5 after = (.error (.ownership .unallocated), after) := rfl

def wrongBlock : Session Effects := { before with heap := fun id => if id = 2 then some ⟨7, .bytes 160⟩ else none }
theorem wrong_registry_type_rejects : run external 7 ⟨2, 0⟩ 5 wrongBlock = (.error (.ownership .wrongType), wrongBlock) := rfl
def readonly : Session Effects := { before with memory := memory { backing with writable := false } }
def stack : Session Effects := { before with memory := memory { backing with stack := true } }
theorem readonly_rejects : run external 7 ⟨2, 0⟩ 5 readonly = (.error (.memory .memoryValidity), readonly) := rfl
theorem stack_rejects : run external 7 ⟨2, 0⟩ 5 stack = (.error (.memory .memoryValidity), stack) := rfl
def wrongType : Session Effects := { before with memory := memory { backing with type := .array 40 WordArray.word, cells := [] } }
theorem same_bytes_wrong_type_rejects : run external 7 ⟨2, 0⟩ 5 wrongType = (.error (.memory .memoryValidity), wrongType) := rfl
def missing : Session Effects := { before with memory := erase memory 2 }
theorem missing_memory_rejects : run external 7 ⟨2, 0⟩ 5 missing = (.error (.memory .unallocated), missing) := rfl
def invalid : Session Effects := { before with memory := { memory with nextId := 0 } }
theorem corrupt_state_rejects : run external 7 ⟨2, 0⟩ 5 invalid = (.error (.memory .malformed), invalid) := rfl
theorem empty_ignores_sentinel : run external 8 ⟨999, 37⟩ 0 invalid = (.ok (), invalid) := rfl

def parent : WordArray.View := ⟨1, 1, 2⟩
theorem parent_contents : WordArray.Represents before.memory parent [99, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have choice : index = 0 ∨ index = 1 := by simp at inside; omega
  rcases choice with rfl | rfl <;> rfl

theorem parent_survives_every_outcome (allocator capacity : Nat) (data : Address) :
    WordArray.Represents (run external allocator data capacity before).2.memory parent [99, 1] :=
  (parent_borrow external allocator data capacity before parent [99, 1] 4 Expression.Tests.argumentsAllocation
    rfl rfl parent_contents).2.1

theorem aliases_die_history_survives :
    after.memory.nextId = 4 ∧ after.memory.nextAddress = 728 ∧
    load after.memory (.pointer (.pointer false false Expression.idType) ⟨2, 56⟩) = .error .unallocated ∧
    after.memory.heap.lookup 0 = before.memory.heap.lookup 0 ∧ after.memory.heap.lookup 1 = before.memory.heap.lookup 1 := by decide

def borrowedParent (writable stack : Bool) : Session Effects := { before with memory :=
  { memory with heap := [(3, ⟨704, allocationType, headerCells, true, false⟩), (2, backing),
    (1, { Expression.Tests.argumentsAllocation with writable := writable, stack := stack }), (0, Expression.Tests.itemAllocation)] } }

theorem readonly_stack_parent_survives (writable stack : Bool) :
    (run external 7 ⟨2, 0⟩ 5 (borrowedParent writable stack)).1 = .ok () ∧
    (run external 7 ⟨2, 0⟩ 5 (borrowedParent writable stack)).2.memory.heap.lookup 1 =
      some { Expression.Tests.argumentsAllocation with writable := writable, stack := stack } := by
  cases writable <;> cases stack <;> decide

/-- A separate registry payload is framed by a real successful release. This
does not assert native descriptor-to-payload correspondence for this fixture. -/
def graphCell : Compiler.Extraction.Storage.Cell :=
  { item := ⟨1, some 1, 0⟩, otherValue := 0, itemAddress := 0,
    arguments := [777, 99, 1, 5], argumentsAddress := 1 }
def graphBefore : Session Effects :=
  { before with heap := (Compiler.Extraction.Memory.write
      (Compiler.Extraction.Memory.write registry 0 (some ⟨7, .item graphCell.item⟩))
      1 (some ⟨7, .arguments graphCell.arguments⟩)) }
theorem graph_payload_survives : (run external 7 ⟨2, 0⟩ 5 graphBefore).1 = .ok () ∧
    Compiler.Extraction.Memory.GraphResident 7 (run external 7 ⟨2, 0⟩ 5 graphBefore).2.heap [graphCell] := by
  refine ⟨rfl, run_graph_frame external 7 ⟨2, 0⟩ 5 graphBefore [graphCell] ?_⟩
  simp [Compiler.Extraction.Memory.GraphResident, Compiler.Extraction.Memory.Resident,
    Compiler.Extraction.Memory.SliceValid, Compiler.Extraction.Storage.Cell.argumentSlice,
    graphBefore, graphCell, Compiler.Extraction.Memory.write]

end Compiler.Extraction.RepresentativeArray.Backing.Release.Tests
