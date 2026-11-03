/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerLocalArgumentsProofs
import Compiler.Extraction.InternerConstructorFrameTests

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments.Tests
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open Normalization.Tests

def source : View := ⟨0, 1, 2⟩
def target : View := ⟨3, 0, 2⟩
def copied := (copy source Semantic.Tests.caller).2
def overwritten (selected : Nat) := (zigLocal source selected 99 true Semantic.Tests.caller).2

theorem source_represented : Represents original.memory source [1, 2] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  change index < 2 at inside
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with zero | one
  · subst index; rfl'
  · subst index; rfl'

theorem copied_offset_words : (copy source Semantic.Tests.caller).1 = .ok target ∧
    Compiler.ZigAir.Memory.load copied.memory.memory (target.pointer 0) = .ok (number 1) ∧
    Compiler.ZigAir.Memory.load copied.memory.memory (target.pointer 1) = .ok (number 2) ∧
    copied.memory.memory.nextId = 4 := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem good_and_writable_are_derived : Good target [1, 2] copied ∧ Writable copied.memory.memory target := by
  obtain ⟨after, ran, good, _, _, _, _, _, writable, _⟩ :=
    copy_verified source 1 2 Semantic.Tests.caller _ before.memory original_valid source_represented actual_caller_allocation
  have same : copied = after := congrArg Prod.snd ran
  exact same.symm ▸ ⟨good, writable⟩

theorem original_borrow_preserved : copied.graph = Semantic.Tests.caller.graph ∧ copied.memory.heap = original.heap ∧
    copied.memory.effects = 5 ∧ copied.memory.memory.heap.lookup 0 = original.memory.heap.lookup 0 ∧
    copied.memory.memory.heap.lookup 2 = original.memory.heap.lookup 2 := ⟨rfl, rfl, rfl, by rfl', by rfl'⟩

theorem false_flag_skips_overwrite : zigLocal source 1 99 false Semantic.Tests.caller = copy source Semantic.Tests.caller := by rfl'

theorem overwrite_first_slot : Compiler.ZigAir.Memory.load (overwritten 0).memory.memory (target.pointer 0) = .ok (number 99) ∧
    Compiler.ZigAir.Memory.load (overwritten 0).memory.memory (target.pointer 1) = .ok (number 2) := ⟨by rfl', by rfl'⟩

theorem overwrite_second_slot : Compiler.ZigAir.Memory.load (overwritten 1).memory.memory (target.pointer 0) = .ok (number 1) ∧
    Compiler.ZigAir.Memory.load (overwritten 1).memory.memory (target.pointer 1) = .ok (number 99) := ⟨by rfl', by rfl'⟩

theorem optional_store_preserves_borrow_and_identity :
    (overwritten 1).memory.memory.heap.lookup 0 = original.memory.heap.lookup 0 ∧
    (overwritten 1).memory.memory.nextId = 4 ∧ (overwritten 1).memory.effects = 5 := ⟨by rfl', by rfl', rfl⟩

def short : World Nat := { Semantic.Tests.caller with memory := { original with memory :=
  { before.memory with heap := (3, { scratchCell with type := .array 1 word }) :: original.memory.heap } } }

/-- Malformed aggregate geometry is a rejection, not a native successful
initializer. Unlike two separate anonymous stores, this phase has no prefix. -/
theorem aggregate_rejection_has_no_prefix :
    (initPair target 99 1 short).1 = .error (.memory (.preparation (.memory .memoryValidity))) ∧
    (initPair target 99 1 short).2 = short ∧
    Compiler.ZigAir.Memory.load (initPair target 99 1 short).2.memory.memory (target.pointer 0) = .error .uninitialized :=
  ⟨by rfl', by rfl', by rfl'⟩

def secondLoadRejected := zigLocal ⟨0, 2, 2⟩ 0 99 true Semantic.Tests.caller
theorem rejected_second_load_keeps_allocation :
    secondLoadRejected.1 = .error (.memory (.preparation (.memory .memoryValidity))) ∧
    secondLoadRejected.2.memory.memory.nextId = 4 ∧ secondLoadRejected.2.memory.memory.heap.lookup 3 = some scratchCell ∧
    Compiler.ZigAir.Memory.load secondLoadRejected.2.memory.memory (target.pointer 0) = .error .uninitialized ∧
    secondLoadRejected.2.graph = Semantic.Tests.caller.graph := ⟨by rfl', by rfl', by rfl', by rfl', rfl⟩

theorem missing_source_keeps_allocation :
    (copy ⟨99, 0, 2⟩ Semantic.Tests.caller).1 = .error (.memory (.preparation (.memory .unallocated))) ∧
    (copy ⟨99, 0, 2⟩ Semantic.Tests.caller).2.memory.memory.nextId = 4 := ⟨by rfl', by rfl'⟩

theorem length_guard_precedes_allocation : copy ⟨0, 0, 3⟩ Semantic.Tests.caller =
    (.error (.memory (.preparation (.memory .sourceBounds))), Semantic.Tests.caller) := by rfl'

theorem invalid_overwrite_keeps_initialized_copy :
    (zigLocal source 2 99 true Semantic.Tests.caller).1 = .error (.memory (.preparation (.memory .memoryValidity))) ∧
    (zigLocal source 2 99 true Semantic.Tests.caller).2 = copied := ⟨by rfl', by rfl'⟩

def exhausted : World Nat := { Semantic.Tests.caller with memory := { original with memory :=
  { original.memory with nextAddress := Compiler.ZigAir.Memory.addressLimit } } }
theorem stack_limit_precedes_load : copy ⟨99, 0, 2⟩ exhausted =
    (.error (.memory (.preparation (.memory .outOfMemory))), exhausted) := by rfl'

def parentStack := (TemporaryArguments.prepare 3 1 Semantic.Tests.caller).2
def nestedCopy := (zigLocal ⟨3, 0, 2⟩ 1 99 true parentStack).2
theorem older_stack_borrow_survives_copy :
    nestedCopy.memory.memory.heap.lookup 3 = parentStack.memory.memory.heap.lookup 3 ∧
    Compiler.ZigAir.Memory.load nestedCopy.memory.memory ((⟨4, 0, 2⟩ : View).pointer 0) = .ok (number 3) ∧
    Compiler.ZigAir.Memory.load nestedCopy.memory.memory ((⟨4, 0, 2⟩ : View).pointer 1) = .ok (number 99) ∧
    nestedCopy.memory.memory.nextId = 5 := ⟨by rfl', by rfl', by rfl', by rfl'⟩

def returned : World Nat := { copied with memory := { copied.memory with
  memory := Compiler.ZigAir.Memory.cleanup 3 copied.memory.memory } }
theorem stale_local_cannot_alias_new_lifetime :
    (copy target returned).1 = .error (.memory (.preparation (.memory .unallocated))) ∧
    (copy target returned).2.memory.memory.nextId = 5 ∧
    (copy target returned).2.memory.memory.heap.lookup 3 = none := ⟨by rfl', by rfl', by rfl'⟩

def semanticCaller : World Nat := { Semantic.Tests.caller with graph := { Semantic.Tests.wordGraph with
  read := fun id => if id = 99 then some 0 else Semantic.Tests.wordGraph.read id } }
def run (external : External Nat := success) := invoke external 160 7
  (Semantic.Tests.callbacks Semantic.Tests.meaning 99) Caller.Tests.queries (Folding.Op.opcode .and)
  source 1 2 3 0 true semanticCaller

theorem ordinary_success_unwinds_local : run.1 = .ok 99 ∧ run.2.memory.memory.heap = original.memory.heap ∧
    run.2.memory.memory.nextId > 4 := ⟨by rfl', by rfl', by decide +kernel⟩

theorem ordinary_oom_unwinds_local : (run (external (fun _ => true))).1 = .error (.language .outOfMemory) ∧
    (run (external (fun _ => true))).2.memory.memory.heap = original.memory.heap := ⟨by rfl', by rfl'⟩

theorem nonvacuous_constructor_contract : run.1 = .ok 99 ∧ Valid run.2.memory ∧
    Semantic.Ensures Semantic.Tests.meaning semanticCaller.graph run.1 run.2.graph
      (fun id graph => graph.read id = some 0) := by
  have checked := invoke_verified success 160 7 (Semantic.Tests.callbacks Semantic.Tests.meaning 99)
    Caller.Tests.queries (Folding.Op.opcode .and) source 1 2 3 0 true semanticCaller _ before.memory
    Compiler.Extraction.Recursive.Tests.base 0 original_valid source_represented (by decide) actual_caller_allocation
    (external_admitted _) (Semantic.Tests.ownership _ _) (Semantic.Tests.semantics _ _)
    ⟨(by intro _ _ impossible; cases impossible), trivial⟩ (by rfl')
  exact ⟨by rfl', checked (by rfl')⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.LocalArguments.Tests
