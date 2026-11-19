/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemDeinitProofs
import Compiler.Extraction.ExpressionDeinitTests

namespace Compiler.Extraction.AssemblyItemDeinit.Tests
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Bytes may be uninitialized at release. Existing argument cells share the
same logical and typed registries, including an unrelated scratch allocation. -/
def payload : Bytes := ⟨3, 3, 0⟩
def cell : Compiler.ZigAir.Memory.Allocation := ⟨64, .array 3 byte, [], true, false⟩
def initial : Session Nat := ⟨write Arguments.Tests.logical 3 (some ⟨7, .bytes 3⟩),
  ⟨(3, cell) :: Arguments.Tests.bytes.heap, 4, 67⟩, 1⟩

def external : Release Nat := fun slice before =>
  if before.memory.heap.lookup slice.address = some cell then before.effects * 10 + slice.length else 999

def observed := run external 7 (some payload) initial

theorem initial_valid : Valid initial := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro allocator id values nonempty stored
    by_cases same : id = 3
    · subst id; simp [initial, write] at stored
    · obtain ⟨⟨old, found, typed, writable, stack⟩, represented⟩ := Arguments.Tests.related allocator id values nonempty
        (by simpa [initial, write, same] using stored)
      have framed : initial.memory.heap.lookup id = Arguments.Tests.bytes.heap.lookup id := by
        simp [initial, Compiler.ZigAir.Memory.Heap.lookup_cons, Ne.symm same]
      exact ⟨⟨old, framed.trans found, typed, writable, stack⟩,
        represented_frame _ _ represented framed⟩
  · intro id allocation stored
    by_cases same : id = 3
    · subst id; exact ⟨cell, rfl, rfl⟩
    · obtain ⟨old, found, _persistent⟩ := ExpressionDeinit.Tests.initial_valid.injected id allocation
        (by simpa [initial, write, same, ExpressionDeinit.Tests.initial] using stored)
      exact ⟨old, by simpa [initial, Compiler.ZigAir.Memory.Heap.lookup_cons, Ne.symm same,
        ExpressionDeinit.Tests.initial] using found, _persistent⟩

theorem payload_owned : Owned 7 payload initial := Or.inr ⟨rfl, cell, rfl, rfl, rfl, rfl, rfl⟩

theorem complete_contract : ∃ after, observed = (.ok (), after) ∧ Post (some payload) initial after ∧
    after.memory.effects = 13 := by
  obtain ⟨after, executed, post, effects⟩ := run_verified external 7 (some payload) initial initial_valid
    (by intro selected same; cases Option.some.inj same; exact payload_owned)
  exact ⟨after, executed, post, effects⟩

theorem payload_dead : observed.1 = .ok () ∧ observed.2.invalidated = true ∧
    observed.2.memory.heap 3 = none ∧ observed.2.memory.memory.heap.lookup 3 = none ∧
    observed.2.memory.effects = 13 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem payload_alias_dead : Compiler.ZigAir.Memory.load observed.2.memory.memory
    (.pointer (.pointer true true byte) ⟨3, 1⟩) = .error .unallocated := by rfl'

theorem arguments_preserved : SliceValid 7 observed.2.memory.heap Arguments.Tests.first ∧
    observed.2.memory.memory.heap.lookup 0 = some Arguments.Tests.firstCell ∧
    observed.2.memory.memory.heap.lookup 1 = some Arguments.Tests.secondCell ∧
    observed.2.memory.memory.heap.lookup 2 = some Arguments.Tests.scratchCell :=
  ⟨Or.inr (by rfl'), by rfl', by rfl', by rfl'⟩

theorem arguments_contract : ∀ allocator arguments, SliceValid allocator initial.heap arguments →
    SliceValid allocator observed.2.memory.heap arguments := by
  obtain ⟨after, executed, post, _⟩ := complete_contract
  rw [executed]
  exact post.arguments

theorem allocation_history : observed.2.memory.memory.nextId = 4 ∧
    observed.2.memory.memory.nextAddress = 67 := ⟨by rfl', by rfl'⟩

theorem absent_payload : run external 999 none initial = (.ok (), ⟨initial, true⟩) := by rfl'
theorem empty_payload : run external 999 (some ⟨999, 0, 0⟩) initial = (.ok (), ⟨initial, true⟩) := by rfl'

theorem nonzero_offset_rejects (offset : Nat) (nonzero : offset ≠ 0) :
    free external 7 { payload with offset } initial = (.error (.ownership .bounds), initial) := by
  simp [free, payload, nonzero]

theorem nonzero_offset_not_owned (offset : Nat) (nonzero : offset ≠ 0) :
    ¬Owned 7 { payload with offset } initial := by
  simp [Owned, payload, nonzero]

theorem empty_offset_no_release (address offset : Nat) :
    free external 999 ⟨address, 0, offset⟩ initial = (.ok (), initial) := rfl

theorem offset_fault_keeps_value : run external 7 (some { payload with offset := 1 }) initial =
    (.error (.release (.ownership .bounds)), ⟨initial, false⟩) := by rfl'

theorem invalid_descriptor : execute external 7 (some payload) assemblyItemDeinitCode observed.2 =
    (.error .invalidDescriptor, observed.2) := by rfl'
theorem double_free : run external 7 (some payload) observed.2.memory =
    (.error (.release (.ownership .unallocated)), ⟨observed.2.memory, false⟩) := by rfl'

theorem wrong_allocator : run external 8 (some payload) initial =
    (.error (.release (.ownership .wrongAllocator)), ⟨initial, false⟩) := by rfl'
theorem wrong_registry_extent : run external 7 (some ⟨3, 2, 0⟩) initial =
    (.error (.release (.ownership .bounds)), ⟨initial, false⟩) := by rfl'
theorem arguments_not_bytes : run external 7 (some ⟨0, 3, 0⟩) initial =
    (.error (.release (.ownership .wrongType)), ⟨initial, false⟩) := by rfl'

def withCell (updated : Compiler.ZigAir.Memory.Allocation) : Session Nat :=
  { initial with memory := { initial.memory with heap := (3, updated) :: initial.memory.heap.tail } }

theorem readonly_payload : run external 7 (some payload) (withCell { cell with writable := false }) =
    (.error (.release (.memory .memoryValidity)), ⟨withCell { cell with writable := false }, false⟩) := by rfl'
theorem stack_payload : run external 7 (some payload) (withCell { cell with stack := true }) =
    (.error (.release (.memory .memoryValidity)), ⟨withCell { cell with stack := true }, false⟩) := by rfl'
theorem wrong_typed_extent : run external 7 (some payload) (withCell { cell with type := .array 2 byte }) =
    (.error (.release (.memory .memoryValidity)), ⟨withCell { cell with type := .array 2 byte }, false⟩) := by rfl'
theorem signed_bytes_rejected : run external 7 (some payload) (withCell { cell with type := .array 3 (.scalar (.int true 8)) }) =
    (.error (.release (.memory .memoryValidity)),
      ⟨withCell { cell with type := .array 3 (.scalar (.int true 8)) }, false⟩) := by rfl'
theorem wrong_typed_element : run external 7 (some payload) (withCell { cell with type := .array 3 (.scalar (.int false 16)) }) =
    (.error (.release (.memory .malformed)),
      ⟨withCell { cell with type := .array 3 (.scalar (.int false 16)) }, false⟩) := by rfl'
theorem malformed_heap : run external 7 (some payload) (withCell { cell with base := 0 }) =
    (.error (.release (.memory .malformed)), ⟨withCell { cell with base := 0 }, false⟩) := by rfl'

def missing : Session Nat := { initial with memory := Arguments.Tests.bytes }
theorem missing_backing : run external 7 (some payload) missing =
    (.error (.release (.memory .unallocated)), ⟨missing, false⟩) := by rfl'

end Compiler.Extraction.AssemblyItemDeinit.Tests
