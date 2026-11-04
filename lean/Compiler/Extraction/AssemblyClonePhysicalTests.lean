/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyClonePhysical
import Compiler.Extraction.ExpressionLifetimeTests

namespace Compiler.Extraction.AssemblyClone.Physical.Tests
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization
abbrev LifetimeTests := ExpressionDeinit.Lifetime.Tests.initial

def source : Bytes := ⟨3, [7, 8, 9], 0⟩
def sourceCell : Compiler.ZigAir.Memory.Allocation :=
  ⟨64, .array 3 AssemblyItemDeinit.byte, copiedCells source, true, false⟩
def initial : Session Nat :=
  { LifetimeTests with memory := { LifetimeTests.memory with heap := LifetimeTests.memory.heap.replace 3 sourceCell } }

theorem source_found : LifetimeTests.memory.heap.lookup 3 = some AssemblyItemDeinit.Tests.cell := by rfl'
theorem initial_frame (id : Nat) (apart : id ≠ 3) : initial.memory.heap.lookup id = LifetimeTests.memory.heap.lookup id := by
  exact Compiler.ZigAir.Memory.replace_other _ _ _ _ apart

theorem initial_valid : Valid initial := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro allocator id values nonempty stored
    have apart : id ≠ 3 := by
      intro same; subst id
      have impossible : LifetimeTests.heap 3 = some ⟨allocator, .arguments values⟩ := stored
      change (some (⟨7, .bytes 3⟩ : Memory.Allocation)) = some ⟨allocator, .arguments values⟩ at impossible
      cases impossible
    obtain ⟨⟨old, found, typed, writable, stack⟩, represented⟩ := ExpressionDeinit.Lifetime.Tests.initial_valid.related
      allocator id values nonempty stored
    exact ⟨⟨old, (initial_frame id apart).trans found, typed, writable, stack⟩,
      represented_frame _ values represented (initial_frame id apart)⟩
  · intro id block stored
    by_cases same : id = 3
    · subst id; exact ⟨sourceCell, by rfl', rfl⟩
    · obtain ⟨old, found, _persistent⟩ := ExpressionDeinit.Lifetime.Tests.initial_valid.injected id block stored
      exact ⟨old, (initial_frame id same).trans found, _persistent⟩

def input : Value Nat := ⟨ExpressionDeinit.Lifetime.Tests.itemValue, 42, some ⟨1, 2, source⟩⟩
def request (response : Option Nat := some 320) : Allocate Nat := fun length before =>
  (if length = 3 then response else none, before.effects * 10 + 6)
def copied : Value Nat := { input with verbatim := some ⟨1, 2, ⟨5, source.contents, 0⟩⟩ }
def result := run (request) 7 input initial
def target : ExpressionDeinit.Descriptor := ⟨4, ExpressionDeinit.Lifetime.Tests.incoming⟩
def bytes : AssemblyItemDeinit.Release Nat := fun _ before => before.effects * 10 + 2
def objects : AssemblyItem.Release Nat := fun _ before => before.effects * 10 + 3
def external := ExpressionDeinit.Lifetime.Tests.external
def destroyed := rollback (request) bytes objects external 7 input target initial

theorem initial_item : AssemblyItem.Owned 7 4 initial := ⟨⟨_, by rfl'⟩,
  ExpressionDeinit.Lifetime.Tests.object, by rfl', rfl, rfl, rfl⟩
theorem initial_arguments : SliceValid 7 initial.heap target.arguments := Or.inr (by rfl')
theorem clone_result : result.1 = .ok copied := by rfl'
theorem clone_contract : Cloned 7 input copied initial result.2 :=
  run_valid (request) 7 input copied initial result.2 initial_valid (Prod.ext clone_result rfl)
theorem source_readable : readable initial.memory source = true := by rfl'
theorem clone_retains_fields : copied.item = input.item ∧ copied.metadata = 42 ∧
    copied.verbatim.map (fun p => (p.arguments, p.returns, p.data.contents)) = some (1, 2, [7, 8, 9]) :=
  ⟨rfl, rfl, rfl⟩
theorem independent_payload : (payload copied) = some ⟨5, 3, 0⟩ ∧ result.2.memory.nextId = 6 ∧
    result.2.memory.nextAddress = 323 ∧ result.2.effects = 6 := ⟨rfl, by rfl', by rfl', by rfl'⟩

theorem complete_contract : ∃ after, destroyed = (.ok (), after) ∧
    ExpressionDeinit.Lifetime.Post (payload copied) target result.2 after :=
  (rollback_verified (request) bytes objects external 7 input copied target initial result.2 initial_valid
    initial_item initial_arguments (Prod.ext clone_result rfl)).2

theorem complete_cleanup : destroyed.1 = .ok () ∧ destroyed.2.invalidated = true ∧
    destroyed.2.memory.effects = 6234 ∧ destroyed.2.memory.heap 0 = none ∧
    destroyed.2.memory.heap 4 = none ∧ destroyed.2.memory.heap 5 = none ∧
    destroyed.2.memory.memory.heap.lookup 0 = none ∧ destroyed.2.memory.memory.heap.lookup 4 = none ∧
    destroyed.2.memory.memory.heap.lookup 5 = none :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem source_and_borrow_preserved : destroyed.2.memory.memory.heap.lookup 3 = some sourceCell ∧
    readable destroyed.2.memory.memory source = true ∧
    destroyed.2.memory.memory.heap.lookup 1 = initial.memory.heap.lookup 1 ∧
    destroyed.2.memory.memory.heap.lookup 2 = initial.memory.heap.lookup 2 := ⟨by rfl', by rfl', by rfl', by rfl'⟩

theorem absent_no_allocation : run (request) 7 { input with verbatim := none } initial =
    (.ok { input with verbatim := none }, initial) := rfl
def emptyInput := { input with verbatim := some ⟨1, 2, ⟨999, [], 0⟩⟩ }
theorem empty_no_allocation : run (request) 7 emptyInput initial =
    (.ok { emptyInput with verbatim := some ⟨1, 2, ⟨5, [], 0⟩⟩ }, initial) := by rfl'
theorem oom_keeps_effects : run (request none) 7 input initial =
    (.error .outOfMemory, { initial with effects := 6 }) := by rfl'
theorem oom_skips_reads : run (request none) 7 input LifetimeTests =
    (.error .outOfMemory, { LifetimeTests with effects := 6 }) := by rfl'
theorem oom_skips_cleanup : rollback (request none) bytes objects external 7 input target initial =
    (.error (.inl .outOfMemory), ⟨{ initial with effects := 6 }, false⟩) := by rfl'
theorem overlap_rejected : run (request (some 64)) 7 input initial =
    (.error (.memory .memoryValidity), { initial with effects := 6 }) := by rfl'
def unreadable := run (request) 7 input LifetimeTests
theorem unreadable_retains_allocation : unreadable.1 = .error .sourceMismatch ∧
    unreadable.2.effects = 6 ∧ unreadable.2.memory.nextId = 6 ∧ unreadable.2.memory.nextAddress = 323 ∧
    unreadable.2.heap 5 = some ⟨7, .bytes 3⟩ ∧
    unreadable.2.memory.heap.lookup 5 = some (cell 3 320 []) :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩
theorem wrong_source_contents : (duplicate (request) 7 ⟨3, [8, 8, 9], 0⟩ initial).1 = .error .sourceMismatch := by rfl'
def readonly : Session Nat := { initial with memory := { initial.memory with
  heap := initial.memory.heap.replace 3 { sourceCell with writable := false } } }
theorem readonly_source : (run (request) 7 input readonly).1 = .ok copied := by rfl'
def collision : Session Nat := { initial with heap := write initial.heap 5 (some ⟨9, .bytes 8⟩) }
theorem collision_retains_typed_allocation : (duplicate (request) 7 source collision).1 = .error .registryCollision ∧
    (duplicate (request) 7 source collision).2.memory.heap.lookup 5 = some (cell 3 320 []) ∧
    (duplicate (request) 7 source collision).2.effects = 6 := ⟨by rfl', by rfl', by rfl'⟩

-- The source is an interior readonly view; only the freshly copied output
-- owns a complete allocation at offset zero.
def offsetSource : Bytes := ⟨3, [8, 9], 1⟩
def offsetInput : Value Nat := { input with verbatim := some ⟨1, 2, offsetSource⟩ }
def offsetRequest (response : Option Nat := some 320) : Allocate Nat := fun length before =>
  (if length = 2 then response else none, before.effects * 10 + 6)
def offsetCopied : Value Nat := { input with verbatim := some ⟨1, 2, ⟨5, [8, 9], 0⟩⟩ }
def offsetResult := run (offsetRequest) 7 offsetInput initial

theorem offset_descriptor : payload offsetInput = some ⟨3, 2, 1⟩ := rfl
theorem offset_reads : readable initial.memory offsetSource = true ∧
    readable initial.memory { offsetSource with offset := 0 } = false := ⟨by rfl', by rfl'⟩
theorem offset_clone_result : offsetResult.1 = .ok offsetCopied := by rfl'
theorem offset_clone_contract : Cloned 7 offsetInput offsetCopied initial offsetResult.2 :=
  run_valid (offsetRequest) 7 offsetInput offsetCopied initial offsetResult.2 initial_valid
    (Prod.ext offset_clone_result rfl)
theorem offset_copy_extent : offsetResult.2.memory.heap.lookup 5 = some (cell 2 320 [(0, number 8), (1, number 9)]) ∧
    offsetResult.2.memory.nextId = 6 ∧ offsetResult.2.memory.nextAddress = 322 ∧
    offsetResult.2.memory.heap.lookup 3 = some sourceCell ∧ payload offsetCopied = some ⟨5, 2, 0⟩ :=
  ⟨by rfl', by rfl', by rfl', by rfl', rfl⟩
theorem offset_readonly_source : (run (offsetRequest) 7 offsetInput readonly).1 = .ok offsetCopied := by rfl'

def beyondSource : Bytes := ⟨3, [9, 0], 2⟩
def beyondResult := duplicate (offsetRequest) 7 beyondSource initial
theorem offset_bounds_retain_allocation :
    Compiler.ZigAir.Memory.load initial.memory (pointer beyondSource 0) = .ok (number 9) ∧
    beyondResult.1 = .error .sourceMismatch ∧ beyondResult.2.effects = 6 ∧
    beyondResult.2.memory.heap.lookup 5 = some (cell 2 320 []) ∧
    beyondResult.2.memory.nextId = 6 := ⟨by rfl', by rfl', by rfl', by rfl', by rfl'⟩

theorem offset_oom_skips_reads : duplicate (offsetRequest none) 7 { offsetSource with offset := 2^64 } initial =
    (.error .outOfMemory, { initial with effects := 6 }) := by rfl'
theorem offset_empty_skips_reads (address offset : Nat) : duplicate (offsetRequest none) 7 ⟨address, [], offset⟩ initial =
    (.ok ⟨5, [], 0⟩, initial) := rfl

def offsetDestroyed := rollback (offsetRequest) bytes objects external 7 offsetInput target initial
theorem offset_rollback_contract : ∃ after, offsetDestroyed = (.ok (), after) ∧
    ExpressionDeinit.Lifetime.Post (payload offsetCopied) target offsetResult.2 after :=
  (rollback_verified (offsetRequest) bytes objects external 7 offsetInput offsetCopied target initial offsetResult.2
    initial_valid initial_item initial_arguments (Prod.ext offset_clone_result rfl)).2
theorem offset_cleanup : offsetDestroyed.1 = .ok () ∧ offsetDestroyed.2.invalidated = true ∧
    offsetDestroyed.2.memory.effects = 6234 ∧ offsetDestroyed.2.memory.memory.heap.lookup 5 = none ∧
    offsetDestroyed.2.memory.memory.heap.lookup 3 = some sourceCell ∧
    offsetDestroyed.2.memory.memory.heap.lookup 1 = initial.memory.heap.lookup 1 ∧
    readable offsetDestroyed.2.memory.memory offsetSource = true :=
  ⟨by rfl', by rfl', by rfl', by rfl', by rfl', by rfl', by rfl'⟩

end Compiler.Extraction.AssemblyClone.Physical.Tests
