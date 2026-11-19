/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingCopy
import Compiler.Extraction.RepresentativeBackingRegistryTests
import Compiler.Extraction.RepresentativeArrayCopyTests

namespace Compiler.Extraction.RepresentativeArray.Backing.RegisteredCopy.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

def registry : Compiler.Extraction.Memory.Heap := fun id =>
  if id = 1 then some ⟨7, .arguments [777, 99, 1, 5]⟩ else
  if id = 2 ∨ id = 4 then some ⟨7, .representatives []⟩ else none
def before : Session (List Nat) := ⟨registry, RepresentativeArray.Copy.Tests.before, [11, 13]⟩
def after : Session (List Nat) := { before with memory := RepresentativeArray.Copy.Tests.after }

theorem initial_valid : Valid before := by
  refine ⟨RepresentativeArray.Copy.Tests.initial_valid, ?_, ?_⟩
  · intro owner id values nonempty stored
    by_cases parent : id = 1
    · subst id
      have same : (⟨7, .arguments [777, 99, 1, 5]⟩ : Compiler.Extraction.Memory.Allocation) = ⟨owner, .arguments values⟩ :=
        Option.some.inj (by simpa only [before, registry, ↓reduceIte] using stored)
      cases same
      refine ⟨⟨Expression.Tests.argumentsAllocation, rfl, rfl, rfl, rfl⟩, rfl, ?_⟩
      intro index inside
      have choice : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by simp at inside; omega
      rcases choice with rfl | rfl | rfl | rfl <;> rfl
    · by_cases vector : id = 2 ∨ id = 4 <;> simp [before, registry, parent, vector] at stored
  · intro id block stored
    by_cases parent : id = 1
    · subst id; exact ⟨Expression.Tests.argumentsAllocation, rfl, rfl⟩
    · by_cases vector : id = 2 ∨ id = 4
      · rcases vector with rfl | rfl <;> exact ⟨_, rfl, rfl⟩
      · simp [before, registry, parent, vector] at stored

theorem source_owned : Release.Owned 7 ⟨2, 0⟩ 3 before := ⟨rfl, ⟨[], rfl⟩, _, rfl, rfl, rfl, rfl⟩
theorem target_owned : Release.Owned 7 ⟨4, 0⟩ 5 before := ⟨rfl, ⟨[], rfl⟩, _, rfl, rfl, rfl, rfl⟩

theorem actual_copy : run 2 4 2 before = (.ok (), after) := by
  simp only [run, before, RepresentativeArray.Copy.Tests.actual_complete_copy]
  rfl

theorem without_final_premises : ∃ finalState, run 2 4 2 before = (.ok (), finalState) ∧ Valid finalState ∧
    Release.Owned 7 ⟨4, 0⟩ 5 finalState ∧ finalState.heap = before.heap ∧ finalState.effects = before.effects ∧
    finalState.memory.nextId = before.memory.nextId ∧ finalState.memory.nextAddress = before.memory.nextAddress ∧
    (∀ query, query ≠ 4 → finalState.memory.heap.lookup query = before.memory.heap.lookup query) ∧
    (∀ index, index < 2 → Expression.readFields finalState.memory false ⟨4, index * 32⟩ =
      Expression.readFields before.memory false ⟨2, index * 32⟩) :=
  verified 2 4 2 7 5 before initial_valid target_owned (by decide) (by decide) RepresentativeArray.Copy.Tests.initialized_source

theorem registered_arguments_survive (length : Nat) : Valid (run 2 4 length before).2 :=
  (storage 2 4 length 7 [] before initial_valid rfl).1

theorem both_release_permissions_survive (length : Nat) :
    Release.Owned 7 ⟨2, 0⟩ 3 (run 2 4 length before).2 ∧ Release.Owned 7 ⟨4, 0⟩ 5 (run 2 4 length before).2 :=
  ⟨owned 2 4 length 7 3 ⟨2, 0⟩ before initial_valid.memory source_owned,
    owned 2 4 length 7 5 ⟨4, 0⟩ before initial_valid.memory target_owned⟩

theorem offset_parent_survives (length : Nat) :
    WordArray.Represents (run 2 4 length before).2.memory ⟨1, 1, 2⟩ [99, 1] :=
  (parent_borrow 2 4 length 5 before RepresentativeArray.Copy.Tests.targetCell ⟨1, 1, 2⟩ [99, 1] 4
    Expression.Tests.argumentsAllocation initial_valid.memory rfl rfl rfl rfl RepresentativeArray.Copy.Tests.parent_contents).2

theorem copy_does_not_publish : after.heap 4 = some ⟨7, .representatives []⟩ ∧
    readHeader after.memory ⟨3, 0⟩ = readHeader before.memory ⟨3, 0⟩ ∧ after.effects = [11, 13] := ⟨rfl, rfl, rfl⟩

theorem complete_fields : Expression.readFields after.memory false ⟨4, 32⟩ =
    .ok [Expression.Tests.item, Expression.Tests.arguments, FieldTests.id, FieldTests.sequence] := by decide

def partialInput : Session (List Nat) := { before with memory := RepresentativeArray.Copy.Tests.partialState }
theorem partial_failure_keeps_writes : run 2 4 2 partialInput =
    (.error .uninitialized, { partialInput with memory := RepresentativeArray.Copy.Tests.partialAfter }) := by
  simp only [run, partialInput, RepresentativeArray.Copy.Tests.partial_slice_retains_item_and_prior_descriptor.2.1]

theorem prefix_failure_keeps_writes : run 2 4 3 before = (.error .uninitialized, after) := by
  unfold run
  rw [show RepresentativeArray.Copy.run before.memory 2 4 3 = (.error .uninitialized, RepresentativeArray.Copy.Tests.after)
    from RepresentativeArray.Copy.Tests.copying_spare_source_rejects_after_prefix]
  rfl

theorem short_target_keeps_writes : run 2 4 2 { before with memory := RepresentativeArray.Copy.Tests.shortTarget } =
    (.error .memoryValidity, { before with memory := RepresentativeArray.Copy.Tests.shortAfter }) := by
  simp only [run, RepresentativeArray.Copy.Tests.short_target_retains_first_descriptor.2]

theorem readonly_rejects : run 2 4 2 { before with memory := RepresentativeArray.Copy.Tests.readonlyTarget } =
    (.error .readOnly, { before with memory := RepresentativeArray.Copy.Tests.readonlyTarget }) := by
  simp only [run, RepresentativeArray.Copy.Tests.readonly_target_rejects_without_writes]

theorem overlap_rejects : run 2 2 1 before = (.error .memoryValidity, before) := rfl
theorem empty_skips_sentinels : run 99 99 0 before = (.ok (), before) := rfl
theorem stale_source_rejects : run 2 4 1 { before with memory := erase before.memory 2 } =
    (.error .unallocated, { before with memory := erase before.memory 2 }) := rfl

theorem reserved_source_ready : ∀ index, index < 2 → ∀ slot ∈ expressionSlots,
    ∃ value, Expression.readField Registry.Tests.before.memory false ⟨2, index * 32⟩ slot.1 = .ok value := by
  intro index inside slot member
  have choice : index = 0 ∨ index = 1 := by omega
  rcases slot with ⟨offset, type⟩
  simp only [expressionSlots, Expression.allocationType, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, Field.type, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals rcases choice with rfl | rfl
  all_goals exact ⟨_, rfl⟩

theorem reservation_copy_without_final_premises : ∃ reserved finalState,
    Registry.run Registry.Tests.request 7 7 Registry.Tests.before = (.ok (some ⟨4, 0⟩), reserved) ∧
    run 2 4 2 reserved = (.ok (), finalState) ∧ Valid finalState ∧ Release.Owned 7 ⟨4, 0⟩ 7 finalState ∧
    finalState.heap = Compiler.Extraction.Memory.write Registry.Tests.before.heap 4 (some ⟨7, .representatives []⟩) ∧
    finalState.effects = Registry.Tests.before.effects ++ [(7, 0, 224, 8)] ∧
    finalState.memory.nextId = 5 ∧ finalState.memory.nextAddress = 1024 ∧
    (∀ query, query ≠ 4 → finalState.memory.heap.lookup query = Registry.Tests.before.memory.heap.lookup query) ∧
    (∀ index, index < 2 → Expression.readFields finalState.memory false ⟨4, index * 32⟩ =
      Expression.readFields Registry.Tests.before.memory false ⟨2, index * 32⟩) :=
  reserve_verified Registry.Tests.request 7 7 800 2 2 Registry.Tests.before _ Release.Tests.backing Registry.Tests.initial_valid
    (by decide) (by decide) (by decide) rfl Registry.Tests.fits rfl reserved_source_ready

end Compiler.Extraction.RepresentativeArray.Backing.RegisteredCopy.Tests
