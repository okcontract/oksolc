/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeFallbackFrame
import Compiler.Extraction.RepresentativeRelocationTests

namespace Compiler.Extraction.RepresentativeArray.Backing.Fallback.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

def before (runtimeSafety : Bool) : Session Release.Tests.Effects := {
  Relocation.Tests.before runtimeSafety with
  heap := Compiler.Extraction.Memory.write (Relocation.Tests.before runtimeSafety).heap 4 none
  memory := {erase (Relocation.Tests.before runtimeSafety).memory 4 with nextId := 4}
  effects := [(7, 0, 96, 8)] }
def request (response : Option Nat := some 640) : Registry.Allocate Release.Tests.Effects := Registry.Tests.request response
def reserved (runtimeSafety : Bool) : Session Release.Tests.Effects := {
  before runtimeSafety with
  heap := Compiler.Extraction.Memory.write (before runtimeSafety).heap 4 (some ⟨7, .representatives []⟩)
  memory := RegionAllocation.extend (before runtimeSafety).memory (Backing.type 5) 160 640
  effects := [(7, 0, 96, 8), (7, 0, 160, 8)] }

theorem initial_valid (runtimeSafety : Bool) : Valid (before runtimeSafety) := by
  refine ⟨by cases runtimeSafety <;> decide, ?_, ?_⟩
  · intro allocator id values nonempty stored
    have apart : id ≠ 4 := by intro same; simp [before, Compiler.Extraction.Memory.write, same] at stored
    have original := stored
    simp only [before, Compiler.Extraction.Memory.write, if_neg apart] at original
    obtain ⟨⟨cell, found, typed, writable, persistent⟩, represented⟩ :=
      (Relocation.Tests.initial_valid runtimeSafety).related allocator id values nonempty original
    have frame : (before runtimeSafety).memory.heap.lookup id = (Relocation.Tests.before runtimeSafety).memory.heap.lookup id := by
      simp only [before, erase_lookup, if_neg apart]
    exact ⟨⟨cell, frame.trans found, typed, writable, persistent⟩, represented_frame _ values represented frame⟩
  · intro id block stored
    have apart : id ≠ 4 := by intro same; simp [before, Compiler.Extraction.Memory.write, same] at stored
    simp only [before, Compiler.Extraction.Memory.write, if_neg apart] at stored
    obtain ⟨cell, found, persistent⟩ := (Relocation.Tests.initial_valid runtimeSafety).injected id block stored
    exact ⟨cell, (by simpa only [before, erase_lookup, if_neg apart] using found), persistent⟩

theorem fits (runtimeSafety : Bool) : RegionAllocation.Fits (before runtimeSafety).memory ⟨160, 8⟩ 640 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  change entry ∈ [(3, Relocation.Tests.owner runtimeSafety), (2, {FieldTests.data with cells := Append.Tests.newCells}),
    (1, Expression.Tests.argumentsAllocation), (0, Expression.Tests.itemAllocation)] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  all_goals cases runtimeSafety <;> cases shaped <;> decide

theorem actual_reservation (runtimeSafety : Bool) : Registry.run request 7 5 (before runtimeSafety) =
    (.ok (some ⟨4, 0⟩), reserved runtimeSafety) := by cases runtimeSafety <;> rfl

theorem reserved_is_suffix_fixture (runtimeSafety : Bool) : reserved runtimeSafety = Relocation.Tests.before runtimeSafety := by
  have registry : (reserved runtimeSafety).heap = (Relocation.Tests.before runtimeSafety).heap := by
    funext id
    by_cases same : id = 4 <;> simp [reserved, before, Compiler.Extraction.Memory.write, same,
      Relocation.Tests.before, RegisteredCopy.Tests.registry]
  have memory : (reserved runtimeSafety).memory = (Relocation.Tests.before runtimeSafety).memory := by cases runtimeSafety <;> rfl
  change (⟨(reserved runtimeSafety).heap, (reserved runtimeSafety).memory, (reserved runtimeSafety).effects⟩ : Session _) = _
  rw [registry, memory]
  rfl

theorem source_owned (runtimeSafety : Bool) : Release.Owned 7 ⟨2, 0⟩ 3 (before runtimeSafety) :=
  ⟨rfl, ⟨[], rfl⟩, _, rfl, rfl, rfl, rfl⟩
theorem header_loaded (runtimeSafety : Bool) : readItems (before runtimeSafety).memory ⟨3, 16⟩ =
    .ok (.slice itemsType ⟨2, 0⟩ 2) := by cases runtimeSafety <;> rfl
theorem saved_full_capacity (runtimeSafety : Bool) : allocatedSlice (before runtimeSafety).memory ⟨3, 16⟩ =
    .ok (.slice itemsType ⟨2, 0⟩ 3) :=
  allocatedSlice_nonempty _ _ 2 3 _ (initial_valid runtimeSafety).memory rfl rfl (by decide)
    (readItemsData_from_loaded runtimeSafety _ 3 (Relocation.Tests.owner runtimeSafety) _ 2 (initial_valid runtimeSafety).memory
      rfl rfl (header_loaded runtimeSafety)) (by cases runtimeSafety <;> rfl)

theorem source_ready (runtimeSafety : Bool) : ∀ index, index < 2 → ∀ slot ∈ expressionSlots,
    ∃ value, Expression.readField (before runtimeSafety).memory false ⟨2, index * 32⟩ slot.1 = .ok value := by
  intro index inside slot member
  obtain ⟨value, loaded⟩ := Relocation.Tests.source_ready runtimeSafety index inside slot member
  exact ⟨value, (RegisteredCopy.read_field_frame _ _ _ _ (by rfl)).trans loaded⟩

theorem actual_fallback (runtimeSafety : Bool) : run request Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (before runtimeSafety) =
    (.ok (some ()), Relocation.Tests.after runtimeSafety) := by
  exact of_steps request Release.Tests.external 7 _ _ _ 3 5 _ _ _ (actual_reservation runtimeSafety)
    (by rw [reserved_is_suffix_fixture]; exact Relocation.Tests.actual_relocation runtimeSafety)

theorem without_final_premises (runtimeSafety : Bool) : ∃ oldCell after,
    (before runtimeSafety).memory.heap.lookup 2 = some oldCell ∧
    run request Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (before runtimeSafety) = (.ok (some ()), after) ∧
    Valid after ∧ Release.Owned 7 ⟨4, 0⟩ 5 after ∧
    after.heap = Compiler.Extraction.Memory.write
      (Compiler.Extraction.Memory.write (before runtimeSafety).heap 4 (some ⟨7, .representatives []⟩)) 2 none ∧
    after.effects = Release.Tests.external 7 oldCell.base 96 8 [(7, 0, 96, 8), (7, 0, 160, 8)] ∧
    after.memory.nextId = 5 ∧ after.memory.nextAddress = max (before runtimeSafety).memory.nextAddress 800 ∧
    after.memory.heap.lookup 2 = none ∧ readHeader after.memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 2, .scalar (.int false 64 5)) ∧
    (∀ index, index < 2 → Expression.readFields after.memory false ⟨4, index * 32⟩ =
      Expression.readFields (before runtimeSafety).memory false ⟨2, index * 32⟩) ∧
    (∀ query, query ≠ 2 → query ≠ 4 → query ≠ 3 → after.memory.heap.lookup query = (before runtimeSafety).memory.heap.lookup query) :=
  verified runtimeSafety request Release.Tests.external 7 3 2 3 5 2 640 (before runtimeSafety) _ (Relocation.Tests.owner runtimeSafety)
    (initial_valid runtimeSafety) rfl rfl rfl (source_owned runtimeSafety) (by decide) (by decide) (by decide) (by decide)
    rfl (fits runtimeSafety) (header_loaded runtimeSafety) (source_ready runtimeSafety)

theorem oom_before_header (runtimeSafety : Bool) (header oldData : Address) :
    run (request none) Release.Tests.external 7 header oldData 3 5 (before runtimeSafety) =
      (.ok none, {before runtimeSafety with effects := [(7, 0, 96, 8), (7, 0, 160, 8)]}) :=
  oom_verified (request none) Release.Tests.external 7 header oldData 3 5 (before runtimeSafety) _
    (initial_valid runtimeSafety).memory (by decide) (by decide) rfl

theorem bad_response_keeps_effects (runtimeSafety : Bool) :
    run (request (some 641)) Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (before runtimeSafety) =
      (.error (.memory .memoryValidity), {before runtimeSafety with effects := [(7, 0, 96, 8), (7, 0, 160, 8)]}) := by
  cases runtimeSafety <;> rfl

theorem short_release_retains_allocation_and_copy (runtimeSafety : Bool) :
    run request Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ 2 5 (before runtimeSafety) =
      (.error (.memory .memoryValidity), Relocation.Tests.copied runtimeSafety) := by
  simp only [run, actual_reservation, reserved_is_suffix_fixture, Relocation.Tests.short_free_keeps_copy, Except.map]

theorem bad_header_retains_allocation (runtimeSafety : Bool) :
    run request Release.Tests.external 7 ⟨99, 0⟩ ⟨2, 0⟩ 3 5 (before runtimeSafety) =
      (.error (.memory .unallocated), reserved runtimeSafety) := by
  simp only [run, actual_reservation]
  cases runtimeSafety <;> rfl

def collision (runtimeSafety : Bool) : Session Release.Tests.Effects := {before runtimeSafety with
  heap := Compiler.Extraction.Memory.write (before runtimeSafety).heap 4 (some ⟨8, .bytes 8⟩)}
theorem collision_retains_typed_allocation (runtimeSafety : Bool) :
    run request Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (collision runtimeSafety) =
      (.error (.ownership .notFresh), {collision runtimeSafety with
        memory := (reserved runtimeSafety).memory
        effects := (reserved runtimeSafety).effects}) := by
  have rejected : Registry.run request 7 5 (collision runtimeSafety) =
      (.error (.registry .notFresh), {collision runtimeSafety with
        memory := (reserved runtimeSafety).memory
        effects := (reserved runtimeSafety).effects}) := by cases runtimeSafety <;> rfl
  simp only [run, rejected]

def damaged (runtimeSafety : Bool) : Session Release.Tests.Effects := {before runtimeSafety with memory :=
  {(before runtimeSafety).memory with heap := (before runtimeSafety).memory.heap.replace 2 Relocation.Tests.damagedSource}}
def copyPrefix (runtimeSafety : Bool) : Session Release.Tests.Effects := {reserved runtimeSafety with memory :=
  {(reserved runtimeSafety).memory with
    heap := ((reserved runtimeSafety).memory.heap.replace 2 Relocation.Tests.damagedSource).replace 4 {RepresentativeArray.Copy.Tests.targetCell with cells := [(0, Expression.Tests.item)]}}}
theorem copy_fault_retains_allocation_and_prefix (runtimeSafety : Bool) :
    run request Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (damaged runtimeSafety) =
      (.error (.memory .uninitialized), copyPrefix runtimeSafety) := by cases runtimeSafety <;> rfl

theorem capacity_overflow_skips_allocation (runtimeSafety : Bool) :
    run request Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 (addressLimit / 32) (before runtimeSafety) =
      (.ok none, before runtimeSafety) := by cases runtimeSafety <;> rfl

theorem parent_contents (runtimeSafety : Bool) : WordArray.Represents (before runtimeSafety).memory ⟨1, 1, 2⟩ [99, 1] :=
  represented_frame _ _ (Relocation.Tests.parent_contents runtimeSafety) (by rfl)

theorem every_outcome_preserves_parent (runtimeSafety : Bool) (allocator oldCapacity capacity : Nat) (oldData : Address)
    (response : Option Nat) (nonempty : capacity ≠ 0) :
    WordArray.Represents (run (request response) Release.Tests.external allocator ⟨3, 16⟩ oldData oldCapacity capacity
      (before runtimeSafety)).2.memory ⟨1, 1, 2⟩ [99, 1] :=
  (parent_borrow runtimeSafety (request response) Release.Tests.external allocator 3 oldCapacity capacity oldData (before runtimeSafety)
    (Relocation.Tests.owner runtimeSafety) (initial_valid runtimeSafety) nonempty rfl rfl ⟨1, 1, 2⟩ [99, 1] 4
    Expression.Tests.argumentsAllocation rfl rfl (parent_contents runtimeSafety)).2

end Compiler.Extraction.RepresentativeArray.Backing.Fallback.Tests
