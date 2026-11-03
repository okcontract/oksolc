/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeDescriptorPreservation
import Compiler.Extraction.RepresentativeFallbackTests

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation.Tests
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Descriptor fixtures deliberately do not claim item-payload correspondence.
Both rows refer to existing full owned argument storage; the independent parent
view used by the relocation regressions remains an offset into that storage. -/
def first : Storage.Cell := ⟨⟨1, some 16, 0⟩, 0, 0, [777, 99, 1, 5], 23, 1⟩
def second : Storage.Cell := {first with sequence := 29}
def nodes : List Storage.Cell := [first, second]
def firstCells : Cells := [(28, .scalar (.int false 32 23)), (24, .scalar (.int false 32 0)),
  (16, .scalar (.int false 64 4)), (8, .pointer (.pointer true true WordArray.word) ⟨1, 0⟩), (0, Expression.Tests.item)]
def allCells : Cells := [(60, .scalar (.int false 32 29)), (56, .scalar (.int false 32 1)),
  (48, .scalar (.int false 64 4)), (40, .pointer (.pointer true true WordArray.word) ⟨1, 0⟩), (32, Expression.Tests.item)] ++ firstCells
def backing (cells : Cells) : Allocation := {FieldTests.data with cells}
def memory (runtimeSafety : Bool) (cells : Cells) : State := {(Backing.Fallback.Tests.before runtimeSafety).memory with
  heap := (Backing.Fallback.Tests.before runtimeSafety).memory.heap.replace 2 (backing cells)}
def before (runtimeSafety : Bool) : Session Backing.Release.Tests.Effects :=
  {Backing.Fallback.Tests.before runtimeSafety with memory := memory runtimeSafety allCells}

theorem initial_valid (runtimeSafety : Bool) : Valid (before runtimeSafety) := by
  refine ⟨by cases runtimeSafety <;> decide, ?_, ?_⟩
  · intro allocator id contents nonempty stored
    have apart : id ≠ 2 := by intro same; subst id; simp [before, Backing.Fallback.Tests.before, Compiler.Extraction.Memory.write,
      Backing.Relocation.Tests.before, Backing.RegisteredCopy.Tests.registry] at stored
    obtain ⟨⟨cell, found, typed, writable, persistent⟩, represented⟩ :=
      (Backing.Fallback.Tests.initial_valid runtimeSafety).related allocator id contents nonempty stored
    have kept : (before runtimeSafety).memory.heap.lookup id = (Backing.Fallback.Tests.before runtimeSafety).memory.heap.lookup id :=
      replace_other _ 2 id _ apart
    exact ⟨⟨cell, kept.trans found, typed, writable, persistent⟩, represented_frame _ contents represented kept⟩
  · intro id block stored
    by_cases same : id = 2
    · subst id; exact ⟨backing allCells, by cases runtimeSafety <;> rfl, rfl⟩
    · obtain ⟨cell, found, persistent⟩ := (Backing.Fallback.Tests.initial_valid runtimeSafety).injected id block stored
      exact ⟨cell, (replace_other _ 2 id _ same).trans found, persistent⟩

theorem first_initialized (runtimeSafety : Bool) : initializeFields (memory runtimeSafety []) 2 0 ⟨0, 0⟩ ⟨1, 0⟩ 4 0 23 =
    .ok (memory runtimeSafety firstCells) := by cases runtimeSafety <;> rfl
theorem second_initialized (runtimeSafety : Bool) : initializeFields (memory runtimeSafety firstCells) 2 1 ⟨0, 0⟩ ⟨1, 0⟩ 4 1 29 =
    .ok (memory runtimeSafety allCells) := by cases runtimeSafety <;> rfl

theorem prefix_from_initialization (runtimeSafety : Bool) : Prefix (before runtimeSafety).memory 2 nodes := by
  obtain ⟨one, ranOne, validOne, _, prefixOne⟩ := initialize_prefix (memory runtimeSafety []) 2 3 (backing []) [] first
    (by cases runtimeSafety <;> decide) (by cases runtimeSafety <;> rfl) rfl rfl (empty _ _) (by decide) (by decide) (by decide)
  change initializeFields (memory runtimeSafety []) 2 0 ⟨0, 0⟩ ⟨1, 0⟩ 4 0 23 = .ok one at ranOne
  rw [first_initialized] at ranOne
  cases Except.ok.inj ranOne
  obtain ⟨two, ranTwo, _, _, prefixTwo⟩ := initialize_prefix (memory runtimeSafety firstCells) 2 3 (backing firstCells) [first] second
    validOne (by cases runtimeSafety <;> rfl) rfl rfl prefixOne (by decide) (by decide) (by decide)
  change initializeFields (memory runtimeSafety firstCells) 2 1 ⟨0, 0⟩ ⟨1, 0⟩ 4 1 29 = .ok two at ranTwo
  rw [second_initialized] at ranTwo
  cases Except.ok.inj ranTwo
  exact prefixTwo

theorem all_initial_queries (runtimeSafety : Bool) (id : Compiler.Algebraic.NodeId) :
    representativeFields (before runtimeSafety).memory ⟨3, 16⟩ id =
      .ok ((Storage.representativeProgram.run nodes id).map (values id.toNat)) :=
  query _ _ 2 3 (backing allCells) nodes id (initial_valid runtimeSafety).memory
    (by cases runtimeSafety <;> rfl) (by cases runtimeSafety <;> rfl) rfl rfl (by decide) (prefix_from_initialization runtimeSafety)

theorem fits (runtimeSafety : Bool) : RegionAllocation.Fits (before runtimeSafety).memory ⟨160, 8⟩ 640 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  change entry ∈ [(3, Backing.Relocation.Tests.owner runtimeSafety), (2, backing allCells),
    (1, Expression.Tests.argumentsAllocation), (0, Expression.Tests.itemAllocation)] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  all_goals cases runtimeSafety <;> cases shaped <;> decide

theorem fallback_without_final_premises (runtimeSafety : Bool) : ∃ after,
    Backing.Fallback.run Backing.Fallback.Tests.request Backing.Release.Tests.external 7 ⟨3, 16⟩ ⟨2, 0⟩ 3 5 (before runtimeSafety) =
      (.ok (some ()), after) ∧ Valid after ∧ Backing.Release.Owned 7 ⟨4, 0⟩ 5 after ∧ after.memory.heap.lookup 2 = none ∧
      readHeader after.memory ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 2, .scalar (.int false 64 5)) ∧
      Prefix after.memory 4 nodes ∧ ∀ id, representativeFields after.memory ⟨3, 16⟩ id =
        .ok ((Storage.representativeProgram.run nodes id).map (values id.toNat)) :=
  fallback_verified runtimeSafety Backing.Fallback.Tests.request Backing.Release.Tests.external 7 3 2 3 5 640 (before runtimeSafety)
    _ (Backing.Relocation.Tests.owner runtimeSafety) nodes (initial_valid runtimeSafety) (by cases runtimeSafety <;> rfl) rfl rfl
    ⟨rfl, ⟨[], rfl⟩, backing allCells, by cases runtimeSafety <;> rfl, rfl, rfl, rfl⟩
    (by decide) (by decide) (by decide) (by decide) rfl (fits runtimeSafety) (by cases runtimeSafety <;> rfl)
    (prefix_from_initialization runtimeSafety)

theorem offset_borrow_still_live (runtimeSafety : Bool) : WordArray.Represents (before runtimeSafety).memory ⟨1, 1, 2⟩ [99, 1] :=
  represented_frame _ _ (Backing.Fallback.Tests.parent_contents runtimeSafety) (by rfl)

theorem wrong_item_rejects (runtimeSafety : Bool) : ¬Row (before runtimeSafety).memory 2 1 {second with itemAddress := 9} := by
  simp only [Row]; cases runtimeSafety <;> decide
theorem wrong_arguments_reject (runtimeSafety : Bool) : ¬Row (before runtimeSafety).memory 2 1 {second with argumentsAddress := 9} := by
  simp only [Row]; cases runtimeSafety <;> decide
theorem short_arguments_reject (runtimeSafety : Bool) : ¬Row (before runtimeSafety).memory 2 1 {second with arguments := [99, 1]} := by
  simp only [Row]; cases runtimeSafety <;> decide
theorem wrong_sequence_rejects (runtimeSafety : Bool) : ¬Row (before runtimeSafety).memory 2 1 {second with sequence := 0} := by
  simp only [Row]; cases runtimeSafety <;> decide
theorem arbitrary_descriptors_are_not_nodes (runtimeSafety : Bool) :
    ¬Prefix (Backing.Fallback.Tests.before runtimeSafety).memory 2 nodes := by
  intro claimed
  have row := claimed 0 first rfl
  have rejected : ¬Row (Backing.Fallback.Tests.before runtimeSafety).memory 2 0 first := by
    simp only [Row]; cases runtimeSafety <;> decide
  exact rejected row

theorem missing_second_row_rejects (runtimeSafety : Bool) : ¬Prefix (memory runtimeSafety firstCells) 2 nodes := by
  intro claimed
  have rejected : ¬Row (memory runtimeSafety firstCells) 2 1 second := by
    simp only [Row]; cases runtimeSafety <;> decide
  exact rejected (claimed 1 second rfl)

theorem wrong_stored_id_rejects (runtimeSafety : Bool) :
    ¬Row (memory runtimeSafety (allCells.map (fun slot => if slot.1 = 56 then (56, .scalar (.int false 32 0)) else slot))) 2 1 second := by
  simp only [Row]; cases runtimeSafety <;> decide

theorem interior_owned_arguments_reject (runtimeSafety : Bool) :
    ¬Row (memory runtimeSafety (allCells.map (fun slot =>
      if slot.1 = 40 then (40, .pointer (.pointer true true WordArray.word) ⟨1, 4⟩)
      else if slot.1 = 48 then (48, .scalar (.int false 64 2)) else slot))) 2 1 {second with arguments := [99, 1]} := by
  simp only [Row]; cases runtimeSafety <;> decide

/-- A later malformed descriptor retains the complete previous row. The actual
failure occurs after the new item store; no rollback or default row is inferred. -/
theorem rejected_initialization_keeps_old_row (runtimeSafety : Bool) :
    (initializeFieldsReached (memory runtimeSafety firstCells) 2 1 ⟨0, 0⟩ ⟨1, 0⟩ addressLimit 1 29).1 = .error .malformed ∧
    Row (initializeFieldsReached (memory runtimeSafety firstCells) 2 1 ⟨0, 0⟩ ⟨1, 0⟩ addressLimit 1 29).2 2 0 first := by
  refine ⟨by cases runtimeSafety <;> decide, ?_⟩
  exact (initialization_frame (memory runtimeSafety firstCells) 2 1 0 ⟨0, 0⟩ ⟨1, 0⟩ addressLimit 1 29 (by decide)).trans
    (by cases runtimeSafety <;> rfl)

end Compiler.Extraction.RepresentativeArray.DescriptorRelation.Tests
