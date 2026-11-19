/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeDescriptorAppend
import Compiler.Extraction.RepresentativeDescriptorTests
import Compiler.Extraction.RepresentativeGrowingAppendTests

namespace Compiler.Extraction.RepresentativeArray.DescriptorRelation.AppendTests
open Compiler.ZigAir.Memory
open Compiler.Algebraic

def third : Storage.Cell := {Tests.second with sequence := 31}
def cells : List Storage.Cell := Tests.nodes ++ [third]
def before (runtimeSafety : Bool) : State := (Tests.before runtimeSafety).memory
def itemOnly : Cells := (64, Expression.Tests.item) :: Tests.allCells
def argumentsWritten : Cells := [(80, .scalar (.int false 64 4)), (72, .pointer (.pointer true true WordArray.word) ⟨1, 0⟩)] ++ itemOnly
def idWritten : Cells := (88, .scalar (.int false 32 2)) :: argumentsWritten
def complete : Cells := (92, .scalar (.int false 32 31)) :: idWritten
def after (runtimeSafety : Bool) (fields : Cells := complete) : State :=
  let owner := {Backing.Relocation.Tests.owner runtimeSafety with
    cells := (Backing.Relocation.Tests.owner runtimeSafety).cells.set 24 (.scalar (.int false 64 3))}
  let heap := ((before runtimeSafety).heap.replace 3 owner).replace 2 (Tests.backing fields)
  {before runtimeSafety with heap}
def request := Backing.Tests.request
def attempt (runtimeSafety : Bool) (argumentsLength : Nat := 4) (id : Int := 2) (sequence : Int := 31) :=
  Append.Execution.ownerRun runtimeSafety (before runtimeSafety) ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩ argumentsLength id sequence (request none) []

def ready (runtimeSafety : Bool) : State := after runtimeSafety Tests.allCells

/-- Expose each reached prefix so deliberately changed control flow is rejected
at its owning step without repeatedly reducing a complete concrete heap. -/
theorem attempt_suffix (runtimeSafety : Bool) (argumentsLength : Nat) (id sequence : Int) :
    attempt runtimeSafety argumentsLength id sequence =
      let (result, finalState) := initializeFieldsReached (ready runtimeSafety) 2 2 ⟨0, 0⟩ ⟨1, 0⟩ argumentsLength id sequence
      match result with
      | .error fault => ((.error fault, finalState), [])
      | .ok () => ((.ok (some ()), finalState), []) := by
  have selected := Owner.root_header_pointer runtimeSafety (before runtimeSafety) 3 (Backing.Relocation.Tests.owner runtimeSafety)
    true (Tests.initial_valid runtimeSafety).memory (by cases runtimeSafety <;> rfl) rfl
  have lengthRead : readField (before runtimeSafety) ⟨3, 16⟩ Append.lengthOffset = .ok (.scalar (.int false 64 2)) := by
    cases runtimeSafety <;> rfl
  have capacityRead : readField (before runtimeSafety) ⟨3, 16⟩ capacityOffset = .ok (.scalar (.int false 64 3)) := by
    cases runtimeSafety <;> rfl
  have ensured := Capacity.ensure_unchanged (before runtimeSafety) ⟨3, 16⟩ 3 3 (request none) [] (by decide) capacityRead (by decide)
  have written : Append.writeLength (before runtimeSafety) ⟨3, 16⟩ 3 = .ok (ready runtimeSafety) := by
    cases runtimeSafety <;> decide +kernel
  have slot : Append.selectNewElement (ready runtimeSafety) ⟨3, 16⟩ 3 = .ok ⟨2, 64⟩ := by
    cases runtimeSafety <;> decide
  simp only [attempt, Append.Execution.ownerRun, Append.Execution.ownerWithCapacity, selected]
  change Append.Execution.run (before runtimeSafety) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 0⟩ argumentsLength id sequence (request none) [] = _
  simp only [Append.Execution.run, Append.Execution.runWithCapacity, lengthRead, show (2 : Int).toNat = 2 from rfl, show (3 : Int).toNat = 3 from rfl, Append.nextLength, Nat.reduceAdd,
    if_neg (by decide : ¬3 ≥ addressLimit), ensured, Append.Execution.assumeCapacity, capacityRead, Append.hasCapacity,
    Nat.le_refl, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte, written, Append.Execution.finish, slot, Nat.reduceDiv] <;> rfl

theorem actual_spare (runtimeSafety : Bool) : attempt runtimeSafety = ((.ok (some ()), after runtimeSafety), []) := by
  rw [attempt_suffix]
  cases runtimeSafety <;> rfl

theorem spare_without_final_premises (runtimeSafety : Bool) : ∃ finalState,
    attempt runtimeSafety = ((.ok (some ()), finalState), []) ∧ Prefix finalState 2 cells ∧
      ∀ id, representativeFields finalState ⟨3, 16⟩ id = .ok ((Storage.representativeProgram.run cells id).map (values id.toNat)) := by
  obtain ⟨finalState, executed, _, _, _, represented, _, _, queries⟩ := spare_append runtimeSafety (before runtimeSafety) 3 2 3
    (Backing.Relocation.Tests.owner runtimeSafety) (Tests.backing Tests.allCells) Tests.nodes third (request none) []
    (Tests.initial_valid runtimeSafety).memory (by cases runtimeSafety <;> rfl) rfl rfl (by cases runtimeSafety <;> rfl) rfl rfl
    (by cases runtimeSafety <;> rfl) (by cases runtimeSafety <;> rfl) (Tests.prefix_from_initialization runtimeSafety)
    (by decide) (by decide) (by decide)
  exact ⟨finalState, executed, represented, queries⟩

theorem spare_derived_queries (runtimeSafety : Bool) : Prefix (after runtimeSafety) 2 cells ∧
    ∀ id, representativeFields (after runtimeSafety) ⟨3, 16⟩ id = .ok ((Storage.representativeProgram.run cells id).map (values id.toNat)) := by
  obtain ⟨finalState, executed, represented, queries⟩ := spare_without_final_premises runtimeSafety
  have same : finalState = after runtimeSafety := congrArg (fun outcome => outcome.1.2) (executed.symm.trans (actual_spare runtimeSafety))
  exact same ▸ ⟨represented, queries⟩

theorem old_rows_survive_all_rejections (runtimeSafety : Bool) (argumentsLength : Nat) (id sequence : Int) :
    Prefix (attempt runtimeSafety argumentsLength id sequence).1.2 2 Tests.nodes :=
  owner_spare_frame runtimeSafety (before runtimeSafety) 3 2 3 (Backing.Relocation.Tests.owner runtimeSafety) Tests.nodes
    ⟨0, 0⟩ ⟨1, 0⟩ argumentsLength id sequence (request none) [] (Tests.initial_valid runtimeSafety).memory
    (by cases runtimeSafety <;> rfl) rfl (by cases runtimeSafety <;> rfl) (by cases runtimeSafety <;> rfl)
    (by decide) (by decide) (by decide) (Tests.prefix_from_initialization runtimeSafety)

theorem malformed_arguments_keep_length_and_item (runtimeSafety : Bool) :
    attempt runtimeSafety addressLimit = ((.error .malformed, after runtimeSafety itemOnly), []) := by
  rw [attempt_suffix]
  cases runtimeSafety <;> rfl
theorem malformed_sequence_keeps_id (runtimeSafety : Bool) :
    attempt runtimeSafety 4 2 (-1) = ((.error .malformed, after runtimeSafety idWritten), []) := by
  rw [attempt_suffix]
  cases runtimeSafety <;> rfl

theorem partial_row_is_not_published (runtimeSafety : Bool) :
    Prefix (after runtimeSafety itemOnly) 2 Tests.nodes ∧ ¬Prefix (after runtimeSafety itemOnly) 2 cells ∧
      representativeFields (after runtimeSafety itemOnly) ⟨3, 16⟩ 2 = .error .uninitialized := by
  have old := old_rows_survive_all_rejections runtimeSafety addressLimit 2 31
  rw [malformed_arguments_keep_length_and_item] at old
  refine ⟨old, ?_, by cases runtimeSafety <;> decide⟩
  intro represented
  have row := represented 2 third rfl
  have rejected : ¬Row (after runtimeSafety itemOnly) 2 2 third := by simp only [Row]; cases runtimeSafety <;> decide
  exact rejected row

theorem full_capacity_does_not_widen_length (runtimeSafety : Bool) :
    representativeFields (after runtimeSafety) ⟨3, 16⟩ 3 = .ok (.error .invalidId) := by
  cases runtimeSafety <;> decide

def emptyOwner (runtimeSafety stack : Bool) : Allocation := Owner.FieldTests.cell runtimeSafety true stack (Growth.Tests.nativeCells runtimeSafety Growth.Tests.emptyCells)
def emptyState (runtimeSafety stack : Bool) : State := Append.Execution.Tests.before runtimeSafety true stack
def firstAfter (runtimeSafety stack : Bool) : State := Append.Execution.Tests.after runtimeSafety stack Tests.firstCells

theorem actual_first (runtimeSafety stack : Bool) :
    Append.Execution.ownerRun runtimeSafety (emptyState runtimeSafety stack) ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩ 4 0 23 (request (some 800)) [] =
      ((.ok (some ()), firstAfter runtimeSafety stack), [(160, 8)]) := by
  have selected := Owner.root_header_pointer runtimeSafety (emptyState runtimeSafety stack) 3 (emptyOwner runtimeSafety stack)
    true (Growth.Tests.initial_valid runtimeSafety stack) rfl rfl
  have lengthRead : readField (emptyState runtimeSafety stack) ⟨3, 16⟩ Append.lengthOffset = .ok (.scalar (.int false 64 0)) := by
    cases runtimeSafety <;> cases stack <;> rfl
  have ensured := Append.Execution.Tests.capacity_prefix runtimeSafety stack
  change Capacity.ensure (emptyState runtimeSafety stack) ⟨3, 16⟩ 1 (request (some 800)) [] = _ at ensured
  simp only [Append.Execution.ownerRun, Append.Execution.ownerWithCapacity, selected]
  change Append.Execution.run (emptyState runtimeSafety stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 0⟩ 4 0 23 (request (some 800)) [] = _
  simp only [Append.Execution.run, Append.Execution.runWithCapacity, lengthRead, Int.toNat_zero, Append.nextLength, Nat.zero_add,
    if_neg (by decide : ¬1 ≥ addressLimit), ensured]
  cases runtimeSafety <;> cases stack <;> rfl

theorem first_without_final_premises (runtimeSafety stack : Bool) : ∃ finalState,
    Append.Execution.ownerRun runtimeSafety (emptyState runtimeSafety stack) ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩ 4 0 23 (request (some 800)) [] =
      ((.ok (some ()), finalState), [(160, 8)]) ∧ Prefix finalState 4 [Tests.first] ∧
      ∀ id, representativeFields finalState ⟨3, 16⟩ id = .ok ((Storage.representativeProgram.run [Tests.first] id).map (values id.toNat)) := by
  obtain ⟨finalState, executed, _, _, _, represented, _, _, queries⟩ := first_append runtimeSafety (emptyState runtimeSafety stack)
    3 (emptyOwner runtimeSafety stack) Growth.Tests.sentinel Tests.first 800 (request (some 800)) [] [(160, 8)]
    (Growth.Tests.initial_valid runtimeSafety stack) rfl rfl rfl (by cases runtimeSafety <;> cases stack <;> rfl)
    (by cases runtimeSafety <;> cases stack <;> rfl) (by decide) rfl (Capacity.Tests.fits runtimeSafety stack) (Growth.Tests.empty_unlocked runtimeSafety true stack)
  exact ⟨finalState, executed, represented, queries⟩

theorem first_derived_queries (runtimeSafety stack : Bool) : Prefix (firstAfter runtimeSafety stack) 4 [Tests.first] ∧
    ∀ id, representativeFields (firstAfter runtimeSafety stack) ⟨3, 16⟩ id =
      .ok ((Storage.representativeProgram.run [Tests.first] id).map (values id.toNat)) := by
  obtain ⟨finalState, executed, represented, queries⟩ := first_without_final_premises runtimeSafety stack
  have same : finalState = firstAfter runtimeSafety stack :=
    congrArg (fun outcome => outcome.1.2) (executed.symm.trans (actual_first runtimeSafety stack))
  exact same ▸ ⟨represented, queries⟩

theorem first_oom_keeps_empty (runtimeSafety stack : Bool) :
    Append.Execution.ownerRun runtimeSafety (emptyState runtimeSafety stack) ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 0⟩ addressLimit (-1) (-1) (request none) [] =
      ((.ok none, emptyState runtimeSafety stack), [(160, 8)]) ∧ Prefix (emptyState runtimeSafety stack) 97 [] := by
  refine ⟨?_, empty _ _⟩
  exact Append.Execution.first_oom runtimeSafety (emptyState runtimeSafety stack) 3 (emptyOwner runtimeSafety stack) Growth.Tests.sentinel
    ⟨0, 0⟩ ⟨1, 0⟩ addressLimit (-1) (-1) (request none) [] [(160, 8)] (Growth.Tests.initial_valid runtimeSafety stack) rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl) rfl
    (Growth.Tests.empty_unlocked runtimeSafety true stack)

theorem empty_arguments_keep_sentinel (runtimeSafety stack : Bool) :
    let cell := {Tests.first with arguments := [], argumentsAddress := 97}
    ∃ finalState, Append.Execution.ownerRun runtimeSafety (emptyState runtimeSafety stack) ⟨3, 0⟩ ⟨0, 0⟩ ⟨97, 0⟩ 0 0 23 (request (some 800)) [] =
      ((.ok (some ()), finalState), [(160, 8)]) ∧ Prefix finalState 4 [cell] := by
  obtain ⟨finalState, executed, _, _, _, represented, _⟩ := first_append runtimeSafety (emptyState runtimeSafety stack)
    3 (emptyOwner runtimeSafety stack) Growth.Tests.sentinel {Tests.first with arguments := [], argumentsAddress := 97}
    800 (request (some 800)) [] [(160, 8)] (Growth.Tests.initial_valid runtimeSafety stack) rfl rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl) (by decide) rfl
    (Capacity.Tests.fits runtimeSafety stack) (Growth.Tests.empty_unlocked runtimeSafety true stack)
  exact ⟨finalState, executed, represented⟩

end Compiler.Extraction.RepresentativeArray.DescriptorRelation.AppendTests
