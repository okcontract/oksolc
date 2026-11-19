/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeGrowthStorage
import Compiler.Extraction.RepresentativePublicationTests

namespace Compiler.Extraction.RepresentativeArray.Growth.Tests
open Compiler.ZigAir.Memory

def sentinel : Address := ⟨99, 64⟩
def emptyItemCells : Cells := ((.slice itemsType sentinel 0 : Value).leaves 16).reverse
def emptyCells : Cells := emptyItemCells.set 32 (.scalar (.int false 64 0))
-- The fixture explicitly initializes the captured safety lock. Other owner
-- fields remain unconstrained until their own reached statements initialize them.
def nativeCells (runtimeSafety : Bool) (cells : Cells) : Cells :=
  cells ++ if runtimeSafety then [(40, .scalar (.int false 64 0))] else []
def state (runtimeSafety writable stack : Bool) (cells : Cells := emptyCells) : State :=
  {Owner.FieldTests.before runtimeSafety writable stack with heap :=
    (Owner.FieldTests.before runtimeSafety writable stack).heap.replace 3 (Owner.FieldTests.cell runtimeSafety writable stack (nativeCells runtimeSafety cells))}
def request := Backing.Tests.request
def reserved (runtimeSafety writable stack : Bool) (cells : Cells := emptyCells) : State :=
  RegionAllocation.extend (state runtimeSafety writable stack cells) (Backing.type 3) 96 800
def finalCells : Cells := (emptyCells.set 16 (.pointer Publication.pointerType ⟨4, 0⟩)).set 32 (.scalar (.int false 64 3))
def after (runtimeSafety stack : Bool) : State := {reserved runtimeSafety true stack with
  heap := (reserved runtimeSafety true stack).heap.replace 3 (Owner.FieldTests.cell runtimeSafety true stack (nativeCells runtimeSafety finalCells))}

theorem initial_valid (runtimeSafety stack : Bool) : (state runtimeSafety true stack).valid = true := by
  cases runtimeSafety <;> cases stack <;> decide

theorem initialized_empty_header (runtimeSafety stack : Bool) :
    Owner.initializeHeader runtimeSafety (state runtimeSafety true stack []) ⟨3, 0⟩ sentinel 0 0 =
      .ok (state runtimeSafety true stack) := by
  have selected := Owner.root_header_pointer runtimeSafety (state runtimeSafety true stack []) 3
    (Owner.FieldTests.cell runtimeSafety true stack (nativeCells runtimeSafety [])) true
    (by cases runtimeSafety <;> cases stack <;> decide) rfl rfl
  simp only [Owner.initializeHeader, selected, bind, Except.bind]
  cases runtimeSafety <;> cases stack <;> rfl

theorem fixture_lock (runtimeSafety writable stack : Bool) (cells : Cells) :
    Owner.NativeLock.checkHeader (state runtimeSafety writable stack cells) ⟨3, 16⟩ =
      Owner.NativeLock.checkUnlocked runtimeSafety (state runtimeSafety writable stack cells) ⟨3, 0⟩ :=
  Owner.NativeLock.checkHeader_owner runtimeSafety _ 3
    (Owner.FieldTests.cell runtimeSafety writable stack (nativeCells runtimeSafety cells)) rfl rfl

theorem empty_unlocked (runtimeSafety writable stack : Bool) :
    Owner.NativeLock.checkHeader (state runtimeSafety writable stack) ⟨3, 16⟩ = .ok () := by
  apply Owner.NativeLock.checkHeader_of_cell runtimeSafety _ 3
    (Owner.FieldTests.cell runtimeSafety writable stack (nativeCells runtimeSafety emptyCells))
    (by cases runtimeSafety <;> cases writable <;> cases stack <;> decide) rfl rfl
  intro active
  subst runtimeSafety
  rfl

theorem fits (runtimeSafety stack : Bool) : RegionAllocation.Fits (state runtimeSafety true stack) ⟨96, 8⟩ 800 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  change entry ∈ [(3, Owner.FieldTests.cell runtimeSafety true stack (nativeCells runtimeSafety emptyCells)),
    (2, RepresentativeArray.Tests.backing), (1, Expression.Tests.argumentsAllocation), (0, Expression.Tests.itemAllocation)] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl <;> cases runtimeSafety <;> cases stack <;> cases shaped <;> decide

theorem actual_first_growth (runtimeSafety stack : Bool) :
    run (state runtimeSafety true stack) ⟨3, 16⟩ 3 (request (some 800)) [] =
      ((.ok (some ()), after runtimeSafety stack), [(96, 8)]) := by
  simp only [run, prepare, fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem growth_without_final_premises (runtimeSafety stack : Bool) :
    ∃ finalState, run (state runtimeSafety true stack) ⟨3, 16⟩ 3 (request (some 800)) [] =
        ((.ok (some ()), finalState), [(96, 8)]) ∧
      finalState.valid = true ∧ (state runtimeSafety true stack).heap.RetainsShape finalState.heap ∧
      readHeader finalState ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 0, .scalar (.int false 64 3)) ∧
      finalState.heap.lookup 4 = some ⟨800, Backing.type 3, [], true, false⟩ ∧
      finalState.nextId = 5 ∧ finalState.nextAddress = 896 ∧
      (∀ id, id ≠ 3 → id ≠ 4 → finalState.heap.lookup id = (state runtimeSafety true stack).heap.lookup id) := by
  have checked := run_verified runtimeSafety (state runtimeSafety true stack) 3
    (Owner.FieldTests.cell runtimeSafety true stack (nativeCells runtimeSafety emptyCells)) sentinel 3 800 (request (some 800)) [] [(96, 8)]
    (initial_valid runtimeSafety stack) rfl rfl rfl (by cases runtimeSafety <;> cases stack <;> decide +kernel)
    (by cases runtimeSafety <;> cases stack <;> decide +kernel) (by decide) (by decide) rfl (fits runtimeSafety stack) (empty_unlocked runtimeSafety true stack)
  cases runtimeSafety <;> cases stack <;> exact checked

theorem header_and_backing_from_growth (runtimeSafety stack : Bool) :
    (after runtimeSafety stack).valid = true ∧
      readHeader (after runtimeSafety stack) ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 0, .scalar (.int false 64 3)) ∧
      Expression.readFields (after runtimeSafety stack) false ⟨4, 0⟩ = .error .uninitialized ∧
      representative (after runtimeSafety stack) ⟨3, 16⟩ 0 = .ok (.error .invalidId) := by
  obtain ⟨finalState, executed, valid, _, header, _⟩ := growth_without_final_premises runtimeSafety stack
  have same := (Prod.mk.inj (Prod.mk.inj (executed.symm.trans (actual_first_growth runtimeSafety stack))).1).2
  subst finalState
  exact ⟨valid, header, by cases runtimeSafety <;> cases stack <;> rfl, by cases runtimeSafety <;> cases stack <;> rfl⟩

def missingLength : Cells := emptyCells.filter (fun entry => entry.1 != 24)
def capacityOnly : Cells := [⟨32, .scalar (.int false 64 0)⟩]

theorem allocation_view_does_not_read_length (runtimeSafety : Bool) :
    allocatedSlice (state runtimeSafety true true missingLength) ⟨3, 16⟩ = .ok (.slice itemsType sentinel 0) ∧
      readItems (state runtimeSafety true true missingLength) ⟨3, 16⟩ = .error .uninitialized := by
  cases runtimeSafety <;> constructor <;> rfl

theorem oom_before_length_read (runtimeSafety : Bool) :
    run (state runtimeSafety true true missingLength) ⟨3, 16⟩ 3 (request none) [(4, 4)] =
      ((.ok none, state runtimeSafety true true missingLength), [(4, 4), (96, 8)]) :=
  run_oom _ _ sentinel _ _ _ _ (by cases runtimeSafety <;> decide)
    (by cases runtimeSafety <;> rfl) (by cases runtimeSafety <;> rfl) (by decide) (by decide) rfl
    (by rw [fixture_lock]; cases runtimeSafety <;> decide +kernel)

theorem missing_length_retains_reservation (runtimeSafety : Bool) :
    run (state runtimeSafety true true missingLength) ⟨3, 16⟩ 3 (request (some 800)) [] =
      ((.error .uninitialized, reserved runtimeSafety true true missingLength), [(96, 8)]) := by
  simp only [run, prepare, fixture_lock]
  cases runtimeSafety <;> decide +kernel

theorem readonly_rejection_retains_reservation (runtimeSafety : Bool) :
    run (state runtimeSafety false true) ⟨3, 16⟩ 3 (request (some 800)) [] =
      ((.error .readOnly, reserved runtimeSafety false true), [(96, 8)]) := by
  simp only [run, prepare, fixture_lock]
  cases runtimeSafety <;> decide +kernel

theorem nonempty_length_retains_reservation (runtimeSafety : Bool) :
    let cells := emptyCells.set 24 (.scalar (.int false 64 1))
    run (state runtimeSafety true true cells) ⟨3, 16⟩ 3 (request (some 800)) [] =
      ((.error .unsupported, reserved runtimeSafety true true cells), [(96, 8)]) := by
  dsimp only
  simp only [run, prepare, fixture_lock]
  cases runtimeSafety <;> decide +kernel

theorem zero_skips_pointer_length_and_allocator (runtimeSafety : Bool) :
    run (state runtimeSafety true true capacityOnly) ⟨3, 16⟩ 0 (request (some 800)) [] =
      ((.ok (some ()), state runtimeSafety true true capacityOnly), []) := by
  simp only [run, prepare, fixture_lock]
  cases runtimeSafety <;> decide +kernel

theorem missing_pointer_rejects_before_allocator (runtimeSafety : Bool) :
    run (state runtimeSafety true true capacityOnly) ⟨3, 16⟩ 3 (request none) [] =
      ((.error .uninitialized, state runtimeSafety true true capacityOnly), []) := by
  simp only [run, prepare, fixture_lock]
  cases runtimeSafety <;> decide +kernel

theorem capacity_failure_precedes_allocation (runtimeSafety : Bool) :
    run (state runtimeSafety true true []) ⟨3, 16⟩ 3 (request (some 800)) [] =
      ((.error .uninitialized, state runtimeSafety true true []), []) ∧
    run (state runtimeSafety true true) ⟨3, 17⟩ 3 (request (some 800)) [] =
      ((.error .memoryValidity, state runtimeSafety true true), []) := by
  simp only [run, prepare, fixture_lock]
  cases runtimeSafety <;> constructor <;> decide +kernel

theorem overflow_is_oom_without_callback (runtimeSafety : Bool) :
    run (state runtimeSafety true true) ⟨3, 16⟩ (addressLimit / 32) (request (some 800)) [] =
      ((.ok none, state runtimeSafety true true), []) ∧
    run (state runtimeSafety true true) ⟨3, 16⟩ addressLimit (request (some 800)) [] =
      ((.error .malformed, state runtimeSafety true true), []) := by
  simp only [run, prepare, fixture_lock]
  cases runtimeSafety <;> constructor <;> decide +kernel

theorem rejected_allocator_keeps_effects (runtimeSafety : Bool) :
    run (state runtimeSafety true true) ⟨3, 16⟩ 3 (request (some 0)) [] =
      ((.error .memoryValidity, state runtimeSafety true true), [(96, 8)]) ∧
    run (state runtimeSafety true true) ⟨3, 16⟩ 3 (request (some 608)) [] =
      ((.error .memoryValidity, state runtimeSafety true true), [(96, 8)]) := by
  simp only [run, prepare, fixture_lock]
  cases runtimeSafety <;> constructor <;> decide +kernel

theorem nonempty_growth_is_unsupported (runtimeSafety : Bool) :
    run (state runtimeSafety true true Owner.FieldTests.completedCells) ⟨3, 16⟩ 4 (request none) [] =
      ((.error .unsupported, state runtimeSafety true true Owner.FieldTests.completedCells), []) := by
  simp only [run, prepare, fixture_lock]
  cases runtimeSafety <;> decide +kernel

theorem existing_capacity_skips_allocator (runtimeSafety : Bool) :
    run (state runtimeSafety true true Owner.FieldTests.completedCells) ⟨3, 16⟩ 3 (request none) [] =
      ((.ok (some ()), state runtimeSafety true true Owner.FieldTests.completedCells), []) :=
  run_unchanged _ _ 3 _ _ _ (by decide) (by cases runtimeSafety <;> rfl) (by decide)
    (by rw [fixture_lock]; cases runtimeSafety <;> decide +kernel)

theorem allocated_capacity_includes_uninitialized_spare (runtimeSafety : Bool) :
    allocatedSlice (state runtimeSafety true true Owner.FieldTests.completedCells) ⟨3, 16⟩ = .ok (.slice itemsType ⟨2, 0⟩ 3) ∧
      Expression.readFields (state runtimeSafety true true Owner.FieldTests.completedCells) false ⟨2, 64⟩ = .error .uninitialized := by
  cases runtimeSafety <;> constructor <;> rfl

theorem allocation_view_checks_backing_extent (runtimeSafety : Bool) :
    let cells := Owner.FieldTests.completedCells.set 32 (.scalar (.int false 64 4))
    allocatedSlice (state runtimeSafety true true cells) ⟨3, 16⟩ = .error .memoryValidity ∧
      allocatedSlice (erase (state runtimeSafety true true Owner.FieldTests.completedCells) 2) ⟨3, 16⟩ = .error .unallocated := by
  cases runtimeSafety <;> constructor <;> rfl

theorem parent_contents (runtimeSafety stack : Bool) : WordArray.Represents (state runtimeSafety true stack) ⟨1, 1, 2⟩ [99, 1] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have choice : index = 0 ∨ index = 1 := by simp at inside; omega
  rcases choice with rfl | rfl <;> cases runtimeSafety <;> cases stack <;> rfl

theorem all_outcomes_preserve_parent (runtimeSafety stack : Bool) (base : Option Nat) (capacity : Nat) :
    WordArray.Represents (run (state runtimeSafety true stack) ⟨3, 16⟩ capacity (request base) []).1.2 ⟨1, 1, 2⟩ [99, 1] :=
  run_parent_borrow _ _ _ _ _ _ _ (initial_valid runtimeSafety stack) (by decide) (parent_contents runtimeSafety stack)

/-- Corrupt only the native lock leaf; retain the ordinary header and owner
geometry so lock rejection cannot be masked by another malformed input. -/
def lockState (value : Option Value) : State :=
  { state true true true with
    heap := (state true true true).heap.replace 3
      (Owner.FieldTests.cell true true true (match value with
      | none => emptyCells
      | some value => emptyCells.set 40 value)) }

theorem lock_observations :
    Owner.NativeLock.checkHeader (lockState none) ⟨3, 16⟩ = .error .uninitialized ∧
    Owner.NativeLock.checkHeader (lockState (some (.scalar (.int false 64 1)))) ⟨3, 16⟩ = .error .unsupported ∧
    Owner.NativeLock.checkHeader (lockState (some (.scalar (.int false 64 (addressLimit - 1))))) ⟨3, 16⟩ = .error .unsupported := by
  have select (value : Option Value) : Owner.NativeLock.checkHeader (lockState value) ⟨3, 16⟩ =
      Owner.NativeLock.checkUnlocked true (lockState value) ⟨3, 0⟩ :=
    Owner.NativeLock.checkHeader_owner true (lockState value) 3
    (Owner.FieldTests.cell true true true (match value with | none => emptyCells | some value => emptyCells.set 40 value)) rfl rfl
  simp only [select]
  decide +kernel

theorem lock_failure_precedes_capacity_and_allocator (capacity : Nat) :
    run (lockState none) ⟨3, 16⟩ capacity (request (some 800)) [] =
      ((.error .uninitialized, lockState none), []) ∧
    run (lockState (some (.scalar (.int false 64 1)))) ⟨3, 16⟩ capacity (request (some 800)) [] =
      ((.error .unsupported, lockState (some (.scalar (.int false 64 1)))), []) :=
  ⟨lock_rejected _ _ _ _ _ _ lock_observations.1, lock_rejected _ _ _ _ _ _ lock_observations.2.1⟩

end Compiler.Extraction.RepresentativeArray.Growth.Tests
