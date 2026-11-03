/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayCapacity
import Compiler.Extraction.RepresentativeOwnerAppendTests

namespace Compiler.Extraction.RepresentativeArray.Capacity.Tests
open Compiler.ZigAir.Memory

def state (runtimeSafety writable stack : Bool) (cells : Cells := Growth.Tests.emptyCells) : State :=
  Growth.Tests.state runtimeSafety writable stack cells
def request := Backing.Tests.request
def reserved (runtimeSafety writable stack : Bool) : State :=
  RegionAllocation.extend (state runtimeSafety writable stack) (Backing.type 5) 160 800
def finalCells : Cells := (Growth.Tests.emptyCells.set 16 (.pointer Publication.pointerType ⟨4, 0⟩)).set 32 (.scalar (.int false 64 5))
def after (runtimeSafety stack : Bool) : State := {reserved runtimeSafety true stack with
  heap := (reserved runtimeSafety true stack).heap.replace 3 (Owner.FieldTests.cell runtimeSafety true stack (Growth.Tests.nativeCells runtimeSafety finalCells))}

theorem arithmetic_boundaries : grow 0 = 4 ∧ grow 1 = 5 ∧ grow 2 = 7 ∧ grow 3 = 8 ∧ grow 8 = 16 ∧
    grow (addressLimit / 2 - 1) = 13835058055282163714 ∧
    grow (addressLimit - 2) = addressLimit - 1 ∧ grow (addressLimit - 1) = addressLimit - 1 := by decide

theorem fits (runtimeSafety stack : Bool) : RegionAllocation.Fits (state runtimeSafety true stack) ⟨160, 8⟩ 800 := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  intro entry present layout shaped
  change entry ∈ [(3, Owner.FieldTests.cell runtimeSafety true stack (Growth.Tests.nativeCells runtimeSafety Growth.Tests.emptyCells)),
    (2, RepresentativeArray.Tests.backing), (1, Expression.Tests.argumentsAllocation), (0, Expression.Tests.itemAllocation)] at present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl <;> cases runtimeSafety <;> cases stack <;> cases shaped <;> decide

theorem actual_first_growth (runtimeSafety stack : Bool) :
    ensure (state runtimeSafety true stack) ⟨3, 16⟩ 1 (request (some 800)) [] =
      ((.ok (some ()), after runtimeSafety stack), [(160, 8)]) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem derived_first_growth (runtimeSafety stack : Bool) :
    ∃ finalState, ensure (state runtimeSafety true stack) ⟨3, 16⟩ 1 (request (some 800)) [] =
        ((.ok (some ()), finalState), [(160, 8)]) ∧
      finalState.valid = true ∧ (state runtimeSafety true stack).heap.RetainsShape finalState.heap ∧
      readHeader finalState ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 0, .scalar (.int false 64 5)) ∧
      finalState.heap.lookup 4 = some ⟨800, Backing.type 5, [], true, false⟩ ∧
      finalState.nextId = 5 ∧ finalState.nextAddress = max (state runtimeSafety true stack).nextAddress 960 ∧
      (∀ id, id ≠ 3 → id ≠ 4 → finalState.heap.lookup id = (state runtimeSafety true stack).heap.lookup id) :=
  first_verified runtimeSafety (state runtimeSafety true stack) 3
    (Owner.FieldTests.cell runtimeSafety true stack (Growth.Tests.nativeCells runtimeSafety Growth.Tests.emptyCells)) Growth.Tests.sentinel 1 800
    (request (some 800)) [] [(160, 8)] (Growth.Tests.initial_valid runtimeSafety stack) rfl rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl)
    (by decide) (by decide) (by decide) rfl (fits runtimeSafety stack) (Growth.Tests.empty_unlocked runtimeSafety true stack)

theorem derived_header_and_storage (runtimeSafety stack : Bool) :
    (after runtimeSafety stack).valid = true ∧
      readHeader (after runtimeSafety stack) ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 0, .scalar (.int false 64 5)) ∧
      (after runtimeSafety stack).heap.lookup 4 = some ⟨800, Backing.type 5, [], true, false⟩ := by
  obtain ⟨finalState, executed, valid, _, header, backing, _⟩ := derived_first_growth runtimeSafety stack
  have same : finalState = after runtimeSafety stack := by
    have equality := executed.symm.trans (actual_first_growth runtimeSafety stack)
    exact congrArg (fun result => result.1.2) equality
  exact same ▸ ⟨valid, header, backing⟩

theorem zero_skips_other_fields_and_allocator (runtimeSafety stack : Bool) :
    let before := state runtimeSafety false stack [(32, .scalar (.int false 64 0))]
    ensure before ⟨3, 16⟩ 0 (request (some 800)) [] = ((.ok (some ()), before), []) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem equality_skips_growth_policy (runtimeSafety stack : Bool) :
    let before := state runtimeSafety false stack [(32, .scalar (.int false 64 1))]
    ensure before ⟨3, 16⟩ 1 (request (some 800)) [] = ((.ok (some ()), before), []) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem oom_uses_selected_capacity (runtimeSafety stack : Bool) :
    ensure (state runtimeSafety true stack) ⟨3, 16⟩ 1 (request none) [] =
      ((.ok none, state runtimeSafety true stack), [(160, 8)]) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem oom_precedes_length_read (runtimeSafety stack : Bool) :
    let before := state runtimeSafety false stack
      [(16, .pointer Publication.pointerType Growth.Tests.sentinel), (32, .scalar (.int false 64 0))]
    ensure before ⟨3, 16⟩ 1 (request none) [] = ((.ok none, before), [(160, 8)]) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem saturation_byte_overflow_is_oom (runtimeSafety stack : Bool) :
    ensure (state runtimeSafety true stack) ⟨3, 16⟩ (addressLimit - 1) (request (some 800)) [] =
      ((.ok none, state runtimeSafety true stack), []) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem invalid_usize_is_not_oom (runtimeSafety stack : Bool) :
    ensure (state runtimeSafety true stack) ⟨99, 0⟩ addressLimit (request none) [] =
      ((.error .malformed, state runtimeSafety true stack), []) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem capacity_fault_precedes_allocation (runtimeSafety stack : Bool) :
    let before := state runtimeSafety true stack []
    ensure before ⟨3, 16⟩ 1 (request (some 800)) [] = ((.error .uninitialized, before), []) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem unsupported_nonempty_growth_retains_state (runtimeSafety stack : Bool) :
    let before := state runtimeSafety true stack [(32, .scalar (.int false 64 3)), (16, .pointer Publication.pointerType ⟨2, 0⟩)]
    ensure before ⟨3, 16⟩ 4 (request (some 800)) [] = ((.error .unsupported, before), []) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem saved_view_fault_precedes_remap (runtimeSafety stack : Bool) :
    let before := state runtimeSafety true stack [(32, .scalar (.int false 64 1))]
    ensure before ⟨3, 16⟩ 2 (request (some 800)) [] = ((.error .uninitialized, before), []) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem readonly_rejection_retains_reservation (runtimeSafety stack : Bool) :
    ensure (state runtimeSafety false stack) ⟨3, 16⟩ 1 (request (some 800)) [] =
      ((.error .readOnly, reserved runtimeSafety false stack), [(160, 8)]) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem invalid_region_retains_effects (runtimeSafety stack : Bool) :
    ensure (state runtimeSafety true stack) ⟨3, 16⟩ 1 (request (some 0)) [] =
      ((.error .memoryValidity, state runtimeSafety true stack), [(160, 8)]) := by
  try dsimp only
  simp only [ensure, prepare, state, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem parent_survives_all_outcomes (runtimeSafety stack : Bool) (minimum : Nat) (base : Option Nat) :
    WordArray.Represents (ensure (state runtimeSafety true stack) ⟨3, 16⟩ minimum (request base) []).1.2
      ⟨1, 1, 2⟩ [99, 1] :=
  ensure_parent_borrow (state runtimeSafety true stack) ⟨3, 16⟩ minimum (request base) [] ⟨1, 1, 2⟩ [99, 1]
    (Growth.Tests.initial_valid runtimeSafety stack) (by decide) (Growth.Tests.parent_contents runtimeSafety stack)

/-- The outer unchanged branch precedes precise growth and its lock assertion. -/
theorem spare_capacity_skips_lock :
    ensure (Growth.Tests.lockState none) ⟨3, 16⟩ 0 (request (some 800)) [] =
      ((.ok (some ()), Growth.Tests.lockState none), []) :=
  ensure_unchanged _ _ 0 0 _ _ (by decide) (by decide +kernel) (by decide)

end Compiler.Extraction.RepresentativeArray.Capacity.Tests
