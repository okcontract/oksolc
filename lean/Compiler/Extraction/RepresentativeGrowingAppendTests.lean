/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeAppendFrame
import Compiler.Extraction.RepresentativeCapacityTests

namespace Compiler.Extraction.RepresentativeArray.Append.Execution.Tests
open Compiler.ZigAir.Memory

def before (runtimeSafety writable stack : Bool) (cells : Cells := Growth.Tests.emptyCells) : State :=
  Growth.Tests.state runtimeSafety writable stack cells
def ready (runtimeSafety stack : Bool) : State :=
  ⟨[(4, ⟨800, Backing.type 5, [], true, false⟩),
    (3, Owner.FieldTests.cell runtimeSafety true stack (Growth.Tests.nativeCells runtimeSafety [(32, .scalar (.int false 64 5)),
      (16, .pointer Publication.pointerType ⟨4, 0⟩), (24, .scalar (.int false 64 0))])),
    (2, RepresentativeArray.Tests.backing), (1, Expression.Tests.argumentsAllocation), (0, Expression.Tests.itemAllocation)], 5, 960⟩
def headerCells : Cells := [(24, .scalar (.int false 64 1)), (32, .scalar (.int false 64 5)), (16, .pointer Publication.pointerType ⟨4, 0⟩)]
def withItem : Cells := [(0, .pointer Expression.itemType ⟨0, 0⟩)]
def withArguments : Cells := [(16, .scalar (.int false 64 2)), (8, .pointer (.pointer true true Expression.idType) ⟨1, 4⟩)] ++ withItem
def withId : Cells := (24, .scalar (.int false 32 0)) :: withArguments
def complete : Cells := (28, .scalar (.int false 32 29)) :: withId
def after (runtimeSafety stack : Bool) (fields : Cells := complete) : State :=
  ⟨[(4, ⟨800, Backing.type 5, fields, true, false⟩), (3, Owner.FieldTests.cell runtimeSafety true stack (Growth.Tests.nativeCells runtimeSafety headerCells)),
    (2, RepresentativeArray.Tests.backing), (1, Expression.Tests.argumentsAllocation), (0, Expression.Tests.itemAllocation)], 5, 960⟩
def request := Backing.Tests.request

theorem capacity_prefix (runtimeSafety stack : Bool) :
    Capacity.ensure (before runtimeSafety true stack) ⟨3, 16⟩ 1 (request (some 800)) [] =
      ((.ok (some ()), ready runtimeSafety stack), [(160, 8)]) := by
  cases runtimeSafety <;> cases stack <;> exact Capacity.Tests.actual_first_growth _ _

/-- Keep the already tested growth prefix explicit so reduction is bounded by
the actual append continuation, without raising Lean work limits. -/
theorem reached_prefix (runtimeSafety stack : Bool) (argumentsLength : Nat) (id sequence : Int) :
    run (before runtimeSafety true stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ argumentsLength id sequence (request (some 800)) [] =
      let (result, finalState) := assumeCapacity (ready runtimeSafety stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ argumentsLength id sequence
      match result with
      | .error fault => ((.error fault, finalState), [(160, 8)])
      | .ok () => ((.ok (some ()), finalState), [(160, 8)]) := by
  have lengthRead : readField (before runtimeSafety true stack) ⟨3, 16⟩ lengthOffset = .ok (.scalar (.int false 64 0)) := by
    cases runtimeSafety <;> cases stack <;> rfl
  simp only [run, runWithCapacity, lengthRead, Int.toNat_zero, nextLength, Nat.zero_add, if_neg (by decide : ¬1 ≥ addressLimit), capacity_prefix] <;> rfl

theorem actual_first_append (runtimeSafety stack : Bool) :
    run (before runtimeSafety true stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request (some 800)) [] =
      ((.ok (some ()), after runtimeSafety stack), [(160, 8)]) := by
  rw [reached_prefix]
  cases runtimeSafety <;> cases stack <;> rfl

theorem actual_owner_first_append (runtimeSafety stack : Bool) :
    ownerRun runtimeSafety (before runtimeSafety true stack) ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request (some 800)) [] =
      ((.ok (some ()), after runtimeSafety stack), [(160, 8)]) := by
  have selected := Owner.root_header_pointer runtimeSafety (before runtimeSafety true stack) 3
    (Owner.FieldTests.cell runtimeSafety true stack (Growth.Tests.nativeCells runtimeSafety Growth.Tests.emptyCells)) true (Growth.Tests.initial_valid runtimeSafety stack) rfl rfl
  simpa only [ownerRun, ownerWithCapacity, selected, run] using actual_first_append runtimeSafety stack

theorem first_without_final_premises (runtimeSafety stack : Bool) :
    ∃ finalState, ownerRun runtimeSafety (before runtimeSafety true stack) ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request (some 800)) [] =
        ((.ok (some ()), finalState), [(160, 8)]) ∧
      finalState.valid = true ∧ (before runtimeSafety true stack).heap.RetainsShape finalState.heap ∧
      readHeader finalState ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 1, .scalar (.int false 64 5)) ∧
      Expression.readFields finalState false ⟨4, 0⟩ = .ok [.pointer Expression.itemType ⟨0, 0⟩,
        .slice Expression.argumentsType ⟨1, 4⟩ 2, .scalar (.int false 32 0), .scalar (.int false 32 29)] ∧
      finalState.nextId = 5 ∧ finalState.nextAddress = max (before runtimeSafety true stack).nextAddress 960 ∧
      (∀ other, other ≠ 3 → other ≠ 4 → finalState.heap.lookup other = (before runtimeSafety true stack).heap.lookup other) :=
  first_verified runtimeSafety (before runtimeSafety true stack) 3 (Owner.FieldTests.cell runtimeSafety true stack (Growth.Tests.nativeCells runtimeSafety Growth.Tests.emptyCells))
    Growth.Tests.sentinel ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 800 (request (some 800)) [] [(160, 8)] (Growth.Tests.initial_valid runtimeSafety stack)
    rfl rfl rfl (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl)
    (by decide) (by decide) (by decide) rfl (Capacity.Tests.fits runtimeSafety stack) (Growth.Tests.empty_unlocked runtimeSafety true stack)

theorem derived_readback (runtimeSafety stack : Bool) :
    (after runtimeSafety stack).valid = true ∧
      readHeader (after runtimeSafety stack) ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 1, .scalar (.int false 64 5)) ∧
      Expression.readFields (after runtimeSafety stack) false ⟨4, 0⟩ = .ok [.pointer Expression.itemType ⟨0, 0⟩,
        .slice Expression.argumentsType ⟨1, 4⟩ 2, .scalar (.int false 32 0), .scalar (.int false 32 29)] := by
  obtain ⟨finalState, executed, valid, _, header, fields, _⟩ := first_without_final_premises runtimeSafety stack
  have same : finalState = after runtimeSafety stack :=
    congrArg (fun result => result.1.2) (executed.symm.trans (actual_owner_first_append runtimeSafety stack))
  exact same ▸ ⟨valid, header, fields⟩

theorem spare_uses_same_run (runtimeSafety stack : Bool) :
    run (Owner.AppendTests.before runtimeSafety true stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29 (request none) [] =
      ((.ok (some ()), Owner.AppendTests.after runtimeSafety stack), []) := by
  try dsimp only
  simp only [run, runWithCapacity, Capacity.ensure, Capacity.prepare, Growth.run, Growth.prepare]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem spare_without_final_premises (runtimeSafety stack : Bool) :
    ∃ finalState, ownerRun runtimeSafety (Owner.AppendTests.before runtimeSafety true stack) ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29 (request none) [] =
      ((.ok (some ()), finalState), []) ∧ finalState.valid = true := by
  obtain ⟨finalState, executed, valid, _⟩ := spare_verified runtimeSafety (Owner.AppendTests.before runtimeSafety true stack) 3 2 3 1
    (Owner.AppendTests.ownerCell runtimeSafety true stack) RepresentativeArray.FieldTests.data ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29 (request none) []
    (Owner.AppendTests.initial_owner_and_spare runtimeSafety stack).1 rfl rfl rfl rfl rfl rfl
    (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨finalState, executed, valid⟩

theorem oom_skips_assignment (runtimeSafety stack : Bool) :
    run (before runtimeSafety true stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ addressLimit (-1) (-1) (request none) [] =
      ((.ok none, before runtimeSafety true stack), [(160, 8)]) := by
  try dsimp only
  simp only [run, runWithCapacity, Capacity.ensure, Capacity.prepare, before, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem derived_owner_oom (runtimeSafety stack : Bool) :
    ownerRun runtimeSafety (before runtimeSafety true stack) ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request none) [] =
      ((.ok none, before runtimeSafety true stack), [(160, 8)]) :=
  first_oom runtimeSafety (before runtimeSafety true stack) 3 (Owner.FieldTests.cell runtimeSafety true stack (Growth.Tests.nativeCells runtimeSafety Growth.Tests.emptyCells))
    Growth.Tests.sentinel ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request none) [] [(160, 8)] (Growth.Tests.initial_valid runtimeSafety stack)
    rfl rfl (by cases runtimeSafety <;> cases stack <;> rfl) (by cases runtimeSafety <;> cases stack <;> rfl) rfl
    (Growth.Tests.empty_unlocked runtimeSafety true stack)

theorem malformed_arguments_keep_length_and_item (runtimeSafety stack : Bool) :
    run (before runtimeSafety true stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ addressLimit 0 29 (request (some 800)) [] =
      ((.error .malformed, after runtimeSafety stack withItem), [(160, 8)]) := by
  rw [reached_prefix]
  cases runtimeSafety <;> cases stack <;> rfl

theorem malformed_id_keeps_arguments (runtimeSafety stack : Bool) :
    run (before runtimeSafety true stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 (-1) 29 (request (some 800)) [] =
      ((.error .malformed, after runtimeSafety stack withArguments), [(160, 8)]) := by
  rw [reached_prefix]
  cases runtimeSafety <;> cases stack <;> rfl

theorem malformed_sequence_keeps_id (runtimeSafety stack : Bool) :
    run (before runtimeSafety true stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 (-1) (request (some 800)) [] =
      ((.error .malformed, after runtimeSafety stack withId), [(160, 8)]) := by
  rw [reached_prefix]
  cases runtimeSafety <;> cases stack <;> rfl

theorem partial_descriptor_is_not_complete (runtimeSafety stack : Bool) :
    readHeader (after runtimeSafety stack withItem) ⟨3, 16⟩ = .ok (.slice itemsType ⟨4, 0⟩ 1, .scalar (.int false 64 5)) ∧
      representativeFields (after runtimeSafety stack withItem) ⟨3, 16⟩ 0 = .error .uninitialized := by
  cases runtimeSafety <;> cases stack <;> decide

theorem length_read_precedes_capacity_oom (runtimeSafety stack : Bool) :
    let state := before runtimeSafety true stack [(32, .scalar (.int false 64 0)), (16, .pointer Publication.pointerType Growth.Tests.sentinel)]
    run state ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request none) [] = ((.error .uninitialized, state), []) := by
  try dsimp only
  simp only [run, runWithCapacity, Capacity.ensure, Capacity.prepare, before, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem missing_pointer_keeps_length_store (runtimeSafety stack : Bool) :
    let state := before runtimeSafety true stack [(32, .scalar (.int false 64 5)), (24, .scalar (.int false 64 0))]
    run state ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request none) [] =
      ((.error .uninitialized, before runtimeSafety true stack [(24, .scalar (.int false 64 1)), (32, .scalar (.int false 64 5))]), []) := by
  try dsimp only
  simp only [run, runWithCapacity, Capacity.ensure, Capacity.prepare, before, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem readonly_length_precedes_pointer_read (runtimeSafety stack : Bool) :
    let state := before runtimeSafety false stack [(32, .scalar (.int false 64 5)), (24, .scalar (.int false 64 0))]
    run state ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request none) [] = ((.error .readOnly, state), []) := by
  try dsimp only
  simp only [run, runWithCapacity, Capacity.ensure, Capacity.prepare, before, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem readonly_growth_retains_reservation (runtimeSafety stack : Bool) :
    run (before runtimeSafety false stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request (some 800)) [] =
      ((.error .readOnly, Capacity.Tests.reserved runtimeSafety false stack), [(160, 8)]) := by
  try dsimp only
  simp only [run, runWithCapacity, Capacity.ensure, Capacity.prepare, before, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem invalid_region_keeps_effects (runtimeSafety stack : Bool) :
    run (before runtimeSafety true stack) ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request (some 0)) [] =
      ((.error .memoryValidity, before runtimeSafety true stack), [(160, 8)]) := by
  try dsimp only
  simp only [run, runWithCapacity, Capacity.ensure, Capacity.prepare, before, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem length_overflow_is_rejection_before_allocator (runtimeSafety stack : Bool) :
    let state := before runtimeSafety true stack [(24, .scalar (.int false 64 (addressLimit - 1)))]
    run state ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 0 29 (request none) [] = ((.error .malformed, state), []) := by
  try dsimp only
  simp only [run, runWithCapacity, Capacity.ensure, Capacity.prepare, before, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem nonempty_growth_remains_unsupported (runtimeSafety stack : Bool) :
    let state := before runtimeSafety true stack [(24, .scalar (.int false 64 3)), (32, .scalar (.int false 64 3)),
      (16, .pointer Publication.pointerType ⟨2, 0⟩)]
    run state ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 3 29 (request none) [] = ((.error .unsupported, state), []) := by
  try dsimp only
  simp only [run, runWithCapacity, Capacity.ensure, Capacity.prepare, before, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem missing_saved_view_precedes_remap (runtimeSafety stack : Bool) :
    let state := before runtimeSafety true stack [(24, .scalar (.int false 64 1)), (32, .scalar (.int false 64 1))]
    run state ⟨3, 16⟩ ⟨0, 0⟩ ⟨1, 4⟩ 2 1 29 (request none) [] = ((.error .uninitialized, state), []) := by
  try dsimp only
  simp only [run, runWithCapacity, Capacity.ensure, Capacity.prepare, before, Growth.run, Growth.prepare, Growth.Tests.fixture_lock]
  cases runtimeSafety <;> cases stack <;> decide +kernel

theorem parent_survives_all_outcomes (runtimeSafety stack : Bool) (argumentsLength : Nat) (id sequence : Int) (base : Option Nat) :
    let finalState := (ownerRun runtimeSafety (before runtimeSafety true stack) ⟨3, 0⟩ ⟨0, 0⟩ ⟨1, 4⟩ argumentsLength id sequence (request base) []).1.2
    finalState.valid = true ∧ finalState.heap.lookup 1 = some Expression.Tests.argumentsAllocation ∧ WordArray.Represents finalState ⟨1, 1, 2⟩ [99, 1] ∧
      (∀ writable many type offset, load finalState (.pointer (.pointer writable many type) ⟨1, offset⟩) =
        load (before runtimeSafety true stack) (.pointer (.pointer writable many type) ⟨1, offset⟩)) :=
  owner_parent_borrow runtimeSafety (before runtimeSafety true stack) 3 (Owner.FieldTests.cell runtimeSafety true stack (Growth.Tests.nativeCells runtimeSafety Growth.Tests.emptyCells))
    ⟨0, 0⟩ ⟨1, 4⟩ argumentsLength id sequence (request base) [] ⟨1, 1, 2⟩ [99, 1] 4 Expression.Tests.argumentsAllocation
    (Growth.Tests.initial_valid runtimeSafety stack) rfl rfl rfl rfl (Growth.Tests.parent_contents runtimeSafety stack)

end Compiler.Extraction.RepresentativeArray.Append.Execution.Tests
