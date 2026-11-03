/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeCapacityProgram
import Compiler.Extraction.RepresentativeAppendProgram
import Compiler.Extraction.RepresentativeGrowthStorage

namespace Compiler.Extraction.RepresentativeArray.Capacity
open Compiler.ZigAir.Memory

theorem initial_capacity_checked : initialCapacity = 4 := by decide

/-- Zig's inner ordinary addition cannot overflow for an admitted usize.
Only the outer addition in growCapacity is saturating. -/
theorem inner_sum_bounded (minimum : Nat) (width : minimum < addressLimit) :
    minimum / 2 + initialCapacity < addressLimit := by
  rw [initial_capacity_checked]
  change minimum < 18446744073709551616 at width
  change minimum / 2 + 4 < 18446744073709551616
  omega

theorem grow_bounded (minimum : Nat) : grow minimum < addressLimit := by
  have bound := Nat.min_le_left (addressLimit - 1) (minimum + (minimum / 2 + initialCapacity))
  have positive : 0 < addressLimit := by decide
  unfold grow
  omega

theorem grow_sufficient (minimum : Nat) (width : minimum < addressLimit) : minimum ≤ grow minimum := by
  unfold grow
  omega

theorem grow_positive (minimum : Nat) (width : minimum < addressLimit) (positive : 0 < minimum) :
    0 < grow minimum := by
  have enough := grow_sufficient minimum width
  omega

theorem first_capacity_checked : grow 1 = 5 := by decide

/-- Source-selected target capacity. The current header is read before growth
policy arithmetic; an unchanged capacity skips all later growth operations. -/
def prepare (state : State) (header : Address) (minimum : Nat) : Except Fault (Option Nat) :=
  if minimum ≥ addressLimit then .error .malformed else
  match readField state header capacityOffset with
  | .error fault => .error fault
  | .ok (.scalar (.int false 64 capacity)) =>
    if Append.hasCapacity capacity.toNat minimum then .ok none else .ok (some (grow minimum))
  | .ok _ => .error .malformed

theorem prepare_selected (state : State) (header : Address) (minimum capacity : Nat)
    (selected : prepare state header minimum = .ok (some capacity)) : capacity = grow minimum := by
  unfold prepare at selected
  split at selected
  · cases selected
  · split at selected
    · cases selected
    · split at selected
      · cases selected
      · exact (Option.some.inj (Except.ok.inj selected)).symm
    · cases selected

/-- The first-allocation facade uses the same source-selected target. Every
ordinary outcome or checked rejection retains the reached state and effects. -/
def ensure (state : State) (header : Address) (minimum : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) :
    (Except Fault (Option Unit) × State) × σ :=
  match prepare state header minimum with
  | .error fault => ((.error fault, state), effects)
  | .ok none => ((.ok (some ()), state), effects)
  | .ok (some capacity) => Growth.run state header capacity allocate effects

theorem ensure_unchanged (state : State) (header : Address) (capacity minimum : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (width : minimum < addressLimit)
    (loaded : readField state header capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (enough : minimum ≤ capacity) :
    ensure state header minimum allocate effects = ((.ok (some ()), state), effects) := by
  simp only [ensure, prepare, if_neg (Nat.not_le.mpr width), loaded, Int.toNat_natCast, Append.hasCapacity,
    decide_eq_true_eq, if_pos enough]

theorem ensure_growing (state : State) (header : Address) (capacity minimum : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (width : minimum < addressLimit)
    (loaded : readField state header capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (short : capacity < minimum) :
    ensure state header minimum allocate effects = Growth.run state header (grow minimum) allocate effects := by
  simp only [ensure, prepare, if_neg (Nat.not_le.mpr width), loaded, Int.toNat_natCast, Append.hasCapacity,
    decide_eq_true_eq, if_neg (Nat.not_le.mpr short)]

/-- First growth now derives its allocation request from minimum capacity.
The actual allocator response and initial captured owner derive the fresh
uninitialized backing and final header, without a supplied growth result. -/
theorem first_verified (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (sentinel : Address) (minimum base : Nat) (allocate : RegionAllocation.Allocator σ) (effects reached : σ)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) (writable : cell.writable = true)
    (items : readItems state (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType sentinel 0))
    (oldCapacity : readField state (Owner.headerAddress ⟨lifetime, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (width : minimum < addressLimit) (positive : 0 < minimum) (size : grow minimum * 32 < addressLimit)
    (response : allocate (grow minimum * 32) 8 effects = (some base, reached))
    (fits : RegionAllocation.Fits state ⟨grow minimum * 32, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader state (Owner.headerAddress ⟨lifetime, 0⟩) = .ok ()) :
    ∃ after, ensure state (Owner.headerAddress ⟨lifetime, 0⟩) minimum allocate effects = ((.ok (some ()), after), reached) ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after (Owner.headerAddress ⟨lifetime, 0⟩) =
        .ok (.slice itemsType ⟨state.nextId, 0⟩ 0, .scalar (.int false 64 (grow minimum))) ∧
      after.heap.lookup state.nextId = some ⟨base, Backing.type (grow minimum), [], true, false⟩ ∧
      after.nextId = state.nextId + 1 ∧ after.nextAddress = max state.nextAddress (base + grow minimum * 32) ∧
      (∀ id, id ≠ lifetime → id ≠ state.nextId → after.heap.lookup id = state.heap.lookup id) := by
  rw [ensure_growing state _ 0 minimum allocate effects width oldCapacity positive]
  exact Growth.run_verified runtimeSafety state lifetime cell sentinel (grow minimum) base allocate effects reached
    initial found typed writable items oldCapacity (grow_positive minimum width positive) size response fits unlocked

theorem first_oom (state : State) (header sentinel : Address) (minimum : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects reached : σ) (initial : state.valid = true)
    (pointer : readItemsData state header = .ok (.pointer Publication.pointerType sentinel))
    (oldCapacity : readField state header capacityOffset = .ok (.scalar (.int false 64 0)))
    (width : minimum < addressLimit) (positive : 0 < minimum) (size : grow minimum * 32 < addressLimit)
    (response : allocate (grow minimum * 32) 8 effects = (none, reached))
    (unlocked : Owner.NativeLock.checkHeader state header = .ok ()) :
    ensure state header minimum allocate effects = ((.ok none, state), reached) := by
  rw [ensure_growing state header 0 minimum allocate effects width oldCapacity positive]
  exact Growth.run_oom state header sentinel (grow minimum) allocate effects reached initial pointer oldCapacity
    (grow_positive minimum width positive) size response unlocked

theorem ensure_storage (state : State) (header : Address) (minimum : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (initial : state.valid = true) :
    (ensure state header minimum allocate effects).1.2.valid = true ∧
      (∀ id, id ≠ header.allocation → id ≠ state.nextId →
        (ensure state header minimum allocate effects).1.2.heap.lookup id = state.heap.lookup id) := by
  unfold ensure
  cases prepare state header minimum with
  | error fault => exact ⟨initial, fun _ _ _ => rfl⟩
  | ok selected => cases selected with
    | none => exact ⟨initial, fun _ _ _ => rfl⟩
    | some capacity => exact Growth.run_storage state header capacity allocate effects initial

theorem ensure_parent_borrow (state : State) (header : Address) (minimum : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (parent : WordArray.View)
    (items : List (BitVec 32)) (initial : state.valid = true)
    (separate : parent.allocation ≠ header.allocation) (represented : WordArray.Represents state parent items) :
    WordArray.Represents (ensure state header minimum allocate effects).1.2 parent items := by
  refine ⟨represented.1, ?_⟩
  intro index inside
  have nonempty : items ≠ [] := by intro empty; simp [empty] at inside
  have older := WordAllocation.source_older state parent items initial represented nonempty
  have frame := (ensure_storage state header minimum allocate effects initial).2 parent.allocation separate (by omega)
  exact (load_eq_of_lookup state _ true false WordArray.word (parent.address index) frame).trans (represented.2 index inside)

end Compiler.Extraction.RepresentativeArray.Capacity
