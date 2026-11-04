/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryRegionAllocation

namespace Compiler.ZigAir.Memory.RegionAllocation

/-- Valid native ranges lie below the reached high-water mark. -/
theorem fits_above (state : State) (layout : Layout) (base : Nat) (valid : state.valid = true)
    (positive : 0 < base) (aligned : base % layout.alignment = 0)
    (bounded : base + layout.bytes ≤ addressLimit) (above : state.nextAddress ≤ base) : Fits state layout base := by
  refine ⟨positive, aligned, bounded, ?_⟩
  intro entry member old shaped
  have found := lookup_of_mem_valid _ _ _ valid member
  obtain ⟨_, _, actual, actualShape, _, highWater, _⟩ := valid_lookup _ _ _ valid found
  have same := Option.some.inj (actualShape.symm.trans shaped)
  subst actual
  exact Or.inr (Nat.le_trans highWater above)

theorem extend_valid (state : State) (type : Ty) (layout : Layout) (base : Nat)
    (valid : state.valid = true) (shaped : type.layout = some layout) (fits : Fits state layout base) :
    (extend state type layout.bytes base).valid = true := by
  simp only [State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid ⊢
  refine ⟨⟨Nat.max_le.mpr ⟨valid.1.1, fits.bounded⟩, ?_⟩, ?_⟩
  · intro entry present
    rcases List.mem_cons.mp present with same | old
    · subst entry
      simp only [cell, shaped, Bool.and_eq_true, decide_eq_true_eq, Cells.empty_valid]
      exact ⟨⟨by simp [extend], fits.positive⟩, ⟨fits.aligned, Nat.le_max_right _ _⟩, trivial⟩
    · obtain ⟨⟨older, positive⟩, checked⟩ := valid.1.2 entry old
      refine ⟨⟨by dsimp [extend]; omega, positive⟩, ?_⟩
      cases oldShape : entry.2.type.layout with
      | none => simp [oldShape] at checked
      | some oldLayout =>
        simp only [oldShape, Bool.and_eq_true, decide_eq_true_eq] at checked ⊢
        exact ⟨⟨checked.1.1, Nat.le_trans checked.1.2 (Nat.le_max_left _ _)⟩, checked.2⟩
  · apply List.pairwise_cons.mpr
    refine ⟨?_, valid.2⟩
    intro entry present
    have checked := valid.1.2 entry present
    have older := checked.1.1
    cases oldShape : entry.2.type.layout with
    | none => simp [oldShape] at checked
    | some oldLayout =>
      simp only [separated, cell, shaped, oldShape, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨by omega, fits.separate entry present oldLayout oldShape⟩

/-- The checked extended heap supplies the same complete region contract used
by allocation preservation. This direction derives admission from an actual
accepted response; callers need not assume a fresh, aligned host address. -/
theorem fits_of_extend_valid (state : State) (type : Ty) (layout : Layout) (base : Nat)
    (shaped : type.layout = some layout)
    (valid : (extend state type layout.bytes base).valid = true) : Fits state layout base := by
  simp only [State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at valid
  have checked := valid.1.2 (state.nextId, cell type base) (List.mem_cons_self)
  simp only [cell, shaped, Bool.and_eq_true, decide_eq_true_eq, Cells.empty_valid] at checked
  refine ⟨checked.1.2, checked.2.1.1, Nat.le_trans checked.2.1.2 valid.1.1, ?_⟩
  intro entry member old oldShape
  have apart := (List.pairwise_cons.mp valid.2).1 entry member
  simp only [separated, cell, shaped, oldShape, Bool.and_eq_true, decide_eq_true_eq] at apart
  exact apart.2

theorem extend_lookup (state : State) (type : Ty) (bytes base id : Nat) :
    (extend state type bytes base).heap.lookup id =
      if state.nextId = id then some (cell type base) else state.heap.lookup id :=
  Heap.lookup_cons _ _ _ _

theorem extend_shape (state : State) (type : Ty) (bytes base : Nat) (valid : state.valid = true) :
    state.heap.RetainsShape (extend state type bytes base).heap := by
  intro id old found
  have older := (valid_lookup state id old valid found).1
  refine ⟨old, ?_, Allocation.SameShape.refl _⟩
  simpa only [extend_lookup, if_neg (by omega : state.nextId ≠ id)] using found

theorem extend_load_other (state : State) (type : Ty) (bytes base : Nat) (writable many : Bool)
    (child : Ty) (address : Address) (apart : address.allocation ≠ state.nextId) :
    load (extend state type bytes base) (.pointer (.pointer writable many child) address) =
      load state (.pointer (.pointer writable many child) address) := by
  apply load_eq_of_lookup
  simp only [extend_lookup, if_neg (Ne.symm apart)]

theorem reserve_empty (state : State) (type : Ty) (layout : Layout)
    (allocate : Allocator σ) (effects : σ) (shaped : type.layout = some layout)
    (empty : layout.bytes = 0) :
    reserve state type allocate effects = ((.ok (some ⟨state.nextId, 0⟩), state), effects) := by
  simp [reserve, shaped, empty]

theorem reserve_overflow (state : State) (type : Ty) (layout : Layout)
    (allocate : Allocator σ) (effects : σ) (valid : state.valid = true)
    (shaped : type.layout = some layout) (overflow : addressLimit ≤ layout.bytes) :
    reserve state type allocate effects = ((.ok none, state), effects) := by
  have positive : layout.bytes ≠ 0 := by intro zero; simp [zero, addressLimit] at overflow
  simp [reserve, shaped, positive, valid, overflow]

theorem reserve_failed (state : State) (type : Ty) (layout : Layout)
    (allocate : Allocator σ) (effects reached : σ) (valid : state.valid = true)
    (shaped : type.layout = some layout) (nonzero : layout.bytes ≠ 0) (size : layout.bytes < addressLimit)
    (response : allocate layout.bytes layout.alignment effects = (none, reached)) :
    reserve state type allocate effects = ((.ok none, state), reached) := by
  simp [reserve, shaped, nonzero, valid, Nat.not_le.mpr size, response]

theorem reserve_admitted (state : State) (type : Ty) (layout : Layout) (base : Nat)
    (allocate : Allocator σ) (effects reached : σ) (valid : state.valid = true)
    (shaped : type.layout = some layout) (nonzero : layout.bytes ≠ 0) (size : layout.bytes < addressLimit)
    (response : allocate layout.bytes layout.alignment effects = (some base, reached)) (fits : Fits state layout base) :
    reserve state type allocate effects = ((.ok (some ⟨state.nextId, 0⟩), extend state type layout.bytes base), reached) := by
  simp [reserve, shaped, nonzero, valid, Nat.not_le.mpr size, response,
    extend_valid state type layout base valid shaped fits]

/-- Every published nonempty allocation comes from the actual external response,
with complete type, fresh lifetime and checked validity. -/
theorem reserve_nonempty_success (state after : State) (type : Ty) (layout : Layout)
    (allocate : Allocator σ) (effects reached : σ) (address : Address)
    (shaped : type.layout = some layout) (nonzero : layout.bytes ≠ 0)
    (done : reserve state type allocate effects = ((.ok (some address), after), reached)) :
    ∃ base, address = ⟨state.nextId, 0⟩ ∧ after = extend state type layout.bytes base ∧
      allocate layout.bytes layout.alignment effects = (some base, reached) ∧ after.valid = true := by
  simp only [reserve, shaped, if_neg nonzero] at done
  split at done
  · simp at done
  · split at done
    · simp at done
    · cases response : allocate layout.bytes layout.alignment effects with
      | mk selected advanced =>
        simp only [response] at done
        cases selected with
        | none => simp at done
        | some base =>
          dsimp only at done
          split at done
          · cases done
            exact ⟨base, rfl, rfl, rfl, by assumption⟩
          · simp at done

theorem reserve_preserves_valid (state : State) (type : Ty) (allocate : Allocator σ) (effects : σ)
    (valid : state.valid = true) : (reserve state type allocate effects).1.2.valid = true := by
  unfold reserve
  cases shaped : type.layout with
  | none => exact valid
  | some layout =>
    dsimp only
    split
    · exact valid
    · split
      · exact valid
      · split
        · exact valid
        · cases response : allocate layout.bytes layout.alignment effects with
          | mk selected reached =>
            dsimp only
            cases selected with
            | none => exact valid
            | some base =>
              dsimp only
              split
              · assumption
              · exact valid

/-- Every outcome preserves each allocation other than the one fresh lifetime.
This includes ordinary OOM and rejected allocator responses with reached effects. -/
theorem reserve_heap_other (state : State) (type : Ty) (allocate : Allocator σ) (effects : σ)
    (id : Nat) (apart : id ≠ state.nextId) :
    (reserve state type allocate effects).1.2.heap.lookup id = state.heap.lookup id := by
  unfold reserve
  cases shaped : type.layout with
  | none => rfl
  | some layout =>
    dsimp only
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · cases response : allocate layout.bytes layout.alignment effects with
          | mk selected reached =>
            dsimp only
            cases selected with
            | none => rfl
            | some base =>
              dsimp only
              split
              · simp only [extend_lookup, if_neg (Ne.symm apart)]
              · rfl

end Compiler.ZigAir.Memory.RegionAllocation
