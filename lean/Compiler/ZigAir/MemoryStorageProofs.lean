/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryStorage

namespace Compiler.ZigAir.Memory

/-- Nominal metadata and complete aggregate views supply no whole-object value.
This rejection is independent of the initialized leaves or view admission. -/
theorem Cells.read_record_unsupported (cells : Cells) (owner : Ty) (offset : Nat) (identity : String) (layout : Layout) :
    cells.read owner offset (.record identity layout) = .error .unsupported := by
  simp only [Cells.read, ite_self]

theorem Cells.read_aggregate_unsupported (cells : Cells) (owner : Ty) (offset : Nat) (identity : String)
    (layout : Layout) (fields : List (Nat × Field)) :
    cells.read owner offset (.aggregate identity layout fields) = .error .unsupported := by
  simp only [Cells.read, ite_self]

theorem Cells.readLeaf_hasType (cells : Cells) (owner : Ty) (offset : Nat) (wanted : Ty) (value : Value)
    (loaded : cells.readLeaf owner offset wanted = .ok value) : value.hasType wanted = true := by
  unfold Cells.readLeaf at loaded
  split at loaded
  · contradiction
  · cases found : cells.lookup offset with
    | none => simp [found] at loaded
    | some actual =>
      simp only [found] at loaded
      split at loaded
      · rename_i typed
        have same : actual = value := Except.ok.inj loaded
        exact same ▸ typed
      · contradiction

theorem Cells.empty_valid (owner : Ty) : Cells.valid [] owner = true := by rfl

theorem Cells.lookup_set (cells : Cells) (offset : Nat) (value : Value) :
    (cells.set offset value).lookup offset = some value := by
  simp [Cells.lookup, Cells.set]

theorem Cells.lookup_set_other (cells : Cells) (offset other : Nat) (value : Value) (different : other ≠ offset) :
    (cells.set offset value).lookup other = cells.lookup other := by
  induction cells with
  | nil => simp [Cells.lookup, Cells.set, Ne.symm different]
  | cons entry tail ih =>
    rcases entry with ⟨key, old⟩
    by_cases selected : key = offset
    · subst key
      simpa [Cells.lookup, Cells.set, Ne.symm different] using ih
    · by_cases found : key = other
      · subst key
        simp [Cells.lookup, Cells.set, different, Ne.symm different]
      · simpa [Cells.lookup, Cells.set, selected, found, Ne.symm different] using ih

theorem Cells.set_preserves_valid (cells : Cells) (owner : Ty) (offset : Nat) (value : Value)
    (initial : cells.valid owner = true) (fits : leafFits owner (offset, value) = true) :
    (cells.set offset value).valid owner = true := by
  simp only [Cells.valid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at initial ⊢
  constructor
  · intro entry present
    rcases List.mem_cons.mp present with same | old
    · simpa only [same] using fits
    · exact initial.1 entry (List.mem_filter.mp old).1
  · apply List.pairwise_cons.mpr
    refine ⟨?_, initial.2.filter _⟩
    intro entry present
    have different : entry.1 ≠ offset := by simpa using (List.mem_filter.mp present).2
    exact Ne.symm different

theorem Cells.fold_preserves_valid (updates cells : Cells) (owner : Ty)
    (initial : cells.valid owner = true) (fits : updates.all (leafFits owner) = true) :
    (updates.foldl (fun cells entry => cells.set entry.1 entry.2) cells).valid owner = true := by
  induction updates generalizing cells with
  | nil => exact initial
  | cons entry tail ih =>
    simp only [List.all_cons, Bool.and_eq_true] at fits
    exact ih (cells.set entry.1 entry.2) (cells.set_preserves_valid owner entry.1 entry.2 initial fits.1) fits.2

theorem Cells.write_preserves_valid (cells : Cells) (owner : Ty) (offset : Nat) (value : Value) (after : Cells)
    (initial : cells.valid owner = true) (success : cells.write owner offset value = .ok after) :
    after.valid owner = true := by
  unfold Cells.write at success
  split at success
  · contradiction
  · split at success
    · contradiction
    · dsimp only at success
      split at success
      · contradiction
      · rename_i accepted
        cases Except.ok.inj success
        exact Cells.fold_preserves_valid _ cells owner initial (by simpa using accepted)

theorem Cells.write_single (cells : Cells) (owner : Ty) (offset : Nat) (value : Value)
    (valid : value.valid = true) (view : acceptsView owner offset value.type = true)
    (fits : leafFits owner (offset, value) = true) (single : value.leaves offset = [(offset, value)]) :
    cells.write owner offset value = .ok (cells.set offset value) := by
  simp [Cells.write, valid, view, single, fits]

theorem Cells.write_success (cells : Cells) (owner : Ty) (offset : Nat) (value : Value) (after : Cells)
    (success : cells.write owner offset value = .ok after) :
    value.valid = true ∧ acceptsView owner offset value.type = true ∧
    (value.leaves offset).all (leafFits owner) = true ∧
    after = (value.leaves offset).foldl (fun cells entry => cells.set entry.1 entry.2) cells := by
  unfold Cells.write at success
  split at success
  · contradiction
  · rename_i valid
    split at success
    · contradiction
    · rename_i view
      dsimp only at success
      split at success
      · contradiction
      · rename_i fits
        exact ⟨by simpa using valid, by simpa using view, by simpa using fits, (Except.ok.inj success).symm⟩

/-- Scalar and pointer writes publish one checked leaf. Slice-field updates
share this readback law while framing the other leaf independently. -/
theorem Cells.readLeaf_after_single_write (cells : Cells) (owner : Ty) (offset : Nat) (value : Value) (after : Cells)
    (success : cells.write owner offset value = .ok after) (single : value.leaves offset = [(offset, value)]) :
    after.readLeaf owner offset value.type = .ok value := by
  obtain ⟨valid, _, fits, same⟩ := cells.write_success owner offset value after success
  rw [single] at fits same
  simp only [List.all_cons, List.all_nil, Bool.and_true, leafFits, Bool.and_eq_true, decide_eq_true_eq] at fits
  simp only [List.foldl_cons, List.foldl_nil] at same
  rw [same]
  simp only [Cells.readLeaf, fits.1, ne_self_iff_false, ↓reduceIte, Cells.lookup_set,
    Value.hasType, decide_true, valid, Bool.true_and]

/-- Every successful admitted write can be read through the same view. This law
also covers initializing previously missing leaves and overwriting aliases. -/
theorem Cells.read_after_write (cells : Cells) (owner : Ty) (offset : Nat) (value : Value) (after : Cells)
    (success : cells.write owner offset value = .ok after) :
    after.read owner offset value.type = .ok value := by
  rcases cells.write_success owner offset value after success with ⟨valid, view, fits, rfl⟩
  cases value with
  | scalar value | optionalScalar _ value | optionalObject _ _ value =>
    simp only [Value.leaves, List.all_cons, List.all_nil, Bool.and_true, leafFits,
      Bool.and_eq_true, decide_eq_true_eq] at fits
    simp only [Value.type] at fits view
    simp [Cells.read, Value.leaves, Value.type, view, Cells.readLeaf, fits.1, Cells.lookup_set, Value.hasType, valid]
  | pointer type address =>
    cases type <;> simp only [Value.valid] at valid
    all_goals try contradiction
    simp only [Value.leaves, List.all_cons, List.all_nil, Bool.and_true, leafFits,
      Bool.and_eq_true, decide_eq_true_eq] at fits
    simp only [Value.type] at fits view
    simp [Cells.read, Value.leaves, Value.type, view, Cells.readLeaf, fits.1, Cells.lookup_set, Value.hasType, Value.valid]
  | slice type address length =>
    cases type <;> simp only [Value.valid] at valid
    all_goals try contradiction
    rename_i writable child
    simp only [Value.leaves, List.all_cons, List.all_nil, Bool.and_true, leafFits,
      Bool.and_eq_true, decide_eq_true_eq] at fits
    have different : offset ≠ offset + 8 := by omega
    have lengthValid : (Scalar.Value.int false 64 length).valid = true := fits.2.2
    simp only [Value.type, Scalar.Value.type] at fits view
    simp [Cells.read, Value.leaves, Value.type, view, Cells.readLeaf, fits.1.1, fits.2.1, usize,
      Cells.lookup_set_other _ _ _ _ different, Cells.lookup_set, Value.hasType, Value.valid,
      Scalar.Value.type, lengthValid, bind, Except.bind]

end Compiler.ZigAir.Memory
