/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAllocationLaws
import Compiler.ZigAir.MemoryHeapFrame

namespace Compiler.ZigAir.Memory

/-- Every admitted value can initialize its own root object. There are no
whole-array values or manufactured defaults in this storage vocabulary. -/
theorem Cells.write_root (cells : Cells) (value : Value) (valid : value.valid = true) :
    ∃ contents, cells.write value.type 0 value = .ok contents := by
  cases value with
  | scalar value | optionalScalar _ value | optionalObject _ _ value =>
    refine ⟨_, Cells.write_single _ _ _ _ valid ?_ ?_ rfl⟩
    · simp [acceptsView, Value.type]
    · simpa [leafFits, leafType, Value.type] using valid
  | pointer ty address =>
    cases ty <;> simp only [Value.valid, Bool.false_eq_true] at valid
    next writable many child =>
      refine ⟨cells.set 0 _, Cells.write_single _ _ _ _ rfl ?_ ?_ rfl⟩
      · simp [acceptsView, Value.type]
      · simp [leafFits, leafType, Value.type, Value.valid]
  | slice ty address length =>
    cases ty <;> simp only [Value.valid, Bool.false_eq_true] at valid
    next writable child =>
      have width : length < addressLimit := by simpa [addressLimit] using valid
      simp [Cells.write, Value.type, Value.valid, Value.leaves, acceptsView, leafFits, leafType,
        usize, Scalar.Value.type, Scalar.Value.valid, Scalar.Ty.contains, Scalar.Ty.lower, Scalar.Ty.upper, addressLimit] at *
      split
      · omega
      · split
        · omega
        · exact ⟨_, rfl⟩

/-- A live writable root can be initialized or overwritten with any admitted
value of its exact type. Initialization and subsequent counter updates share
the same checked access argument. -/
theorem root_store_total (state : State) (id : Nat) (cell : Allocation) (value : Value) (layout : Layout)
    (initial : state.valid = true) (found : state.heap.lookup id = some cell)
    (typed : cell.type = value.type) (writable : cell.writable = true)
    (valid : value.valid = true) (shaped : value.type.layout = some layout) (positive : 0 < layout.bytes) :
    ∃ after, store state (.pointer (.pointer true false value.type) ⟨id, 0⟩) value = .ok after := by
  obtain ⟨_, positiveBase, checkedLayout, checkedShape, aligned, bounded, limit⟩ :=
    valid_lookup state id cell initial found
  rw [typed] at checkedShape
  have same : checkedLayout = layout := Option.some.inj (checkedShape.symm.trans shaped)
  subst checkedLayout
  have checks : ¬(cell.base = 0 ∨ cell.base + layout.bytes > addressLimit ∨ cell.base + 0 ≥ addressLimit ∨
      0 + layout.bytes > layout.bytes ∨ (cell.base + 0) % layout.alignment ≠ 0) := by
    simp only [Nat.add_zero, Nat.zero_add]
    omega
  have accessed : access state ⟨id, 0⟩ layout true = .ok cell := by
    simp only [access, found, typed, shaped, writable, Bool.not_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, if_neg checks]
  obtain ⟨contents, written⟩ := Cells.write_root cell.cells value valid
  exact ⟨_, store_of_access state value.type ⟨id, 0⟩ layout cell contents value
    (by simpa [Value.hasType] using valid) shaped accessed (by simpa only [typed] using written)⟩

theorem fresh_store_total (state allocated : State) (value pointer : Value) (layout : Layout)
    (valid : value.valid = true) (shaped : value.type.layout = some layout) (positive : 0 < layout.bytes)
    (allocation : allocate state value.type = .ok (pointer, allocated)) :
    ∃ after, store allocated pointer value = .ok after := by
  have heapValid := allocate_preserves_valid state value.type pointer allocated allocation
  obtain ⟨_, base, _, pointerShape, stateShape⟩ := allocate_shape state value.type pointer allocated allocation
  have found : allocated.heap.lookup state.nextId = some ⟨base, value.type, [], true, true⟩ := by
    rw [stateShape]; simp [Heap.lookup_cons]
  rw [pointerShape]
  exact root_store_total allocated state.nextId _ value layout heapValid found rfl rfl valid shaped positive

theorem allocate_fault_of_layout (state : State) (child : Ty) (layout : Layout) (fault : Fault)
    (initial : state.valid = true) (shaped : child.layout = some layout)
    (failed : allocate state child = .error fault) : fault = .outOfMemory := by
  simp only [allocate, initial, Bool.not_true, Bool.false_eq_true, ↓reduceIte, shaped] at failed
  split at failed
  · exact (Except.error.inj failed).symm
  · contradiction

end Compiler.ZigAir.Memory
