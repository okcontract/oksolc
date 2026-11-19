/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryInvariant

/-! Compositional facts used to establish function-local memory invariants.
Fresh allocation preserves old reads, including faults. No native allocator
refinement or assumption that allocation succeeds is introduced. -/
namespace Compiler.ZigAir.Memory

theorem valid_lookup (state : State) (id : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup id = some cell) :
    id < state.nextId ∧ 0 < cell.base ∧ ∃ layout,
      cell.type.layout = some layout ∧ cell.base % layout.alignment = 0 ∧
      cell.base + layout.bytes ≤ state.nextAddress ∧ state.nextAddress ≤ addressLimit := by
  have present := Heap.lookup_mem state.heap id cell found
  simp only [State.valid, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at initial
  have entry := initial.1.2 (id, cell) present
  rcases entry with ⟨⟨older, positive⟩, shape⟩
  cases shaped : cell.type.layout with
  | none => simp [shaped] at shape
  | some layout =>
    simp only [shaped, Bool.and_eq_true, decide_eq_true_eq] at shape
    exact ⟨older, positive, layout, rfl, shape.1.1, shape.1.2, initial.1.1⟩

/-- A positive declared root of a valid live allocation supplies its complete
access checks. Write permission is independent of shape and initialization. -/
theorem root_access (state : State) (id : Nat) (cell : Allocation) (layout : Layout) (write : Bool)
    (initial : state.valid = true) (found : state.heap.lookup id = some cell)
    (shaped : cell.type.layout = some layout) (positive : 0 < layout.bytes)
    (permitted : write = true → cell.writable = true) :
    access state ⟨id, 0⟩ layout write = .ok cell := by
  obtain ⟨_, basePositive, actual, actualShape, aligned, bounded, limit⟩ := valid_lookup state id cell initial found
  have same : actual = layout := Option.some.inj (actualShape.symm.trans shaped)
  subst actual
  have checks : ¬(cell.base = 0 ∨ cell.base + layout.bytes > addressLimit ∨
      cell.base + 0 ≥ addressLimit ∨ 0 + layout.bytes > layout.bytes ∨
      (cell.base + 0) % layout.alignment ≠ 0) := by
    simp only [Nat.add_zero, Nat.zero_add]
    omega
  cases write <;>
    simp only [access, found, shaped, Bool.false_and, Bool.false_eq_true, ↓reduceIte, if_neg checks]
  simp only [permitted rfl, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte]

theorem allocate_shape (state : State) (child : Ty) (value : Value) (after : State)
    (success : allocate state child = .ok (value, after)) :
    ∃ layout base, child.layout = some layout ∧
      value = .pointer (.pointer true false child) ⟨state.nextId, 0⟩ ∧
      after = ⟨(state.nextId, ⟨base, child, [], true, true⟩) :: state.heap,
        state.nextId + 1, base + layout.bytes⟩ := by
  unfold allocate at success
  split at success
  · contradiction
  · cases shaped : child.layout with
    | none => simp [shaped] at success
    | some layout =>
      simp only [shaped] at success
      split at success
      · contradiction
      · have same := Except.ok.inj success
        cases same
        exact ⟨layout, _, rfl, rfl, rfl⟩

theorem allocate_pointer (state : State) (child : Ty) (value : Value) (after : State)
    (success : allocate state child = .ok (value, after)) :
    value = .pointer (.pointer true false child) ⟨state.nextId, 0⟩ ∧
      after.nextId = state.nextId + 1 := by
  obtain ⟨_, _, _, pointer, rfl⟩ := allocate_shape state child value after success
  exact ⟨pointer, rfl⟩

/-- A valid heap with the same address counter has the same allocation room.
The returned allocation still uses its own heap and fresh lifetime identifier. -/
theorem allocate_at_same_address (state witness : State) (child : Ty)
    (valid : state.valid = true) (witnessValid : witness.valid = true)
    (address : state.nextAddress = witness.nextAddress) (pointer : Value) (after : State)
    (success : allocate witness child = .ok (pointer, after)) :
    ∃ pointer actual, allocate state child = .ok (pointer, actual) ∧ actual.nextAddress = after.nextAddress := by
  simp only [allocate, valid, witnessValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at success ⊢
  rw [address]
  cases shaped : child.layout with
  | none => simp only [shaped] at success; contradiction
  | some layout =>
    simp only [shaped] at success ⊢
    split at success
    · contradiction
    · rename_i allowed
      simp only [if_neg allowed]
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj success)
      exact ⟨_, _, rfl, rfl⟩

/-- Valid heaps with the same allocation cursors agree on allocation failure,
the fresh pointer and both resulting cursors. Existing heap contents need not
agree, and successful allocation is not an assumption. -/
theorem allocate_same_cursors (state other : State) (child : Ty)
    (valid : state.valid = true) (otherValid : other.valid = true)
    (identity : state.nextId = other.nextId) (address : state.nextAddress = other.nextAddress) :
    (allocate state child).map (fun result => (result.1, result.2.nextId, result.2.nextAddress)) =
      (allocate other child).map (fun result => (result.1, result.2.nextId, result.2.nextAddress)) := by
  simp only [allocate, valid, otherValid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [identity, address]
  cases child.layout with
  | none => rfl
  | some layout => dsimp only; split <;> rfl

theorem load_after_allocate (state : State) (child : Ty) (value : Value) (after : State)
    (writable many : Bool) (readType : Ty) (address : Address)
    (success : allocate state child = .ok (value, after))
    (apart : address.allocation ≠ state.nextId) :
    load after (.pointer (.pointer writable many readType) address) =
      load state (.pointer (.pointer writable many readType) address) := by
  obtain ⟨_, _, _, _, rfl⟩ := allocate_shape state child value after success
  apply load_eq_of_lookup
  simp only [Heap.lookup_cons, if_neg (Ne.symm apart)]

theorem store_keeps_counters (state : State) (pointer value : Value) (after : State)
    (success : store state pointer value = .ok after) :
    after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, rfl⟩ := store_success state pointer value after success
  exact ⟨rfl, rfl⟩

theorem store_of_access (state : State) (child : Ty) (address : Address) (layout : Layout)
    (cell : Allocation) (contents : Cells) (value : Value)
    (typed : value.hasType child = true) (shaped : child.layout = some layout)
    (accessed : access state address layout true = .ok cell)
    (written : cell.cells.write cell.type address.offset value = .ok contents) :
    store state (.pointer (.pointer true false child) address) value =
      .ok { state with heap := state.heap.replace address.allocation { cell with cells := contents } } := by
  simp only [store, typed, Bool.not_true, Bool.false_eq_true, ↓reduceIte, shaped,
    accessed, writeCell, written, bind, Except.bind]

/-- A checked readable view admits the corresponding readonly single pointer.
This needs full view access, rather than mere membership of an allocation. -/
theorem pointerCast_readonly_of_load (state : State) (writable many : Bool) (child : Ty)
    (address : Address) (value : Value)
    (read : load state (.pointer (.pointer writable many child) address) = .ok value) :
    pointerCast state (.pointer false false child) (.pointer (.pointer writable many child) address) =
      .ok (.pointer (.pointer false false child) address) := by
  cases shaped : child.layout with
  | none => simp [load, shaped] at read
  | some layout =>
    cases accessed : access state address layout false with
    | error fault => simp [load, shaped, accessed, bind, Except.bind] at read
    | ok cell => simp [pointerCast, pointerCompatible, shaped, accessed, bind, Except.bind]

end Compiler.ZigAir.Memory
