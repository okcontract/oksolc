/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAir
import Compiler.ZigAir.MemoryStorageProofs

namespace Compiler.ZigAir.Memory

theorem bounded_slice_iff (start finish bound : Nat) :
    checkSliceBounds start finish (some bound) = .ok () ↔ start ≤ finish ∧ finish ≤ bound := by
  simp [checkSliceBounds]

theorem unbounded_slice_iff (start finish : Nat) :
    checkSliceBounds start finish none = .ok () ↔ start ≤ finish := by
  simp [checkSliceBounds]

theorem larger_allocation_does_not_relax_view (start finish view extent : Nat)
    (_insideAllocation : finish ≤ extent) (outsideView : view < finish) :
    checkSliceBounds start finish (some view) = .error .sourceBounds := by
  simp [checkSliceBounds, Nat.not_le.mpr outsideView]

theorem access_success_region (state : State) (address : Address) (layout : Layout) (write : Bool)
    (allocation : Allocation) (success : access state address layout write = .ok allocation) :
    state.heap.lookup address.allocation = some allocation ∧ ∃ region,
      allocation.type.layout = some region ∧ 0 < allocation.base ∧
      allocation.base + region.bytes ≤ addressLimit ∧ allocation.base + address.offset < addressLimit ∧
      address.offset + layout.bytes ≤ region.bytes ∧
      (allocation.base + address.offset) % layout.alignment = 0 ∧
      (write = true → allocation.writable = true) := by
  cases found : state.heap.lookup address.allocation with
  | none => simp [access, found] at success
  | some cell =>
    cases shaped : cell.type.layout with
    | none => simp [access, found, shaped] at success
    | some region =>
      by_cases denied : write = true ∧ cell.writable = false
      · simp [access, found, shaped, denied] at success
      · by_cases invalid : cell.base = 0 ∨ cell.base + region.bytes > addressLimit ∨
            cell.base + address.offset ≥ addressLimit ∨ address.offset + layout.bytes > region.bytes ∨
            (cell.base + address.offset) % layout.alignment ≠ 0
        · simp [access, found, shaped, denied, invalid] at success
        · have same : cell = allocation := by simpa [access, found, shaped, denied, invalid] using success
          subst allocation
          refine ⟨rfl, region, shaped, ?_⟩
          have permitted : write = true → cell.writable = true := by
            intro yes
            cases h : cell.writable with
            | false => exact False.elim (denied ⟨yes, h⟩)
            | true => rfl
          exact ⟨by omega, by omega, by omega, by omega, by omega, permitted⟩

theorem Heap.lookup_cons (key id : Nat) (value : Allocation) (tail : Heap) :
    Heap.lookup ((key, value) :: tail) id = if key = id then some value else tail.lookup id := by
  by_cases h : key = id <;> simp [Heap.lookup, h]

theorem Heap.lookup_mem (heap : Heap) (id : Nat) (cell : Allocation)
    (found : heap.lookup id = some cell) : (id, cell) ∈ heap := by
  unfold Heap.lookup at found
  cases entry : heap.find? (fun item => item.1 == id) with
  | none => simp [entry] at found
  | some item =>
    have selected : item.1 = id := by simpa using List.find?_some entry
    have present := List.mem_of_find?_eq_some entry
    simp only [entry, Option.map_some, Option.some.injEq] at found
    simpa only [← selected, ← found] using present

theorem Heap.replace_cons (key id : Nat) (value cell : Allocation) (tail : Heap) :
    Heap.replace ((key, value) :: tail) id cell =
      (if key = id then (id, cell) else (key, value)) :: tail.replace id cell := by rfl

theorem replace_other (heap : Heap) (id other : Nat) (cell : Allocation) (different : other ≠ id) :
    (heap.replace id cell).lookup other = heap.lookup other := by
  induction heap with
  | nil => rfl
  | cons head tail ih =>
    rcases head with ⟨key, value⟩
    by_cases selected : key = id
    · subst key
      simp only [Heap.replace_cons, ite_true, Heap.lookup_cons, if_neg (Ne.symm different)]
      exact ih
    · simp only [Heap.replace_cons, if_neg selected, Heap.lookup_cons]
      split
      · rfl
      · exact ih

theorem cleanup_keeps_counters (mark : Nat) (state : State) :
    (cleanup mark state).nextId = state.nextId ∧ (cleanup mark state).nextAddress = state.nextAddress := by
  exact ⟨rfl, rfl⟩

theorem Value.usize_valid (number : Nat) (bounded : number < addressLimit) :
    (Value.scalar (.int false 64 number)).valid = true := by
  simp only [addressLimit, Nat.reducePow] at bounded
  have numberInt : (number : Int) < 18446744073709551616 := by omega
  simp [Value.valid, Scalar.Value.valid, Scalar.Ty.contains, Scalar.Ty.lower, Scalar.Ty.upper, numberInt]

theorem length_write_preserves_pointer (base : Nat) (writable : Bool) (child : Ty) (address : Address)
    (before after : Nat) (afterBound : after < addressLimit) :
    writeCell ⟨base, .slice writable child, (Value.slice (.slice writable child) address before).leaves, true, false⟩
      8 (.scalar (.int false 64 after)) =
      .ok ⟨base, .slice writable child, [(8, .scalar (.int false 64 after)), (0, .pointer (.pointer writable true child) address)], true, false⟩ := by
  have validAfter := Value.usize_valid after afterBound
  have view : acceptsView (.slice writable child) 8 (Value.scalar (.int false 64 after)).type = true := by rfl
  have fits : leafFits (.slice writable child) (8, .scalar (.int false 64 after)) = true := by
    simp only [leafFits, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨rfl, validAfter⟩
  have written := Cells.write_single (Value.slice (.slice writable child) address before).leaves
    (.slice writable child) 8 (.scalar (.int false 64 after)) validAfter view fits rfl
  rw [writeCell, written]
  rfl

theorem length_read_observes_view (base : Nat) (writable : Bool) (child : Ty) (address : Address)
    (length : Nat) (bounded : length < addressLimit) :
    readCell ⟨base, .slice writable child, (Value.slice (.slice writable child) address length).leaves, true, false⟩
      8 usize = .ok (.scalar (.int false 64 length)) := by
  have lengthInt : (length : Int) < 18446744073709551616 := by
    simp only [addressLimit, Nat.reducePow] at bounded
    omega
  simp [readCell, Cells.read, Cells.readLeaf, Cells.lookup, Value.leaves, leafType, acceptsView,
    Value.hasType, Value.valid, Value.type, usize, Scalar.Value.type, Scalar.Value.valid,
    Scalar.Ty.contains, Scalar.Ty.lower, Scalar.Ty.upper, lengthInt]

end Compiler.ZigAir.Memory
