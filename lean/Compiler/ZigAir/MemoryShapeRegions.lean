/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryAllocationShape
import Compiler.ZigAir.MemoryWordExchange

namespace Compiler.ZigAir.Memory

theorem Allocation.SameShape.address (before after : Allocation) (same : before.SameShape after)
    (offset : Nat) : after.base + offset = before.base + offset := by rw [same.1]

theorem Heap.RetainsShape.writable (before after : State) (view : WordArray.View)
    (retained : before.heap.RetainsShape after.heap) (cap : WordArray.Writable before view) :
    WordArray.Writable after view := by
  obtain ⟨extent, cell, found, typed, writable, bound⟩ := cap
  obtain ⟨updated, lookup, shape⟩ := retained view.allocation cell found
  exact ⟨extent, updated, lookup, shape.2.1.trans typed, shape.2.2.1.trans writable, bound⟩

private theorem separated_symm (a b : Nat × Allocation) (apart : separated a b = true) :
    separated b a = true := by
  cases left : a.2.type.layout <;> cases right : b.2.type.layout <;>
    simp_all [separated, or_comm, ne_comm]

private theorem lookup_separated (heap : Heap) (first second : Nat) (a b : Allocation)
    (valid : heap.Pairwise fun x y => separated x y = true) (apart : first ≠ second)
    (left : heap.lookup first = some a) (right : heap.lookup second = some b) :
    separated (first, a) (second, b) = true := by
  induction heap with
  | nil => simp [Heap.lookup] at left
  | cons entry tail ih =>
    rcases entry with ⟨id, cell⟩
    by_cases firstHead : id = first
    · subst id
      simp only [Heap.lookup_cons, ite_true, Option.some.injEq] at left
      subst cell
      simp only [Heap.lookup_cons, if_neg apart] at right
      exact List.rel_of_pairwise_cons valid (Heap.lookup_mem tail second b right)
    · simp only [Heap.lookup_cons, if_neg firstHead] at left
      by_cases secondHead : id = second
      · subst id
        simp only [Heap.lookup_cons, ite_true, Option.some.injEq] at right
        subst cell
        exact separated_symm _ _ (List.rel_of_pairwise_cons valid (Heap.lookup_mem tail first a left))
      · simp only [Heap.lookup_cons, if_neg secondHead] at right
        exact ih valid.of_cons left right

/-- Different live allocation IDs occupy disjoint modeled physical intervals.
Both lookups and both layouts are required; validity alone does not make an
arbitrary pointer live. -/
theorem valid_regions_separated (state : State) (first second : Nat) (a b : Allocation) (x y : Layout)
    (initial : state.valid = true) (apart : first ≠ second)
    (left : state.heap.lookup first = some a) (right : state.heap.lookup second = some b)
    (leftLayout : a.type.layout = some x) (rightLayout : b.type.layout = some y) :
    a.base + x.bytes ≤ b.base ∨ b.base + y.bytes ≤ a.base := by
  simp only [State.valid, Bool.and_eq_true, decide_eq_true_eq] at initial
  have separated := lookup_separated state.heap first second a b initial.2 apart left right
  simp only [Memory.separated, leftLayout, rightLayout, Bool.and_eq_true, decide_eq_true_eq] at separated
  exact separated.2

end Compiler.ZigAir.Memory
