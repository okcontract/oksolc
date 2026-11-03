/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArray
import Compiler.ZigAir.MemoryWordAllocationProofs

namespace Compiler.Extraction.RepresentativeArray.Backing
open Compiler.ZigAir.Memory

/-- Persistent backing uses the complete admitted descriptor type. Reserving
capacity initializes no descriptor and publishes no header. Remapping, copying,
release, allocator identity and the native growth caller remain separate steps. -/
def type (capacity : Nat) : Ty := .array capacity Expression.allocationType

theorem layout_checked (capacity : Nat) : (type capacity).layout = some ⟨capacity * 32, 8⟩ := by
  simp only [type, Ty.layout, Expression.layout_checked, bind, Option.bind]

def reserve (state : State) (capacity : Nat) (allocate : RegionAllocation.Allocator σ) (effects : σ) :
    (Except Fault (Option Address) × State) × σ :=
  if capacity ≥ addressLimit then ((.error .malformed, state), effects) else
  RegionAllocation.reserve state (type capacity) allocate effects

/-- The checked region contract derives successful reservation, complete but
uninitialized backing, fresh identity, monotone address high-water mark and exact
preservation of every previously live allocation. No final validity premise is
needed, and no logical graph or registry contents are fabricated. -/
theorem reserve_verified (state : State) (capacity base : Nat) (allocate : RegionAllocation.Allocator σ)
    (effects reached : σ) (valid : state.valid = true) (nonzero : capacity ≠ 0)
    (size : capacity * 32 < addressLimit)
    (response : allocate (capacity * 32) 8 effects = (some base, reached))
    (fits : RegionAllocation.Fits state ⟨capacity * 32, 8⟩ base) :
    ∃ after, reserve state capacity allocate effects = ((.ok (some ⟨state.nextId, 0⟩), after), reached) ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      after.heap.lookup state.nextId = some ⟨base, type capacity, [], true, false⟩ ∧
      after.nextId = state.nextId + 1 ∧ after.nextAddress = max state.nextAddress (base + capacity * 32) ∧
      (∀ id, id ≠ state.nextId → after.heap.lookup id = state.heap.lookup id) := by
  have width : capacity < addressLimit := by omega
  let after := RegionAllocation.extend state (type capacity) (capacity * 32) base
  have checked := RegionAllocation.extend_valid state (type capacity) ⟨capacity * 32, 8⟩ base valid
    (layout_checked capacity) fits
  refine ⟨after, ?_, checked, RegionAllocation.extend_shape _ _ _ _ valid, ?_, rfl, rfl, ?_⟩
  · simpa only [reserve, if_neg (Nat.not_le.mpr width)] using
      RegionAllocation.reserve_admitted state (type capacity) ⟨capacity * 32, 8⟩ base allocate effects reached
        valid (layout_checked capacity) (by dsimp; omega) size response fits
  · simp [after, RegionAllocation.extend_lookup, RegionAllocation.cell]
  · intro id apart
    simp only [after, RegionAllocation.extend_lookup, if_neg (Ne.symm apart)]

theorem reserve_preserves_valid (state : State) (capacity : Nat) (allocate : RegionAllocation.Allocator σ)
    (effects : σ) (valid : state.valid = true) : (reserve state capacity allocate effects).1.2.valid = true := by
  unfold reserve
  split
  · exact valid
  · exact RegionAllocation.reserve_preserves_valid state (type capacity) allocate effects valid

/-- Independent parent arguments retain their initialized offset view after
any reservation outcome, including OOM and rejected responses. Aliases into a
subsequently remapped representative buffer still require separate reasoning. -/
theorem reserve_parent_borrow (state : State) (capacity : Nat) (allocate : RegionAllocation.Allocator σ)
    (effects : σ) (parent : WordArray.View) (items : List (BitVec 32))
    (valid : state.valid = true) (represented : WordArray.Represents state parent items) :
    WordArray.Represents (reserve state capacity allocate effects).1.2 parent items := by
  unfold reserve
  split
  · exact represented
  · refine ⟨represented.1, ?_⟩
    intro index inside
    have nonempty : items ≠ [] := by intro empty; simp [empty] at inside
    have older := WordAllocation.source_older state parent items valid represented nonempty
    have frame := RegionAllocation.reserve_heap_other state (type capacity) allocate effects parent.allocation (by omega)
    exact (load_eq_of_lookup state _ true false WordArray.word (parent.address index) frame).trans (represented.2 index inside)

end Compiler.Extraction.RepresentativeArray.Backing
