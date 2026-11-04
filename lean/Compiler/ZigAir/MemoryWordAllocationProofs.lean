/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordAllocation
import Compiler.ZigAir.MemoryRegionAllocationProofs
import Compiler.ZigAir.MemoryWordArrayWrites

namespace Compiler.ZigAir.Memory.WordAllocation
open WordArray

theorem extend_valid (state : State) (length base : Nat) (valid : state.valid = true)
    (fits : Fits state length base) : (extend state length base).valid = true := by
  exact RegionAllocation.extend_valid state (.array length word) ⟨length * 4, 4⟩ base valid
    (array_layout length) fits

theorem extend_lookup (state : State) (length base id : Nat) :
    (extend state length base).heap.lookup id = if state.nextId = id then some (cell length base) else state.heap.lookup id :=
  RegionAllocation.extend_lookup state (.array length word) (length * 4) base id

theorem next_id_fresh (state : State) (valid : state.valid = true) : state.heap.lookup state.nextId = none := by
  cases found : state.heap.lookup state.nextId with
  | none => rfl
  | some cell => have impossible := (valid_lookup state state.nextId cell valid found).1; omega

theorem extend_load_other (state : State) (length base : Nat) (writable many : Bool) (child : Ty)
    (address : Address) (apart : address.allocation ≠ state.nextId) :
    load (extend state length base) (.pointer (.pointer writable many child) address) =
      load state (.pointer (.pointer writable many child) address) := by
  exact RegionAllocation.extend_load_other state (.array length word) (length * 4) base writable many child address apart

theorem source_older (state : State) (source : View) (items : List (BitVec 32))
    (valid : state.valid = true) (represented : Represents state source items) (nonempty : items ≠ []) :
    source.allocation < state.nextId := by
  have inside : 0 < items.length := List.length_pos_iff.mpr nonempty
  have read := represented.2 0 inside
  cases accessed : access state (source.address 0) ⟨4, 4⟩ false with
  | error fault => simp [load, View.pointer, word, Ty.layout, accessed, bind, Except.bind] at read
  | ok cell => exact (valid_lookup state source.allocation cell valid
      (access_success_region state _ _ false cell accessed).1).1

theorem source_preserved (state : State) (length base : Nat) (source : View) (items : List (BitVec 32))
    (valid : state.valid = true) (represented : Represents state source items) :
    Represents (extend state length base) source items := by
  refine ⟨represented.1, ?_⟩
  intro index inside
  have nonempty : items ≠ [] := by intro empty; simp [empty] at inside
  have older := source_older state source items valid represented nonempty
  exact (extend_load_other state length base true false word (source.address index) (by
    change source.allocation ≠ state.nextId; omega)).trans (represented.2 index inside)

/-- A represented readonly source also bounds the byte request. The last word
must fit below the address limit; no source write capability is assumed. -/
theorem source_bytes_bound (state : State) (source : View) (items : List (BitVec 32))
    (represented : Represents state source items) : items.length * 4 < addressLimit := by
  by_cases empty : items = []
  · simp [empty, addressLimit]
  · have positive : 0 < items.length := List.length_pos_iff.mpr empty
    have read := represented.2 (items.length - 1) (by omega)
    cases accessed : access state (source.address (items.length - 1)) ⟨4, 4⟩ false with
    | error fault => simp [load, View.pointer, word, Ty.layout, accessed, bind, Except.bind] at read
    | ok cell =>
      obtain ⟨_, layout, _, base, bounded, _, inside, _, _⟩ := access_success_region state _ _ false cell accessed
      simp only [View.address] at inside
      omega

theorem reserve_empty (state : State) (allocate : Allocator σ) (effects : σ) :
    reserve state 0 allocate effects = ((.ok (some ⟨state.nextId, 0, 0⟩), state), effects) := rfl

theorem reserve_overflow (state : State) (length : Nat) (allocate : Allocator σ) (effects : σ)
    (valid : state.valid = true) (width : length < addressLimit) (overflow : addressLimit ≤ length * 4) :
    reserve state length allocate effects = ((.ok none, state), effects) := by
  have positive : length ≠ 0 := by intro zero; simp [zero, addressLimit] at overflow
  have bytes : length * 4 ≠ 0 := by omega
  simp [reserve, RegionAllocation.reserve, array_layout, positive, bytes, valid, Nat.not_le.mpr width, overflow, Except.map]

theorem reserve_failed (state : State) (length : Nat) (allocate : Allocator σ) (effects reached : σ)
    (valid : state.valid = true) (nonzero : length ≠ 0) (size : length * 4 < addressLimit)
    (response : allocate (length * 4) effects = (none, reached)) :
    reserve state length allocate effects = ((.ok none, state), reached) := by
  have width : length < addressLimit := by omega
  have bytes : length * 4 ≠ 0 := by omega
  simp [reserve, RegionAllocation.reserve, array_layout, nonzero, bytes, valid, Nat.not_le.mpr width,
    Nat.not_le.mpr size, response, Except.map]

theorem reserve_admitted (state : State) (length base : Nat) (allocate : Allocator σ) (effects reached : σ)
    (valid : state.valid = true) (nonzero : length ≠ 0) (size : length * 4 < addressLimit)
    (response : allocate (length * 4) effects = (some base, reached)) (fits : Fits state length base) :
    reserve state length allocate effects = ((.ok (some ⟨state.nextId, 0, length⟩), extend state length base), reached) := by
  have width : length < addressLimit := by omega
  have bytes : length * 4 ≠ 0 := by omega
  have accepted := extend_valid state length base valid fits
  unfold extend at accepted
  simp [reserve, RegionAllocation.reserve, array_layout, nonzero, bytes, valid, Nat.not_le.mpr width,
    Nat.not_le.mpr size, response, accepted, extend, Except.map]

theorem reserve_nonempty_success (state after : State) (length : Nat) (allocate : Allocator σ)
    (effects reached : σ) (view : View) (nonzero : length ≠ 0)
    (done : reserve state length allocate effects = ((.ok (some view), after), reached)) :
    ∃ base, view = ⟨state.nextId, 0, length⟩ ∧ after = extend state length base ∧
      allocate (length * 4) effects = (some base, reached) ∧ after.valid = true := by
  simp only [reserve, if_neg nonzero, RegionAllocation.reserve, array_layout] at done
  have bytes : length * 4 ≠ 0 := by omega
  simp only [if_neg bytes] at done
  split at done
  · simp at done
  · split at done
    · simp [Except.map] at done
    · split at done
      · simp [Except.map] at done
      · cases response : allocate (length * 4) effects with
        | mk selected advanced =>
          simp only [response] at done
          cases selected with
          | none => simp [Except.map] at done
          | some base =>
            dsimp only at done
            split at done
            · simp only [Except.map, Option.map] at done
              cases done
              exact ⟨base, rfl, rfl, rfl, by assumption⟩
            · simp [Except.map] at done

theorem reserve_preserves_valid (state : State) (length : Nat) (allocate : Allocator σ) (effects : σ)
    (valid : state.valid = true) : (reserve state length allocate effects).1.2.valid = true := by
  unfold reserve
  split
  · exact valid
  · split
    · exact valid
    · exact RegionAllocation.reserve_preserves_valid state (.array length word) (fun bytes _ => allocate bytes) effects valid

end Compiler.ZigAir.Memory.WordAllocation
