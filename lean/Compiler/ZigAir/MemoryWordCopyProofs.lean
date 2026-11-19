/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordCopy

namespace Compiler.ZigAir.Memory.WordCopy
open WordArray

theorem copyFrom_refines (remaining index : Nat) (state : State) (source target : View) (items : List (BitVec 32))
    (initial : state.valid = true) (cap : Writable state target) (represented : Represents state source items)
    (length : target.length = items.length) (count : index + remaining = items.length)
    (separate : disjoint source target = true) (prior : Prefix state target items index) :
    ∃ after, copyFrom source target remaining index state = (.ok (), after) ∧
      after.valid = true ∧ Writable after target ∧ Represents after source items ∧
      Represents after target items ∧ Frame target state after := by
  induction remaining generalizing index state with
  | zero =>
    exact ⟨state, rfl, initial, cap, represented,
      ⟨length.symm, fun other bound => prior other bound (by omega)⟩, Frame.refl target state⟩
  | succ remaining ih =>
    have inside : index < items.length := by omega
    have sourceBound : index < source.length := by have := represented.1; omega
    have targetBound : index < target.length := by omega
    have read : load state (readPointer source index) = .ok (number items[index]) := by
      rw [load_readonly]; exact represented.2 index inside
    obtain ⟨middle, written⟩ := write_total state target index items[index] initial cap targetBound
    have frame := frame_store state middle target index items[index] targetBound written
    obtain ⟨after, rest, valid, writable, preserved, copied, framed⟩ := ih (index + 1) middle
      (store_preserves_valid state _ _ middle initial written) (writable_store state middle target _ _ written cap)
      (source_after_store state middle source target items index items[index] targetBound separate represented written)
      (by omega) (prefix_after_store state middle target items index inside prior written)
    refine ⟨after, ?_, valid, writable, preserved, copied, frame.trans framed⟩
    exact (copyFrom_step source target remaining index state middle _ sourceBound targetBound read written).trans rest

/-- Complete typed copying initializes an arbitrary writable destination and
preserves its source, unrelated allocations and out-of-view word observations.
All accesses are derived; no successful-copy or initialized-target premise. -/
theorem copy_refines (state : State) (source target : View) (items : List (BitVec 32))
    (initial : state.valid = true) (cap : Writable state target) (represented : Represents state source items)
    (length : source.length = target.length) (separate : disjoint source target = true) :
    ∃ after, copy state source target = (.ok (), after) ∧
      after.valid = true ∧ Writable after target ∧ Represents after source items ∧
      Represents after target items ∧ Frame target state after := by
  obtain ⟨after, ran, rest⟩ := copyFrom_refines source.length 0 state source target items initial cap represented
    (length.symm.trans represented.1.symm) (by have := represented.1; omega) separate (fun _ _ impossible => by omega)
  refine ⟨after, ?_, rest⟩
  simpa only [copy, length, ne_eq, not_true_eq_false, ↓reduceIte, separate, Bool.not_true, Bool.false_eq_true] using ran

theorem unequal_lengths_reject (state : State) (source target : View) (different : source.length ≠ target.length) :
    copy state source target = (.error .sourceBounds, state) := by simp only [copy, if_pos different]

theorem overlap_rejects (state : State) (source target : View)
    (length : source.length = target.length) (overlap : disjoint source target = false) :
    copy state source target = (.error .memoryValidity, state) := by
  simp only [copy, length, ne_eq, not_true_eq_false, ↓reduceIte, overlap, Bool.not_false]

end Compiler.ZigAir.Memory.WordCopy
