/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordCopy
import Compiler.ZigAir.MemoryAllocationShape

namespace Compiler.ZigAir.Memory.WordCopy
open WordArray

/-- Even a partially initialized copy preserves every allocation's metadata.
This covers all read, write and bound faults with their actual prefix state. -/
theorem copyFrom_storage (source target : View) (remaining index : Nat) (state : State)
    (initial : state.valid = true) :
    (copyFrom source target remaining index state).2.valid = true ∧
      state.heap.RetainsShape (copyFrom source target remaining index state).2.heap := by
  induction remaining generalizing index state with
  | zero => exact ⟨initial, Heap.RetainsShape.refl _⟩
  | succ remaining ih =>
    simp only [copyFrom]
    split
    · cases read : load state (readPointer source index) with
      | error fault => exact ⟨initial, Heap.RetainsShape.refl _⟩
      | ok value =>
        dsimp only
        cases written : store state (target.pointer index) value with
        | error fault => exact ⟨initial, Heap.RetainsShape.refl _⟩
        | ok middle =>
          have rest := ih (index + 1) middle (store_preserves_valid state _ _ middle initial written)
          exact ⟨rest.1, (store_retains_shape state _ _ middle written).trans rest.2⟩
    · exact ⟨initial, Heap.RetainsShape.refl _⟩

theorem copy_storage (state : State) (source target : View) (initial : state.valid = true) :
    (copy state source target).2.valid = true ∧ state.heap.RetainsShape (copy state source target).2.heap := by
  simp only [copy]
  split
  · exact ⟨initial, Heap.RetainsShape.refl _⟩
  · split
    · exact ⟨initial, Heap.RetainsShape.refl _⟩
    · exact copyFrom_storage source target source.length 0 state initial

end Compiler.ZigAir.Memory.WordCopy
