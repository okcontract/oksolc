/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortNormalization
import Compiler.ZigAir.MemoryWordExchange

namespace Compiler.Extraction.InsertionSort
open Compiler.Algebraic Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

/-- The next adjacent exchange in the extracted inner loop has successful
element-pointer formation and nonoverlapping physical regions in the model.
No successful-access or noalias premise is supplied by the caller. -/
theorem adjacent_memory_access (state : State) (view : View) (j : Nat)
    (initial : state.valid = true) (cap : Writable state view) (inside : j + 1 < view.length) :
    elementPointer state view.buffer (j + 1) = .ok (view.pointer (j + 1)) ∧
    elementPointer state view.buffer j = .ok (view.pointer j) ∧
    ∃ cell, state.heap.lookup view.allocation = some cell ∧
      cell.base + (view.address j).offset + 4 = cell.base + (view.address (j + 1)).offset ∧
      cell.base + (view.address (j + 1)).offset + 4 ≤ addressLimit := by
  refine ⟨element_pointer state view (j + 1) initial cap inside,
    element_pointer state view j initial cap (by omega), ?_⟩
  obtain ⟨cell, found, _, upper, _⟩ := element_regions state view (j + 1) j initial cap inside (by omega) (by omega)
  exact ⟨cell, found, by simp [View.address]; omega, upper⟩

/-- The typed exchange memory contract produces exactly the two list writes
used by the generated inner loop. Every unrelated allocation is unchanged.
The native std.mem.swap byte loop must still refine this typed contract. -/
theorem adjacent_memory_exchange (state : State) (view : View) (items : List NodeId) (j : Nat)
    (initial : state.valid = true) (cap : Writable state view) (represented : Represents state view items)
    (inside : j + 1 < items.length) :
    ∃ after, exchange state view (j + 1) j = (.ok (), after) ∧
      after.valid = true ∧ Writable after view ∧
      Represents after view ((items.set (j + 1) items[j]).set j items[j + 1]) ∧
      ((items.set (j + 1) items[j]).set j items[j + 1]).Perm items ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      ∀ id, id ≠ view.allocation → after.heap.lookup id = state.heap.lookup id := by
  obtain ⟨after, ran, valid, writable, values, counters⟩ :=
    exchange_refines state view items (j + 1) j initial cap represented inside (by omega)
  exact ⟨after, ran, valid, writable, values, adjacent_exchange items j inside, counters⟩

theorem view_counter_bounds (state : State) (view : View) (i j : Nat)
    (initial : state.valid = true) (cap : Writable state view)
    (outer : i < view.length) (inner : 0 < j) (within : j ≤ i) :
    j < view.length ∧ j - 1 < view.length ∧ j ≠ j - 1 ∧ i + 1 < 2^64 ∧ j - 1 < 2^64 :=
  iteration_indices view.length i j (view_width state view initial cap) outer inner within

end Compiler.Extraction.InsertionSort
