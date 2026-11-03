/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryByteExchange
import Compiler.ZigAir.MemoryWordBytesTests

namespace Compiler.ZigAir.Memory.ByteExchange.Tests
open WordArray

abbrev caller := WordByteView.Tests.caller 305419896
def view : View := ⟨0, 0, 2⟩
def items : List (BitVec 32) := [3735928559, 305419896]

theorem writable : Writable caller view := ⟨3, WordByteView.Tests.cell 305419896, rfl, rfl, rfl, by decide⟩
theorem represented : Represents caller view items := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have cases : index = 0 ∨ index = 1 := by simp only [items, List.length_cons, List.length_nil] at inside; omega
  rcases cases with rfl | rfl
  · exact (by decide +kernel : load caller (view.pointer 0) = .ok (number 3735928559))
  · exact (by decide +kernel : load caller (view.pointer 1) = .ok (number 305419896))

theorem total_witness (order : WordBytes.Order) :
    ∃ after, run order view 0 1 [0, 1, 2, 3] caller = (.ok (), after) ∧
      after.valid = true ∧ Writable after view ∧ Represents after view [305419896, 3735928559] ∧ Frame view caller after := by
  exact exchange_refines order caller view items 0 1 WordByteView.Tests.valid_caller writable represented
    (by decide) (by decide) (by decide)

def expected : State :=
  ⟨[(0, { WordByteView.Tests.cell 305419896 with cells :=
    [(4, number 3735928559), (0, number 305419896), (8, number 3131961357)] })], 1, 28⟩

theorem little_exact : run .little view 0 1 [0, 1, 2, 3] caller = (.ok (), expected) := by decide +kernel
theorem big_exact : run .big view 0 1 [0, 1, 2, 3] caller = (.ok (), expected) := by decide +kernel
theorem readonly_reject : run .little view 0 1 [0, 1, 2, 3] WordByteView.Tests.readonly =
    (.error .readOnly, WordByteView.Tests.readonly) := by decide +kernel
theorem uninitialized_reject : run .little view 0 1 [0, 1, 2, 3] WordByteView.Tests.empty =
    (.error .uninitialized, WordByteView.Tests.empty) := by decide +kernel
theorem logical_bounds_reject : run .little view 0 2 [0, 1, 2, 3] caller =
    (.error .sourceBounds, caller) := by decide +kernel
theorem dead_reject : run .little view 0 1 [0, 1, 2, 3] {} = (.error .unallocated, {}) := by decide +kernel
theorem empty_no_effect : run .little view 0 1 [] {} = (.ok (), {}) := rfl

-- The value algorithm also describes repeated lanes; a second exchange of the
-- same lane reverses the first. It must not be treated as completed coverage.
theorem repeated_lane : WordBytes.exchangeLanes .little (305419896, 3735928559) [0, 0] =
    (305419896, 3735928559) := by decide +kernel

end Compiler.ZigAir.Memory.ByteExchange.Tests
