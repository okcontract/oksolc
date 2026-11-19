/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WordBytes

/-! Value-level specification for sequential exchange of initialized u32 byte
lanes. The order is explicit; the four-lane result is independent of it. -/
namespace Compiler.ZigAir.WordBytes

def exchangeLane (order : Order) (words : BitVec 32 × BitVec 32) (index : Fin 4) : BitVec 32 × BitVec 32 :=
  (write order words.1 index (read order words.2 index),
   write order words.2 index (read order words.1 index))

def exchangeLanes (order : Order) (words : BitVec 32 × BitVec 32) (indices : List (Fin 4)) : BitVec 32 × BitVec 32 :=
  indices.foldl (exchangeLane order) words

theorem exchangeLane_read (order : Order) (words : BitVec 32 × BitVec 32) (index other : Fin 4) :
    read order (exchangeLane order words index).1 other =
      (if other = index then read order words.2 index else read order words.1 other) ∧
    read order (exchangeLane order words index).2 other =
      (if other = index then read order words.1 index else read order words.2 other) := by
  by_cases same : other = index
  · subst other
    simp only [exchangeLane, read_write_same, ↓reduceIte, and_self]
  · simp only [exchangeLane, read_write_other order _ index other _ same, if_neg same, and_self]

theorem exchange_four (order : Order) (a b : BitVec 32) :
    exchangeLanes order (a, b) [0, 1, 2, 3] = (b, a) := by
  apply Prod.ext <;> apply ext order <;> intro index
  all_goals
    obtain ⟨index, inside⟩ := index
    have cases : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;>
      simp [exchangeLanes, List.foldl, exchangeLane, read_write_same, read_write_other]

end Compiler.ZigAir.WordBytes
