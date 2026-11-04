/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordCopy
import Compiler.ZigAir.MemoryWordCallFrame

namespace Compiler.ZigAir.Memory.WordCopy
open WordArray

/-- A call may change private allocator counters while retaining a disjoint
readonly source, including a source slice in the destination allocation. -/
theorem source_frame (state after : State) (source target : View) (items : List (BitVec 32))
    (represented : Represents state source items) (separate : disjoint source target = true)
    (framed : HeapFrame target state after) : Represents after source items := by
  refine ⟨represented.1, ?_⟩
  intro index inside
  have old := represented.2 index inside
  by_cases same : source.allocation = target.allocation
  · have outside : Outside target (source.address index).offset := by
      have bound : index < source.length := by simpa only [represented.1] using inside
      simp only [disjoint, decide_eq_true_eq] at separate
      simp only [Outside, View.address]
      omega
    have kept := framed.outside (source.address index).offset outside
    simpa only [View.pointer, View.address, same] using kept.trans (by simpa only [View.pointer, View.address, same] using old)
  · exact (load_eq_of_lookup state after true false word (source.address index) (framed.allocations source.allocation same)).trans old

end Compiler.ZigAir.Memory.WordCopy
