/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordFrame

namespace Compiler.ZigAir.Memory.WordArray

/-- The heap observations of Frame, for calls whose private allocation changes
the allocator counters. This relation makes no equality claim about counters;
the executable call retains them in its actual returned State. -/
structure HeapFrame (view : View) (before after : State) : Prop where
  allocations : ∀ id, id ≠ view.allocation → after.heap.lookup id = before.heap.lookup id
  outside : ∀ offset, Outside view offset →
    load after (.pointer (.pointer true false word) ⟨view.allocation, offset⟩) =
      load before (.pointer (.pointer true false word) ⟨view.allocation, offset⟩)

theorem HeapFrame.refl (view : View) (state : State) : HeapFrame view state state :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

theorem HeapFrame.trans (first : HeapFrame view before middle) (second : HeapFrame view middle after) :
    HeapFrame view before after :=
  ⟨fun id apart => (second.allocations id apart).trans (first.allocations id apart),
    fun offset outside => (second.outside offset outside).trans (first.outside offset outside)⟩

theorem Frame.heapFrame (frame : Frame view before after) : HeapFrame view before after :=
  ⟨frame.allocations, frame.outside⟩

theorem HeapFrame.heap_eq (frame : HeapFrame view before middle) (same : after.heap = middle.heap) :
    HeapFrame view before after := by
  refine ⟨fun id apart => by rw [same]; exact frame.allocations id apart, ?_⟩
  intro offset outside
  exact (load_eq_of_lookup middle after _ _ _ _ (by rw [same])).trans (frame.outside offset outside)

end Compiler.ZigAir.Memory.WordArray
