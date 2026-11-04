/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryShapePreservation
import Compiler.ZigAir.MemoryShapeRegions

namespace Compiler.ZigAir.Memory.ShapeTests

def cell : Allocation := ⟨8, usize, [(0, .scalar (.int false 64 0))], true, true⟩

theorem contents_can_change : cell.SameShape { cell with cells := [] } := ⟨rfl, rfl, rfl, rfl⟩
theorem base_cannot_change : ¬ cell.SameShape { cell with base := 16 } := by simp [Allocation.SameShape, cell]
theorem type_cannot_change : ¬ cell.SameShape { cell with type := .scalar (.int false 32) } := by simp [Allocation.SameShape, cell, usize]
theorem permission_cannot_change : ¬ cell.SameShape { cell with writable := false } := by simp [Allocation.SameShape, cell]
theorem lifetime_cannot_change : ¬ cell.SameShape { cell with stack := false } := by simp [Allocation.SameShape, cell]
theorem deletion_not_retained : ¬ Heap.RetainsShape [(0, cell)] [] := by
  intro retained
  obtain ⟨_, impossible, _⟩ := retained 0 cell rfl
  contradiction

def caller : State := ⟨[(0, cell)], 1, 16⟩
def allocated : State := ⟨[(1, { cell with base := 16, cells := [] }), (0, cell)], 2, 24⟩

theorem caller_valid : caller.valid = true := by decide
theorem allocated_valid : allocated.valid = true := by decide
theorem allocate_witness : allocate caller usize = .ok
    (.pointer (.pointer true false usize) ⟨1, 0⟩, allocated) := rfl
theorem allocation_retains_caller : caller.heap.RetainsShape allocated.heap :=
  allocate_retains_shape caller usize _ allocated caller_valid allocate_witness
theorem cleanup_retains_caller : caller.heap.RetainsShape (cleanup caller.nextId allocated).heap :=
  cleanup_retains_shape caller allocated caller_valid allocation_retains_caller
theorem cleanup_removes_fresh : (cleanup caller.nextId allocated).heap.lookup 1 = none := by decide
theorem cleanup_does_not_retain_fresh : ¬ allocated.heap.RetainsShape (cleanup caller.nextId allocated).heap := by
  intro retained
  obtain ⟨_, impossible, _⟩ := retained 1 { cell with base := 16, cells := [] } rfl
  rw [cleanup_removes_fresh] at impossible
  contradiction
theorem live_regions_separate : cell.base + 8 ≤ 16 ∨ 16 + 8 ≤ cell.base :=
  valid_regions_separated allocated 0 1 cell { cell with base := 16, cells := [] } ⟨8, 8⟩ ⟨8, 8⟩
    allocated_valid (by decide) rfl rfl rfl rfl

end Compiler.ZigAir.Memory.ShapeTests
