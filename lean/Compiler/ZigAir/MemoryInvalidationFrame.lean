/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryInvalidation
import Compiler.ZigAir.MemoryRecordFields

namespace Compiler.ZigAir.Memory

/-- Invalidation changes initialized leaves, never field geometry. -/
theorem fieldPointer_after_invalidate (before after : State) (write : Bool) (child : Ty) (target : Address)
    (writable many : Bool) (owner : Ty) (address : Address) (offset : Nat)
    (executed : invalidate before write child target = .ok after) :
    fieldPointer after (.pointer (.pointer writable many owner) address) offset =
      fieldPointer before (.pointer (.pointer writable many owner) address) offset := by
  obtain ⟨_, layout, cell, _, accessed, _, rfl⟩ := invalidate_success before write child target after executed
  exact fieldPointer_replace_cells before target.allocation cell _ writable many owner address offset
    (access_success_region before target layout true cell accessed).1

/-- Reads outside the erased subobject retain both values and rejection
outcomes, including slice pointer/length leaves in the same allocation. -/
theorem load_disjoint_after_invalidate (before after : State) (write : Bool) (child : Ty) (target : Address)
    (layout : Layout) (readWritable readMany : Bool) (readType : Ty) (readOffset : Nat)
    (shaped : child.layout = some layout) (executed : invalidate before write child target = .ok after)
    (apart : ∀ position ∈ readType.readOffsets readOffset, position < target.offset ∨ target.offset + layout.bytes ≤ position) :
    load after (.pointer (.pointer readWritable readMany readType) ⟨target.allocation, readOffset⟩) =
      load before (.pointer (.pointer readWritable readMany readType) ⟨target.allocation, readOffset⟩) := by
  obtain ⟨_, actual, cell, actualShape, accessed, _, rfl⟩ := invalidate_success before write child target after executed
  cases Option.some.inj (actualShape.symm.trans shaped)
  have found := (access_success_region before target layout true cell accessed).1
  have reads : (cell.cells.forget target.offset layout.bytes).read cell.type readOffset readType =
      cell.cells.read cell.type readOffset readType := by
    apply Cells.read_eq_of_lookup
    intro position member
    rw [Cells.lookup_forget]
    apply if_neg
    rintro ⟨lower, upper⟩
    rcases apart position member with earlier | later
    · exact (Nat.not_le_of_gt earlier) lower
    · exact (Nat.not_le_of_gt upper) later
  cases readShape : readType.layout with
  | none => simp [load, readShape]
  | some readLayout =>
    have updated := access_replace_cells before ⟨target.allocation, readOffset⟩ readLayout false cell
      (cell.cells.forget target.offset layout.bytes) found
    simp only [load, readShape, updated, bind, Except.bind]
    cases checked : access before ⟨target.allocation, readOffset⟩ readLayout false with
    | error fault => rfl
    | ok readCell =>
      have same : readCell = cell := Option.some.inj
        ((access_success_region before _ _ false readCell checked).1.symm.trans found)
      subst readCell
      exact reads

end Compiler.ZigAir.Memory
