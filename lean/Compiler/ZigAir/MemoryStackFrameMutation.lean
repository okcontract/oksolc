/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryStackFrame
import Compiler.ZigAir.MemoryStackPrefix

namespace Compiler.ZigAir.Memory

/-- Successful native allocation leaves even its one-past address representable.
This is stronger than State.valid, which permits a counter at addressLimit. -/
theorem allocate_end_bound (state : State) (type : Ty) (value : Value) (after : State)
    (ran : allocate state type = .ok (value, after)) : after.nextAddress < addressLimit := by
  unfold allocate at ran
  split at ran
  · contradiction
  · cases shaped : type.layout with
    | none => simp only [shaped] at ran; cases ran
    | some layout =>
      simp only [shaped] at ran
      split at ran
      · contradiction
      · rename_i bound
        cases Except.ok.inj ran
        dsimp
        omega

/-- Invocation-local allocation preserves a caller's complete writable region. -/
def CellFrame.extend {before after : State} {id : Nat} (frame : CellFrame before id)
    (stack : StackFrame before after) : CellFrame after id where
  cell := frame.cell
  layout := frame.layout
  found := stack.old_lookup id frame.cell frame.found
  shaped := frame.shaped
  admitted := by
    simpa only [access, stack.old_lookup id frame.cell frame.found, frame.found] using frame.admitted

/-- Mutating a borrowed object beneath saved parameters changes the same object
in the caller frame. The local prefix and reached allocation history remain. -/
theorem StackFrame.install_old {before after : State} {id : Nat}
    (stack : StackFrame before after) (frame : CellFrame before id) (cells : Cells)
    (typed : cells.valid frame.cell.type = true) :
    StackFrame (frame.install cells) ((frame.extend stack).install cells) := by
  obtain ⟨locals, heap, owned⟩ := stack.extended
  have old := (valid_lookup before id frame.cell stack.initial frame.found).1
  have preserved : locals.replace id { frame.cell with cells } = locals :=
    Heap.replace_absent locals id _ (by
      intro entry present
      have fresh := (owned entry present).2
      omega)
  refine ⟨frame.valid cells stack.initial typed, (frame.extend stack).valid cells stack.valid typed,
    stack.nextId, locals, ?_, owned⟩
  change (after.heap.replace id { frame.cell with cells }) = locals ++ before.heap.replace id { frame.cell with cells }
  rw [heap]
  simpa only [Heap.replace, List.map_append] using congrArg (· ++ before.heap.replace id { frame.cell with cells }) preserved

theorem StackFrame.cleanup_install {before after : State} {id : Nat}
    (stack : StackFrame before after) (frame : CellFrame before id) (cells : Cells)
    (typed : cells.valid frame.cell.type = true) :
    (cleanup before.nextId ((frame.extend stack).install cells)).valid = true ∧
      (cleanup before.nextId ((frame.extend stack).install cells)).heap = (frame.install cells).heap := by
  have updated := stack.install_old frame cells typed
  exact ⟨updated.cleanup_valid, updated.cleanup_heap⟩

end Compiler.ZigAir.Memory
