/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.WyhashHash
import Compiler.ZigAir.MemoryStackFrame

namespace Compiler.Extraction.WyhashMemory
open Compiler.ZigAir.Memory WyhashLocal

/-- The representation of one private, live native allocation while its local
cells evolve. Every scalar operation below invokes the original heap primitive. -/
def replace (state : State) (id : Nat) (cell : Allocation) (cells : Cells) : State :=
  { state with heap := state.heap.replace id { cell with cells } }

def pointer (id offset : Nat) : Value := .pointer (.pointer true false usize) ⟨id, offset⟩

def ops (state : State) (id : Nat) (cell : Allocation) : Ops := ⟨
  fun cells slot => do
    let .scalar (.int false 64 bits) ← load (replace state id cell cells) (pointer id (8 * slot.val)) | .error .malformed
    .ok (BitVec.ofInt 64 bits),
  fun cells slot bits => do
    let after ← store (replace state id cell cells) (pointer id (8 * slot.val)) (word bits)
    let some updated := after.heap.lookup id | .error .unallocated
    .ok updated.cells⟩

theorem word_region (slot : Fin 6) :
    8 * slot.val + 8 ≤ 104 ∧ (8 * slot.val) % 8 = 0 := by
  have bound := slot.isLt
  constructor
  · omega
  · omega

/-- One heap/cell connection for all six finalization words, including absent
a/b. Its complete equality transports every existing finalization theorem. -/
theorem ops_eq {state : State} {id : Nat} (frame : CellFrame state id) (typed : frame.cell.type = objectType)
    (layout : frame.layout = ⟨104, 8⟩) : ops state id frame.cell = nativeOps := by
  apply Ops.eq
  · funext cells slot
    have loaded := frame.load_eq cells (8 * slot.val) usize ⟨8, 8⟩ rfl (by decide)
      (by rw [layout]; exact (word_region slot).1) (word_region slot).2 (by rw [layout]; rfl)
    have view := (geometry _ (slot_member slot)).2
    dsimp only [ops, nativeOps, pointer]
    change (do let .scalar (.int false 64 bits) ← load (frame.install cells)
                 (.pointer (.pointer true false usize) ⟨id, 8 * slot.val⟩) | .error .malformed
               .ok (BitVec.ofInt 64 bits)) = _
    rw [loaded, typed]
    simp only [usize] at view ⊢
    simp only [Cells.read, view, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  · funext cells slot bits
    have stored := frame.store_eq cells (8 * slot.val) (word bits) ⟨8, 8⟩
      (word_typed bits) rfl (by decide) (by rw [layout]; exact (word_region slot).1)
      (word_region slot).2 (by rw [layout]; rfl)
    rw [word_type] at stored
    dsimp only [ops, nativeOps, pointer]
    change (do let after ← store (frame.install cells)
                 (.pointer (.pointer true false usize) ⟨id, 8 * slot.val⟩) (word bits)
               let some updated := after.heap.lookup id | .error .unallocated
               .ok updated.cells) = _
    rw [stored, typed]
    cases cells.write objectType (8 * slot.val) (word bits) <;>
      simp only [Except.map, bind, Except.bind, frame.lookup]

end Compiler.Extraction.WyhashMemory
