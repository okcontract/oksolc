/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MachineGuarded
import Compiler.ZigAir.MemoryWordSwapInvocation
import Compiler.ZigAir.MemoryWordSwapSites

/-! Argument-relative data-access confinement in the typed heap. Byte pointers
retain the left/right operand identity and a bounded lane of that argument's
word. Typed accesses use the private counter. This is not native provenance or
a source-to-AIR/LLVM noalias preservation theorem. -/
namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir Control.Machine
open Memory.WordArray (View Writable Represents)
open MemoryFill (size size_valid size_typed counter unitRef)

def ByteBorrow (view : View) (left right : Nat) (env : Env) (pointer : Ref) : Prop :=
  ∃ index : Fin 4,
    (pointer = .local 18 ∧ pointer.eval env = .ok (ByteAccess.pointer true false (ByteAccess.atByte (view.address left) index))) ∨
    (pointer = .local 19 ∧ pointer.eval env = .ok (ByteAccess.pointer true false (ByteAccess.atByte (view.address right) index)))

def Footprint (view : View) (left right : Nat) (slot : Address) (event : Observation Ty Prim Value State) : Prop :=
  match event.site.2.2 with
  | .alloc child => child = usize ∧ event.state.nextId = slot.allocation
  | .load pointer | .store pointer _ => pointer.eval event.env = .ok (counter slot)
  | .wordByteLoad _ pointer | .wordByteStore _ pointer _ => ByteBorrow view left right event.env pointer
  | .argument .. | .scalar .. | .pointerField .. | .pointerCast .. | .offsetPointer .. |
    .elementPointer .. | .wordByteCast .. | .sliceElementPointer .. | .slice .. | .sliceLen .. |
    .slicePtr .. | .checkBounds .. => True

theorem Footprint.byte_access (view : View) (left right : Nat) (slot : Address)
    (event : Observation Ty Prim Value State) (order : WordBytes.Order) (pointer : Ref)
    (kind : event.site.2.2 = .wordByteLoad order pointer ∨ ∃ value, event.site.2.2 = .wordByteStore order pointer value)
    (checked : Footprint view left right slot event) : ByteBorrow view left right event.env pointer := by
  rcases kind with load | ⟨value, store⟩
  · simpa only [Footprint, load] using checked
  · simpa only [Footprint, store] using checked

theorem Footprint.counter_access (view : View) (left right : Nat) (slot : Address)
    (event : Observation Ty Prim Value State) (pointer : Ref)
    (kind : event.site.2.2 = .load pointer ∨ ∃ value, event.site.2.2 = .store pointer value)
    (checked : Footprint view left right slot event) : pointer.eval event.env = .ok (counter slot) := by
  rcases kind with load | ⟨value, store⟩
  · simpa only [Footprint, load] using checked
  · simpa only [Footprint, store] using checked

theorem Footprint.allocation (view : View) (left right : Nat) (slot : Address)
    (event : Observation Ty Prim Value State) (child : Ty) (kind : event.site.2.2 = .alloc child)
    (checked : Footprint view left right slot event) : child = usize ∧ event.state.nextId = slot.allocation := by
  simpa only [Footprint, kind] using checked

/-- The modeled read/modify/write implementation of a byte store resolves to
exactly its argument's original word, not a neighboring word. -/
theorem borrowed_word (view : View) (left right : Nat) (env : Env) (pointer : Ref)
    (borrowed : ByteBorrow view left right env pointer) :
    ∃ address, pointer.eval env = .ok (ByteAccess.pointer true false address) ∧
      ((pointer = .local 18 ∧ ByteAccess.wordAddress address = view.address left ∧
          (view.address left).offset ≤ address.offset ∧ address.offset < (view.address left).offset + 4) ∨
       (pointer = .local 19 ∧ ByteAccess.wordAddress address = view.address right ∧
          (view.address right).offset ≤ address.offset ∧ address.offset < (view.address right).offset + 4)) := by
  obtain ⟨index, first | second⟩ := borrowed
  · refine ⟨ByteAccess.atByte (view.address left) index, first.2, Or.inl ⟨first.1, ?_, ?_, ?_⟩⟩
    · exact ByteAccess.wordAddress_atByte _ _ (by simp [View.address])
    · simp [ByteAccess.atByte]
    · simp only [ByteAccess.atByte]; have := index.isLt; omega
  · refine ⟨ByteAccess.atByte (view.address right) index, second.2, Or.inr ⟨second.1, ?_, ?_, ?_⟩⟩
    · exact ByteAccess.wordAddress_atByte _ _ (by simp [View.address])
    · simp [ByteAccess.atByte]
    · simp only [ByteAccess.atByte]; have := index.isLt; omega

theorem borrowed_bytes_apart (view : View) (left right : Nat) (i j : Fin 4) (apart : left ≠ right) :
    ByteAccess.atByte (view.address left) i ≠ ByteAccess.atByte (view.address right) j := by
  intro same
  have offset := congrArg Address.offset same
  simp only [ByteAccess.atByte, View.address] at offset
  have := i.isLt
  have := j.isLt
  omega

theorem borrowed_counter_apart (view : View) (word : Nat) (index : Fin 4) (slot : Address)
    (older : view.allocation < slot.allocation) : ByteAccess.atByte (view.address word) index ≠ slot := by
  intro same
  have id := congrArg Address.allocation same
  simp only [ByteAccess.atByte, View.address] at id
  omega

end Compiler.ZigAir.MemoryWordSwap
