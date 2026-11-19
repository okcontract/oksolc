/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.GeneratedWyhashUpdate
import Compiler.ZigAir.MemoryByteRangeRefinement
import Compiler.ZigAir.WyhashInit

namespace Compiler.ZigAir.WyhashUpdateAir
open Memory AggregateAir Compiler.Extraction
open WyhashInit (object_word_read object_word_store)

abbrev objectType := WyhashLocal.objectType
abbrev selfPointer (id : Nat) : Value := .pointer (.pointer true false objectType) ⟨id, 0⟩

theorem end_bound {state : State} {id : Nat} (frame : CellFrame state id)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (strict : state.nextAddress < addressLimit) : frame.cell.base + 104 < addressLimit := by
  obtain ⟨_, _, layout, shape, _, inside, _⟩ := valid_lookup state id frame.cell valid frame.found
  rw [typed, show objectType.layout = some ⟨104, 8⟩ from rfl] at shape
  cases Option.some.inj shape
  dsimp at inside
  omega

theorem field_pointer {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (typed : frame.cell.type = objectType) (offset : Nat) (field : Ty)
    (selected : fieldType objectType offset = some field) :
    Memory.fieldPointer (frame.install cells) (selfPointer id) offset =
      .ok (.pointer (.pointer true false field) ⟨id, offset⟩) := by
  have accessed := frame.field_read_access cells 0 ⟨104, 8⟩ (by decide)
    (by rw [WyhashInit.object_frame_layout frame typed]; decide) (by decide)
    (by rw [WyhashInit.object_frame_layout frame typed]; decide)
  simpa only [Nat.zero_add] using fieldPointer_of_access _ _ _ objectType field ⟨104, 8⟩ offset true false rfl
    accessed (typed ▸ acceptsView_self objectType) selected

/-- Include the one-past, zero-byte access used by native pointer arithmetic.
Successful native allocation supplies the strict end bound; validity alone
only supplies a non-strict bound and is insufficient for the one-past case. -/
theorem byte_access {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (offset count : Nat) (inside : offset + count ≤ 104) :
    access (frame.install cells) ⟨id, offset⟩ ⟨count, 1⟩ false = .ok { frame.cell with cells } := by
  obtain ⟨_, positive, layout, shaped, _, extent, limit⟩ := valid_lookup state id frame.cell valid frame.found
  rw [typed, show objectType.layout = some ⟨104, 8⟩ from rfl] at shaped
  cases Option.some.inj shaped
  have checks : ¬(frame.cell.base = 0 ∨ frame.cell.base + 104 > addressLimit ∨
      frame.cell.base + offset ≥ addressLimit ∨ offset + count > 104 ∨
      (frame.cell.base + offset) % 1 ≠ 0) := by dsimp at extent; omega
  simp only [access, frame.lookup, typed, show objectType.layout = some ⟨104, 8⟩ from rfl,
    if_neg checks, Bool.false_and, Bool.false_eq_true, ↓reduceIte]

theorem buffer_cast {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit) :
    pointerCast (frame.install cells) (.pointer true true ByteSlice.byte)
      (.pointer (.pointer true false (.array 48 ByteSlice.byte)) ⟨id, 56⟩) =
        .ok (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩) := by
  have accessed := byte_access frame cells valid typed endBound 56 0 (by decide)
  simp only [pointerCast, pointerCompatible, ByteSlice.byte, Ty.layout, Ty.leafLayout,
    Bool.not_true, Bool.true_and, Bool.false_or, decide_true, Bool.or_true,
    Bool.false_eq_true, ↓reduceIte, accessed, bind, Except.bind]

theorem buffer_offset {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (offset : Nat) (inside : offset ≤ 48) :
    offsetPointer (frame.install cells) false (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56⟩) offset =
      .ok (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + offset⟩) := by
  have start := byte_access frame cells valid typed endBound 56 0 (by decide)
  have finish := byte_access frame cells valid typed endBound (56 + offset) 0 (by omega)
  have upper : frame.cell.base + (56 + offset) < addressLimit := by omega
  have raw : ¬((frame.cell.base : Int) + 56 + offset < 0 ∨
      (frame.cell.base : Int) + 56 + offset ≥ addressLimit) := by omega
  have lower : ¬((frame.cell.base : Int) + 56 + offset < frame.cell.base) := by omega
  have position : ((frame.cell.base : Int) + 56 + offset).toNat - frame.cell.base = 56 + offset := by omega
  simp only [offsetPointer, ByteSlice.byte, Ty.layout, Ty.leafLayout, Nat.reduceEqDiff,
    Bool.false_eq_true, ↓reduceIte, start, bind, Except.bind, Nat.mul_one, show ((56 : Nat) : Int) = 56 from rfl,
    if_neg raw, if_neg lower, position, finish]

theorem buffer_slice {state : State} {id : Nat} (frame : CellFrame state id) (cells : Cells)
    (valid : state.valid = true) (typed : frame.cell.type = objectType)
    (endBound : frame.cell.base + 104 < addressLimit)
    (offset count : Nat) (inside : offset + count ≤ 48) :
    makeSlice (frame.install cells) (.slice true ByteSlice.byte)
      (.pointer (.pointer true true ByteSlice.byte) ⟨id, 56 + offset⟩) count =
      .ok (.slice (.slice true ByteSlice.byte) ⟨id, 56 + offset⟩ count) := by
  have accessed := byte_access frame cells valid typed endBound (56 + offset) count (by omega)
  have width : ¬count ≥ addressLimit := by
    have : 48 < addressLimit := by decide
    omega
  simp only [makeSlice, ByteSlice.byte, Ty.layout, Ty.leafLayout,
    Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
    Nat.mul_one, accessed, bind, Except.bind, if_neg width, ne_self_iff_false, or_self, Nat.reduceEqDiff]

/-- The native buffer copy shares the existing update invariant. This covers
the buffered branch, filling a block, and both retained-suffix copies; no byte
value or unrelated allocation is synthesized. -/
theorem copy_buffer {state : State} {id : Nat} (frame : CellFrame state id)
    (typed : frame.cell.type = WyhashLocal.objectType)
    (address : Address) (source cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents source view bytes)
    (reads : ByteRange.Reads state address view.length bytes) (apart : address.allocation ≠ id)
    (total src dst count : Nat) (core : WyhashUpdate.Core cells total)
    (sourceBound : src + count ≤ view.length) (targetBound : dst + count ≤ 48) :
    ∃ after, ByteRange.copy (frame.install cells)
        (.slice (.slice true ByteSlice.byte) ⟨id, 56 + dst⟩ count)
        (.pointer (.pointer false true ByteSlice.byte) ⟨address.allocation, address.offset + src⟩) =
          (.ok (), frame.install after) ∧
      ByteSlice.copy source view (WyhashBuffer.buffer 0 48) src dst count cells = .ok after ∧
      WyhashUpdate.Core after total ∧
      (∀ i < count, WyhashUpdate.ByteAt after (56 + (dst + i))) ∧
      (∀ offset, offset < 56 + dst ∨ 56 + dst + count ≤ offset → after.lookup offset = cells.lookup offset) := by
  obtain ⟨after, copied, nextCore, values, outside⟩ :=
    WyhashUpdate.copy_buffer source cells view bytes geometry represented total src dst count core sourceBound targetBound
  refine ⟨after, ?_, copied, nextCore, values, outside⟩
  exact ByteRange.copy_refines frame address source cells after view (WyhashBuffer.buffer 0 48) bytes
    src dst count apart typed.symm (WyhashBuffer.buffer_geometry 0 48 (by decide))
    (by rw [WyhashInit.object_frame_layout frame typed]; decide) geometry represented reads sourceBound targetBound copied

end Compiler.ZigAir.WyhashUpdateAir
