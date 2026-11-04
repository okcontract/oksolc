/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryBytePointers
import Compiler.ZigAir.MemoryStackFrame

namespace Compiler.ZigAir.Memory.WordArray

/-- The hash helper borrows the original words. Readability suffices; it does
not require a writable allocation or a whole-array root declaration. -/
def View.readonlySlice (view : View) : Value :=
  .slice (.slice false word) (view.address 0) view.length

def View.byteSlice (view : View) : Value :=
  .slice (.slice false ByteAccess.byte) (view.address 0) (view.length * 4)

private theorem read_region (state : State) (address : Address) (value : Value)
    (read : load state (.pointer (.pointer true false word) address) = .ok value) :
    ∃ cell, access state address ⟨4, 4⟩ false = .ok cell ∧
      acceptsView cell.type address.offset word = true := by
  cases accessed : access state address ⟨4, 4⟩ false with
  | error fault => simp [load, Ty.layout, Ty.leafLayout, accessed, bind, Except.bind] at read
  | ok cell =>
    refine ⟨cell, rfl, ?_⟩
    cases viewed : acceptsView cell.type address.offset word
    · simp only [load, show word.layout = some ⟨4, 4⟩ from rfl, accessed,
        bind, Except.bind, readCell, Cells.read, viewed, Bool.not_false, ↓reduceIte] at read
      contradiction
    · rfl

/-- The first and last initialized word derive the complete byte extent in
their shared allocation. Empty slices intentionally require no source access. -/
theorem Represents.byte_region (state : State) (view : View) (items : List (BitVec 32))
    (represented : Represents state view items) (positive : 0 < view.length) :
    ∃ cell, access state (view.address 0) ⟨4, 4⟩ false = .ok cell ∧
      acceptsView cell.type (view.address 0).offset word = true ∧
      access state (view.address 0) ⟨view.length * 4, 1⟩ false = .ok cell := by
  have length := represented.1
  obtain ⟨cell, first, typed⟩ := read_region state (view.address 0) _ (represented.2 0 (by omega))
  obtain ⟨last, finish, _⟩ := read_region state (view.address (view.length - 1)) _
    (represented.2 (view.length - 1) (by omega))
  obtain ⟨found, region, shaped, base, limit, start, _, _, _⟩ := access_success_region _ _ _ _ _ first
  obtain ⟨foundLast, lastRegion, lastShape, _, _, _, extent, _, _⟩ := access_success_region _ _ _ _ _ finish
  have same : last = cell := Option.some.inj (foundLast.symm.trans found)
  subst last
  have sameRegion : lastRegion = region := Option.some.inj (lastShape.symm.trans shaped)
  subst lastRegion
  simp only [View.address, Nat.add_zero] at start extent
  have checked : ¬(cell.base = 0 ∨ cell.base + region.bytes > addressLimit ∨
      cell.base + (view.address 0).offset ≥ addressLimit ∨
      (view.address 0).offset + view.length * 4 > region.bytes ∨
      (cell.base + (view.address 0).offset) % 1 ≠ 0) := by
    simp only [View.address, Nat.add_zero]
    omega
  exact ⟨cell, first, typed, by simp only [access, found, shaped, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, if_neg checked]⟩

theorem Represents.byte_cast (state : State) (view : View) (items : List (BitVec 32))
    (represented : Represents state view items) (positive : 0 < view.length) :
    ByteAccess.cast state false true 4 (.pointer (.pointer false true word) (view.address 0)) =
      .ok (ByteAccess.pointer false true (view.address 0)) := by
  obtain ⟨cell, first, typed, _⟩ := represented.byte_region state view items positive
  obtain ⟨_, _, _, _, _, _, _, aligned, _⟩ := access_success_region _ _ _ _ _ first
  simp only [ByteAccess.cast, word, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    ne_self_iff_false, and_false, first, bind, Except.bind, typed, Bool.not_true, aligned]

theorem Represents.byte_slice (state : State) (view : View) (items : List (BitVec 32))
    (represented : Represents state view items) (positive : 0 < view.length)
    (bounded : view.length * 4 < addressLimit) :
    makeSlice state (.slice false ByteAccess.byte) (ByteAccess.pointer false true (view.address 0))
      (view.length * 4) = .ok view.byteSlice := by
  obtain ⟨cell, _, _, full⟩ := represented.byte_region state view items positive
  simp only [makeSlice, ByteAccess.pointer, ByteAccess.byte, View.byteSlice,
    ne_self_iff_false, Bool.false_and, Bool.false_eq_true, or_self, ↓reduceIte, Nat.not_le.mpr bounded,
    Ty.layout, Ty.leafLayout, Nat.reduceEqDiff, Nat.mul_one, full, bind, Except.bind]

theorem Represents.byte_offset_zero (state : State) (view : View) (items : List (BitVec 32))
    (represented : Represents state view items) (positive : 0 < view.length) :
    offsetPointer state false (ByteAccess.pointer false true (view.address 0)) 0 =
      .ok (ByteAccess.pointer false true (view.address 0)) := by
  obtain ⟨cell, first, _, _⟩ := represented.byte_region state view items positive
  have start := ByteAccess.access_bytes state (view.address 0) cell 0 0 first (by decide) (by decide)
  simp only [Nat.add_zero] at start
  obtain ⟨_, _, _, _, _, upper, _, _, _⟩ := access_success_region _ _ _ _ _ first
  have raw : ¬((cell.base : Int) + ↑(view.address 0).offset < 0 ∨
      (cell.base : Int) + ↑(view.address 0).offset ≥ ↑addressLimit) := by omega
  have lower : ¬((cell.base : Int) + ↑(view.address 0).offset < ↑cell.base) := by omega
  have position : ((cell.base : Int) + ↑(view.address 0).offset).toNat - cell.base =
      (view.address 0).offset := by omega
  simp only [offsetPointer, ByteAccess.pointer, ByteAccess.byte, Ty.layout, Ty.leafLayout,
    Nat.reduceEqDiff, Bool.false_eq_true, ↓reduceIte, start, bind, Except.bind, Nat.zero_mul, Int.natCast_zero,
    Int.add_zero, if_neg raw, if_neg lower, position]

theorem Represents.extend {before after : State} {view : View} {items : List (BitVec 32)}
    (represented : Represents before view items) (frame : StackFrame before after) :
    Represents after view items :=
  ⟨represented.1, fun index inside => frame.old_load true false word _ _ (represented.2 index inside)⟩

end Compiler.ZigAir.Memory.WordArray
