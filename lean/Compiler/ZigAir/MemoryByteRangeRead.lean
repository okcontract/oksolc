/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryByteRangeRefinement

namespace Compiler.ZigAir.Memory.ByteRange

/-- The captured array load reads the same original bytes as the update's
cell-level reader. The empty window performs no access. -/
theorem Reads.read_window {state : State} {address : Address} {length : Nat}
    {bytes : Nat → BitVec 8} (reads : Reads state address length bytes)
    (offset count : Nat) (inside : offset + count ≤ length) :
    read state ⟨address.allocation, address.offset + offset⟩ count =
      .ok ((List.range count).map fun i => bytes (offset + i)) := by
  have sequence (indices : List Nat) (bounded : ∀ i ∈ indices, offset + i < length) :
      indices.mapM (fun i => ScalarBytes.readAt state
        ⟨address.allocation, address.offset + offset + i⟩) =
        .ok (indices.map fun i => bytes (offset + i)) := by
    induction indices with
    | nil => rfl
    | cons i rest ih =>
      have head := reads (offset + i) (bounded i (by simp))
      simp only [Nat.add_assoc] at head ih ⊢
      rw [List.mapM_cons, head, ih (fun j member => bounded j (by simp [member]))]
      rfl
  exact sequence (List.range count) (by intro i member; have := List.mem_range.mp member; omega)

/-- The AIR little-endian fold and the existing byte-slice decoder coincide
for every window, rather than only the eight-byte native load. -/
theorem decode_window (bytes : Nat → BitVec 8) (offset count : Nat) :
    ((List.range count).map fun i => bytes (offset + i)).foldr
      (fun byte (rest : BitVec 64) => byte.zeroExtend 64 ||| (rest <<< 8)) 0 =
        ByteSlice.decode bytes offset count := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    simpa only [List.range_succ_eq_map, List.map_cons, List.map_map,
      Function.comp_def, List.foldr_cons, Nat.add_zero, Nat.succ_eq_add_one,
      Nat.add_right_comm, ByteSlice.decode] using
      congrArg (fun rest : BitVec 64 => (bytes offset).zeroExtend 64 ||| (rest <<< 8)) (ih (offset + 1))

theorem decode_shift (bytes : Nat → BitVec 8) (offset start count : Nat) :
    ByteSlice.decode (fun i => bytes (offset + i)) start count = ByteSlice.decode bytes (offset + start) count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [ByteSlice.decode, ih, Nat.add_assoc]

/-- Successful byte reads derive the entire accessed region. This includes
zero-width pointer arithmetic at an admitted byte, but not an unproved one-past
address. No allocation type or successful wider access is supplied separately. -/
theorem Reads.access_window {state : State} {address : Address} {length : Nat}
    {bytes : Nat → BitVec 8} (reads : Reads state address length bytes)
    (offset count : Nat) (start : offset < length) (inside : offset + count ≤ length) :
    ∃ cell, access state ⟨address.allocation, address.offset + offset⟩ ⟨count, 1⟩ false = .ok cell := by
  have region (i : Nat) (inside : i < length) :
      ∃ cell, access state ⟨address.allocation, address.offset + i⟩ ⟨1, 1⟩ false = .ok cell := by
    have read := reads i inside
    cases found : access state ⟨address.allocation, address.offset + i⟩ ⟨1, 1⟩ false with
    | error fault => simp only [ScalarBytes.readAt, found, bind, Except.bind] at read; cases read
    | ok cell => exact ⟨cell, rfl⟩
  obtain ⟨cell, first⟩ := region offset start
  obtain ⟨last, finish⟩ := region (offset + (count - 1)) (by omega)
  obtain ⟨found, shape, shaped, positive, limit, begin, _, _, _⟩ := access_success_region _ _ _ _ _ first
  obtain ⟨foundLast, lastShape, lastShaped, _, _, _, extent, _, _⟩ := access_success_region _ _ _ _ _ finish
  have same : last = cell := Option.some.inj (foundLast.symm.trans found)
  subst last
  have sameShape : lastShape = shape := Option.some.inj (lastShaped.symm.trans shaped)
  subst lastShape
  have checked : ¬(cell.base = 0 ∨ cell.base + shape.bytes > addressLimit ∨
      cell.base + (address.offset + offset) ≥ addressLimit ∨
      address.offset + offset + count > shape.bytes ∨
      (cell.base + (address.offset + offset)) % 1 ≠ 0) := by
    dsimp at begin extent
    omega
  exact ⟨cell, by simp only [access, found, shaped, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, if_neg checked]⟩

theorem Reads.array_cast {state : State} {address : Address} {length : Nat}
    {bytes : Nat → BitVec 8} (reads : Reads state address length bytes)
    (offset count : Nat) (start : offset < length) (inside : offset + count ≤ length) :
    pointerCast state (.pointer false false (.array count byte))
      (.pointer (.pointer false true byte) ⟨address.allocation, address.offset + offset⟩) =
        .ok (.pointer (.pointer false false (.array count byte))
          ⟨address.allocation, address.offset + offset⟩) := by
  obtain ⟨cell, accessed⟩ := reads.access_window offset count start inside
  simp only [pointerCast, pointerCompatible, byte, Ty.layout, Ty.leafLayout,
    Bool.false_and, Bool.false_eq_true, decide_true, Bool.or_true,
    Bool.not_true, Bool.or_false, ↓reduceIte, Option.bind_some,
    Nat.mul_one, accessed, bind, Except.bind]

theorem Reads.byte_cast {state : State} {address : Address} {length : Nat}
    {bytes : Nat → BitVec 8} (reads : Reads state address length bytes)
    (offset count : Nat) (start : offset < length) :
    pointerCast state (.pointer false true byte)
      (.pointer (.pointer false false (.array count byte)) ⟨address.allocation, address.offset + offset⟩) =
        .ok (.pointer (.pointer false true byte) ⟨address.allocation, address.offset + offset⟩) := by
  obtain ⟨cell, accessed⟩ := reads.access_window offset 0 start (by omega)
  simp only [pointerCast, pointerCompatible, byte, Ty.layout, Ty.leafLayout,
    Bool.false_and, Bool.false_eq_true, decide_true, Bool.or_true,
    Bool.not_true, Bool.or_false, ↓reduceIte, accessed, bind, Except.bind]

theorem Reads.offset_pointer {state : State} {address : Address} {length : Nat}
    {bytes : Nat → BitVec 8} (reads : Reads state address length bytes)
    (start offset : Nat) (first : start < length) (inside : start + offset < length) :
    offsetPointer state false (.pointer (.pointer false true byte)
      ⟨address.allocation, address.offset + start⟩) offset =
        .ok (.pointer (.pointer false true byte)
          ⟨address.allocation, address.offset + (start + offset)⟩) := by
  obtain ⟨cell, begin⟩ := reads.access_window start 0 first (by omega)
  obtain ⟨last, finish⟩ := reads.access_window (start + offset) 0 inside (by omega)
  obtain ⟨found, _, _, _, _, _, _, _, _⟩ := access_success_region _ _ _ _ _ begin
  obtain ⟨foundLast, _, _, _, _, upper, _, _, _⟩ := access_success_region _ _ _ _ _ finish
  have same : last = cell := Option.some.inj (foundLast.symm.trans found)
  subst last
  have raw : ¬((cell.base : Int) + (address.offset + start) + offset < 0 ∨
      (cell.base : Int) + (address.offset + start) + offset ≥ addressLimit) := by
    dsimp at upper
    omega
  have lower : ¬((cell.base : Int) + (address.offset + start) + offset < cell.base) := by omega
  have position : ((cell.base : Int) + (address.offset + start) + offset).toNat - cell.base =
      address.offset + (start + offset) := by omega
  simp only [offsetPointer, byte, Ty.layout, Ty.leafLayout, Nat.reduceEqDiff,
    Bool.false_eq_true, ↓reduceIte, begin, bind, Except.bind, Nat.mul_one,
    Int.natCast_add, if_neg raw, if_neg lower, position, finish]

/-- A start inside the admitted bytes supplies native slice access, including
an empty window at that start. One-past starts need separate admission. -/
theorem Reads.make_slice {state : State} {address : Address} {length : Nat}
    {bytes : Nat → BitVec 8} (reads : Reads state address length bytes)
    (offset count : Nat) (start : offset < length) (inside : offset + count ≤ length)
    (bound : count < addressLimit) :
    makeSlice state (.slice false byte)
      (.pointer (.pointer false true byte) ⟨address.allocation, address.offset + offset⟩) count =
        .ok (.slice (.slice false byte) ⟨address.allocation, address.offset + offset⟩ count) := by
  obtain ⟨cell, accessed⟩ := reads.access_window offset count start inside
  simp only [makeSlice, byte, Ty.layout, Ty.leafLayout, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte, Nat.mul_one, accessed, bind, Except.bind,
    if_neg (by omega : ¬count ≥ addressLimit), ne_self_iff_false, or_self, Nat.reduceEqDiff]

end Compiler.ZigAir.Memory.ByteRange
