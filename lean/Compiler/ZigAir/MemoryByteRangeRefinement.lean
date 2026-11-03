/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryByteRange
import Compiler.ZigAir.MemoryByteSlice

namespace Compiler.ZigAir.Memory.ByteRange

/-- The input bytes are observations of the original allocation, including
integer representation bytes. They need not be stored as byte leaves. -/
def Reads (state : State) (address : Address) (length : Nat) (bytes : Nat → BitVec 8) : Prop :=
  ∀ i < length, ScalarBytes.readAt state ⟨address.allocation, address.offset + i⟩ = .ok (bytes i)

theorem Reads.window {state : State} {address : Address} {length : Nat} {bytes : Nat → BitVec 8}
    (reads : Reads state address length bytes) (offset count : Nat) (inside : offset + count ≤ length) :
    Reads state ⟨address.allocation, address.offset + offset⟩ count (fun i => bytes (offset + i)) := by
  intro i bound
  simpa only [Nat.add_assoc] using reads (offset + i) (by omega)

theorem Reads.install {state : State} {id : Nat} (frame : CellFrame state id)
    (cells : Cells) (address : Address) (length : Nat) (bytes : Nat → BitVec 8)
    (apart : address.allocation ≠ id) (reads : Reads state address length bytes) :
    Reads (frame.install cells) address length bytes := by
  intro i inside
  exact (ScalarBytes.readAt_same_allocation _ _ ⟨address.allocation, address.offset + i⟩
    (frame.outside cells _ apart)).trans (reads i inside)

/-- Saving parameters and other invocation locals preserves the original input
observations. Empty inputs need no allocation or dereference premise. -/
theorem Reads.extend {before after : State} (stack : StackFrame before after)
    (address : Address) (length : Nat) (bytes : Nat → BitVec 8)
    (reads : Reads before address length bytes) : Reads after address length bytes := by
  intro i inside
  have read := reads i inside
  cases found : before.heap.lookup address.allocation with
  | none => simp only [ScalarBytes.readAt, access, found, bind, Except.bind] at read; cases read
  | some cell =>
    exact (ScalarBytes.readAt_same_allocation after before ⟨address.allocation, address.offset + i⟩
      ((stack.old_lookup _ _ found).trans found.symm)).trans read

/-- Lift the existing typed copy to the actual heap. The destination's access
checks follow from its writable frame and geometry. Each source read still
uses the original allocation after every preceding destination write. -/
theorem copyLoop_refines {state : State} {id : Nat} (frame : CellFrame state id)
    (address : Address) (source cells after : Cells) (sourceView targetView : ByteSlice.View)
    (bytes : Nat → BitVec 8) (src dst count index : Nat)
    (apart : address.allocation ≠ id) (typed : targetView.owner = frame.cell.type)
    (targetGeometry : ByteSlice.Geometry targetView)
    (targetRegion : targetView.base + targetView.length ≤ frame.layout.bytes)
    (sourceGeometry : ByteSlice.Geometry sourceView)
    (represented : ByteSlice.Represents source sourceView bytes)
    (reads : Reads state address sourceView.length bytes)
    (sourceBound : src + index + count ≤ sourceView.length)
    (targetBound : dst + index + count ≤ targetView.length)
    (copied : ByteSlice.copy source sourceView targetView (src + index) (dst + index) count cells = .ok after) :
    copyLoop (frame.install cells) ⟨address.allocation, address.offset + src⟩
      ⟨id, targetView.base + dst⟩ index count = (.ok (), frame.install after) := by
  induction count generalizing cells index with
  | zero =>
    cases Except.ok.inj copied
    rfl
  | succ count ih =>
    have srcInside : src + index < sourceView.length := by omega
    have dstInside : dst + index < targetView.length := by omega
    have read := ByteSlice.read_verified source sourceView (src + index) (bytes (src + index))
      srcInside (sourceGeometry _ srcInside).1 (represented _ srcInside)
    have written := ByteSlice.write_verified cells targetView (dst + index) (bytes (src + index))
      dstInside targetGeometry
    have nativeRead := (reads.install frame cells address sourceView.length bytes apart)
      (src + index) srcInside
    have nativeWrite := frame.store_eq cells (targetView.base + (dst + index))
      (ByteSlice.value (bytes (src + index))) ⟨1, 1⟩ (ByteSlice.value_typed _) rfl (by decide)
      (by change targetView.base + (dst + index) + 1 ≤ frame.layout.bytes; omega)
      (Nat.mod_one _) (Nat.mod_one _)
    have writeCells : cells.write frame.cell.type (targetView.base + (dst + index))
        (ByteSlice.value (bytes (src + index))) =
        .ok (cells.set (targetView.base + (dst + index)) (ByteSlice.value (bytes (src + index)))) := by
      simpa only [ByteSlice.write, if_neg (by omega : ¬dst + index ≥ targetView.length), typed] using written
    rw [writeCells] at nativeWrite
    have one : copyByte (frame.install cells) ⟨address.allocation, address.offset + src⟩
        ⟨id, targetView.base + dst⟩ index =
        .ok (frame.install (cells.set (targetView.base + (dst + index)) (ByteSlice.value (bytes (src + index))))) := by
      simpa only [copyByte, Nat.add_assoc, nativeRead, bind, Except.bind, ByteSlice.value] using nativeWrite
    simp only [ByteSlice.copy, read, written, bind, Except.bind] at copied
    rw [copyLoop, one]
    exact ih _ (index + 1) (by omega) (by omega) (by simpa only [Nat.add_assoc] using copied)

/-- The public memcpy primitive consumes the same relation. Its nonoverlap
check follows from the distinct source lifetime, not from a supplied success. -/
theorem copy_refines {state : State} {id : Nat} (frame : CellFrame state id)
    (address : Address) (source cells after : Cells) (sourceView targetView : ByteSlice.View)
    (bytes : Nat → BitVec 8) (src dst count : Nat)
    (apart : address.allocation ≠ id) (typed : targetView.owner = frame.cell.type)
    (targetGeometry : ByteSlice.Geometry targetView)
    (targetRegion : targetView.base + targetView.length ≤ frame.layout.bytes)
    (sourceGeometry : ByteSlice.Geometry sourceView)
    (represented : ByteSlice.Represents source sourceView bytes)
    (reads : Reads state address sourceView.length bytes)
    (sourceBound : src + count ≤ sourceView.length) (targetBound : dst + count ≤ targetView.length)
    (copied : ByteSlice.copy source sourceView targetView src dst count cells = .ok after) :
    copy (frame.install cells)
      (.slice (.slice true byte) ⟨id, targetView.base + dst⟩ count)
      (.pointer (.pointer false true byte) ⟨address.allocation, address.offset + src⟩) =
      (.ok (), frame.install after) := by
  simpa only [copy, destination, ByteRange.source, byte, apart, false_and,
    and_false, ↓reduceIte, Nat.add_zero] using
    copyLoop_refines frame address source cells after sourceView targetView bytes src dst count 0
      apart typed targetGeometry targetRegion sourceGeometry represented reads sourceBound targetBound copied

end Compiler.ZigAir.Memory.ByteRange
