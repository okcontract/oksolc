/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryStorageProofs

namespace Compiler.ZigAir.Memory.ByteSlice

def byte : Ty := .scalar (.int false 8)
def value (bits : BitVec 8) : Value := .scalar (.int false 8 bits.toNat)

/-- A slice inside a declared local object, using the existing sparse cells.
Heap lifetime and access permissions belong to the enclosing local-frame proof. -/
structure View where
  owner : Ty
  base : Nat
  length : Nat

def Geometry (view : View) : Prop := ∀ i < view.length,
  leafType view.owner (view.base + i) = some byte ∧
  acceptsView view.owner (view.base + i) byte = true

def Represents (cells : Cells) (view : View) (bytes : Nat → BitVec 8) : Prop :=
  ∀ i < view.length, cells.lookup (view.base + i) = some (value (bytes i))

def read (cells : Cells) (view : View) (index : Nat) : Except Fault (BitVec 8) := do
  if index ≥ view.length then .error .sourceBounds else
  let .scalar (.int false 8 bits) ← cells.readLeaf view.owner (view.base + index) byte | .error .malformed
  .ok (BitVec.ofInt 8 bits)

def write (cells : Cells) (view : View) (index : Nat) (bits : BitVec 8) : Except Fault Cells :=
  if index ≥ view.length then .error .sourceBounds else
  cells.write view.owner (view.base + index) (value bits)

/-- Little-endian unsigned interpretation of initialized byte leaves. No
alignment, padding or default value is inferred from a pointer cast. -/
def decode (bytes : Nat → BitVec 8) (offset : Nat) : Nat → BitVec 64
  | 0 => 0
  | count + 1 => (bytes offset).zeroExtend 64 ||| (decode bytes (offset + 1) count <<< 8)

def readLE (cells : Cells) (view : View) (offset : Nat) : Nat → Except Fault (BitVec 64)
  | 0 => .ok 0
  | count + 1 => do
      let head ← read cells view offset
      let tail ← readLE cells view (offset + 1) count
      .ok (head.zeroExtend 64 ||| (tail <<< 8))

def copy (source : Cells) (sourceView : View) (targetView : View) :
    Nat → Nat → Nat → Cells → Except Fault Cells
  | _, _, 0, target => .ok target
  | src, dst, count + 1, target => do
      let bits ← read source sourceView src
      let after ← write target targetView dst bits
      copy source sourceView targetView (src + 1) (dst + 1) count after

theorem value_valid (bits : BitVec 8) : (value bits).valid = true := by
  have bound := bits.isLt
  simp [value, Value.valid, Scalar.Value.valid, Scalar.Ty.contains, Scalar.Ty.lower, Scalar.Ty.upper]
  omega

theorem value_typed (bits : BitVec 8) : (value bits).hasType byte = true := by
  simp only [Value.hasType, value, Value.type, Scalar.Value.type, byte, decide_true, Bool.true_and]
  exact value_valid bits

theorem read_verified (cells : Cells) (view : View) (index : Nat) (bits : BitVec 8)
    (inside : index < view.length) (declared : leafType view.owner (view.base + index) = some byte)
    (found : cells.lookup (view.base + index) = some (value bits)) :
    read cells view index = .ok bits := by
  simp only [read, if_neg (by omega : ¬index ≥ view.length), Cells.readLeaf, declared,
    ne_self_iff_false, ↓reduceIte, found, value_typed, bind, Except.bind]
  simp only [value, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem write_verified (cells : Cells) (view : View) (index : Nat) (bits : BitVec 8)
    (inside : index < view.length) (geometry : Geometry view) :
    write cells view index bits = .ok (cells.set (view.base + index) (value bits)) := by
  rw [write, if_neg (by omega : ¬index ≥ view.length)]
  apply Cells.write_single
  · exact value_valid bits
  · exact (geometry index inside).2
  · simp only [leafFits, (geometry index inside).1, value, Value.type, Scalar.Value.type,
      byte, decide_true, Bool.true_and]
    exact value_valid bits
  · rfl

theorem readLE_verified (cells : Cells) (view : View) (bytes : Nat → BitVec 8)
    (geometry : Geometry view) (represented : Represents cells view bytes)
    (offset count : Nat) (inside : offset + count ≤ view.length) :
    readLE cells view offset count = .ok (decode bytes offset count) := by
  induction count generalizing offset with
  | zero => rfl
  | succ count ih =>
    have head := read_verified cells view offset (bytes offset) (by omega)
      (geometry offset (by omega)).1 (represented offset (by omega))
    simp only [readLE, head, ih (offset + 1) (by omega), decode, bind, Except.bind]

/-- Copy derives every initialized destination byte and frames every other leaf.
Both source and target geometry are checked by the ordinary reader/writer. -/
theorem copy_verified (source target : Cells) (sourceView targetView : View)
    (bytes : Nat → BitVec 8) (sourceGeometry : Geometry sourceView) (targetGeometry : Geometry targetView)
    (represented : Represents source sourceView bytes) (src dst count : Nat)
    (sourceBound : src + count ≤ sourceView.length) (targetBound : dst + count ≤ targetView.length) :
    ∃ after, copy source sourceView targetView src dst count target = .ok after ∧
      (∀ i < count, after.lookup (targetView.base + (dst + i)) = some (value (bytes (src + i)))) ∧
      (∀ offset, offset < targetView.base + dst ∨ targetView.base + dst + count ≤ offset →
        after.lookup offset = target.lookup offset) := by
  induction count generalizing src dst target with
  | zero => exact ⟨target, rfl, by omega, by simp⟩
  | succ count ih =>
    have head := read_verified source sourceView src (bytes src) (by omega)
      (sourceGeometry src (by omega)).1 (represented src (by omega))
    have written := write_verified target targetView dst (bytes src) (by omega) targetGeometry
    obtain ⟨after, ran, values, frame⟩ := ih (target.set (targetView.base + dst) (value (bytes src)))
      (src + 1) (dst + 1) (by omega) (by omega)
    refine ⟨after, ?_, ?_, ?_⟩
    · simp only [copy, head, written, bind, Except.bind, ran]
    · intro i inside
      cases i with
      | zero =>
        simpa only [Nat.add_zero, Cells.lookup_set] using frame (targetView.base + dst) (Or.inl (by omega))
      | succ i => simpa only [Nat.add_assoc, Nat.add_comm 1 i] using values i (by omega)
    · intro offset outside
      rw [frame offset (by omega), Cells.lookup_set_other _ _ _ _ (by omega)]

theorem array_geometry (length : Nat) : Geometry ⟨.array length byte, 0, length⟩ := by
  intro index inside
  constructor <;> simp [leafType, acceptsView, byte, Ty.layout, inside, Nat.mod_one]

/-- Successful byte copies preserve the same declared object, including gaps
that remain undefined. Each reached write uses the original validity theorem. -/
theorem copy_valid (source : Cells) (sourceView targetView : View) (src dst count : Nat)
    (target after : Cells) (valid : target.valid targetView.owner = true)
    (ran : copy source sourceView targetView src dst count target = .ok after) :
    after.valid targetView.owner = true := by
  induction count generalizing src dst target with
  | zero => cases Except.ok.inj ran; exact valid
  | succ count ih =>
    cases loaded : read source sourceView src with
    | error fault => simp only [copy, loaded, bind, Except.bind] at ran; cases ran
    | ok bits =>
      cases written : write target targetView dst bits with
      | error fault => simp only [copy, loaded, written, bind, Except.bind] at ran; cases ran
      | ok middle =>
        have stored : target.write targetView.owner (targetView.base + dst) (value bits) = .ok middle := by
          unfold write at written
          split at written
          · contradiction
          · exact written
        apply ih (src + 1) (dst + 1) middle
        · exact Cells.write_preserves_valid target targetView.owner _ _ middle valid stored
        · simpa only [copy, loaded, written, bind, Except.bind] using ran

/-- A read-only byte image in the existing cell representation. Constructing
this view is not an allocation claim about the original byte source. -/
def cellsFrom : List (BitVec 8) → Nat → Cells
  | [], _ => []
  | head :: tail, base => (base, value head) :: cellsFrom tail (base + 1)

def imageView (bytes : List (BitVec 8)) : View := ⟨.array bytes.length byte, 0, bytes.length⟩

theorem cellsFrom_lookup (bytes : List (BitVec 8)) (base index : Nat) (inside : index < bytes.length) :
    (cellsFrom bytes base).lookup (base + index) = some (value (bytes[index]?.getD 0)) := by
  induction bytes generalizing base index with
  | nil => simp at inside
  | cons head tail ih =>
    cases index with
    | zero => simp [cellsFrom, Cells.lookup]
    | succ index =>
      have different : base ≠ base + (index + 1) := by omega
      have next := ih (base + 1) index (by simpa using inside)
      simpa [cellsFrom, Cells.lookup, different, Nat.add_assoc, Nat.add_comm 1 index] using next

theorem image_represents (bytes : List (BitVec 8)) :
    Represents (cellsFrom bytes 0) (imageView bytes) (fun i => bytes[i]?.getD 0) := by
  intro i inside
  exact cellsFrom_lookup bytes 0 i inside

end Compiler.ZigAir.Memory.ByteSlice
