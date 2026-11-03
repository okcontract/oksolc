/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.WyhashBuffer
import Compiler.Extraction.WyhashLocalTests

set_option maxRecDepth 4096

namespace Compiler.Extraction.WyhashBuffer.Tests
open Compiler.ZigAir.Memory WyhashLocal

def bytes (length i : Nat) : BitVec 8 := BitVec.ofNat 8 (i * 17 + length * 29 + 3)
def s0 (length : Nat) : BitVec 64 := BitVec.ofNat 64 (2^63 + length)
def s1 (length : Nat) : BitVec 64 := BitVec.ofNat 64 (0x1122334455667788 + length)
def s2 (length : Nat) : BitVec 64 := BitVec.ofNat 64 (0x99aabbccddeeff00 + length)
def total (length : Nat) : BitVec 64 := BitVec.ofNat 64 (if length < 41 then length + 48 else length)
def source (length : Nat) : Cells :=
  (List.range 48).foldl (fun cells i =>
    if i < length ∨ (length < 16 ∧ 48 - (16 - length) ≤ i) then cells.set (56 + i) (ByteSlice.value (bytes length i)) else cells)
    ((core none none (s0 length) (s1 length) (s2 length) (total length)).set 48 (word (BitVec.ofNat 64 length)))

def edges : List (Nat × BitVec 64) := [(0, 958015201082284350), (1, 10934927712876204435), (15, 8656643314581096934), (16, 14955724781747698451), (17, 14996067907151721286), (31, 15307333682453796091), (32, 3371184154110025817), (33, 14724851402975897376), (47, 7294473824717544550), (48, 5136084580210777493)]

/-- Native-capture fixtures cross both strict round boundaries and the scratch
boundary, including length zero. They leave unused buffer bytes absent. -/
theorem boundary_results : edges.all (fun (length, expected) => decide (run (source length) = .ok expected)) = true := by
  decide +kernel

theorem partial_source_valid : (source 1).valid objectType = true := by decide +kernel

theorem partial_source_represents : Represents (source 1) 1 (bytes 1) := by
  have table : ∀ i : Fin 48, i.val < 1 ∨ 33 ≤ i.val →
      (source 1).lookup (56 + i.val) = some (ByteSlice.value (bytes 1 i.val)) := by decide +kernel
  constructor
  · intro i inside
    exact table ⟨i, by omega⟩ (Or.inl inside)
  · intro _ i lower upper
    exact table ⟨i, upper⟩ (Or.inr (by omega))

theorem partial_source_consumed : run (source 1) = .ok (result 1 (bytes 1) (s0 1) (s1 1) (s2 1) (total 1)) :=
  run_verified (source 1) none none (s0 1) (s1 1) (s2 1) (total 1) 1 (bytes 1)
    partial_source_valid (by unfold WyhashLocal.Represents; decide +kernel) (by decide +kernel) (by decide) (by decide) partial_source_represents

theorem absent_gap : (source 1).lookup 58 = none := by decide +kernel

/-- Exactly sixteen remaining bytes belong to the tail, so the loop performs
no byte or state read even when those cells are absent. -/
theorem exact_boundary_no_reads : WyhashFinalization.loop nativeOps [] scratch 0 0 [] = .ok [] := by
  rw [WyhashFinalization.loop]
  rfl

theorem missing_suffix_rejected : run ((source 1).forget (56 + 47) 1) = .error .uninitialized := by decide +kernel

theorem missing_prefix_rejected : run ((source 17).forget 56 1) = .error .uninitialized := by decide +kernel

theorem wrong_buffer_type_rejected :
    run ((source 17).set 56 (word 0)) = .error .malformed := by decide +kernel

theorem oversize_rejected : run ((source 48).set 48 (word 49)) = .error .sourceBounds := by decide +kernel

theorem small_key_explicit : run ((source 1).set 40 (word 16)) = .error .unsupported := by decide +kernel

theorem missing_length_rejected : run ((source 1).forget 48 8) = .error .uninitialized := by decide +kernel

theorem absent_scratch_rejected : ByteSlice.read [] scratch 0 = .error .uninitialized := by decide +kernel

theorem slice_bounds_rejected : ByteSlice.read (source 17) (buffer 0 17) 17 = .error .sourceBounds := by decide +kernel

theorem wrong_byte_order : ByteSlice.readLE [(0, ByteSlice.value 1), (1, ByteSlice.value 2)]
    ⟨.array 2 ByteSlice.byte, 0, 2⟩ 0 2 = .ok 513 := by decide +kernel

end Compiler.Extraction.WyhashBuffer.Tests
