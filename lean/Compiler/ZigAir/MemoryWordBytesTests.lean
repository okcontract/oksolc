/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordBytes

namespace Compiler.ZigAir.Memory.WordByteView.Tests

deriving instance DecidableEq for Except
open WordArray

def cell (value : BitVec 32) : Allocation :=
  ⟨16, .array 3 word, [(0, number 3735928559), (4, number value), (8, number 3131961357)], true, false⟩
def caller (value : BitVec 32) : State := ⟨[(0, cell value)], 1, 28⟩
def view : View := ⟨0, 1, 1⟩
def pointer : Value := view.pointer 0

def bytes (order : WordBytes.Order) (state : State) : List (Except Fault (BitVec 8)) :=
  (List.range 4).map (read order state pointer)

def words (state : State) : List (Except Fault Value) :=
  (List.range 3).map (fun index => load state (.pointer (.pointer true false word) ⟨0, index * 4⟩))

structure Observation where
  beforeBytes : List (Except Fault (BitVec 8))
  result : Except Fault Unit
  afterWords : List (Except Fault Value)
  afterBytes : List (Except Fault (BitVec 8))
  deriving DecidableEq, Repr

def observe (order : WordBytes.Order) (value : BitVec 32) (index : Nat) (byte : BitVec 8) : Observation :=
  let before := caller value
  let (result, after) := match write order before pointer index byte with
    | .error reason => (.error reason, before)
    | .ok after => (.ok (), after)
  ⟨bytes order before, result, words after, bytes order after⟩

def expected (before after : List (BitVec 8)) (value : BitVec 32) : Observation :=
  ⟨before.map Except.ok, .ok (), [number 3735928559, number value, number 3131961357].map Except.ok, after.map Except.ok⟩

theorem valid_caller : (caller 305419896).valid = true := by decide +kernel
theorem writable_caller : Writable (caller 305419896) view := ⟨3, cell 305419896, rfl, rfl, rfl, by decide⟩
theorem represented_caller : Represents (caller 305419896) view [305419896] := by
  refine ⟨rfl, ?_⟩
  intro index inside
  have : index = 0 := by simp at inside; omega
  subst index
  exact (by decide +kernel : load (caller 305419896) pointer = .ok (number 305419896))

theorem total_write_witness :
    ∃ after, write .little (caller 305419896) pointer 1 255 = .ok after ∧ after.valid = true ∧
      Writable after view ∧ Represents after view [305463160] ∧ Frame view (caller 305419896) after := by
  have computed : WordBytes.write .little (305419896 : BitVec 32) 1 255 = 305463160 := by decide +kernel
  obtain ⟨after, ran, valid, cap, values, frame⟩ :=
    write_refines .little (caller 305419896) view [305419896] 0 1 255
      valid_caller writable_caller represented_caller (by decide)
  change Represents after view [WordBytes.write .little 305419896 1 255] at values
  rw [computed] at values
  exact ⟨after, ran, valid, cap, values, frame⟩

def empty : State := ⟨[(0, { cell 0 with cells := [] })], 1, 28⟩
def readonly : State := ⟨[(0, { cell 0 with writable := false })], 1, 28⟩

theorem uninitialized_read : read .little empty pointer 0 = .error .uninitialized := by decide +kernel
theorem uninitialized_write : write .little empty pointer 0 255 = .error .uninitialized := by decide +kernel
theorem readonly_read : read .little readonly pointer 0 = .ok 0 := by decide +kernel
theorem readonly_write : write .little readonly pointer 0 255 = .error .readOnly := by decide +kernel
theorem const_pointer_write : write .little (caller 0) (.pointer (.pointer false false word) ⟨0, 4⟩) 0 255 =
    .error .readOnly := by decide +kernel
theorem bounds_read : read .little (caller 0) pointer 4 = .error .sourceBounds := by decide +kernel
theorem bounds_write : write .little (caller 0) pointer 4 255 = .error .sourceBounds := by decide +kernel
theorem dead_read : read .little {} pointer 0 = .error .unallocated := by decide +kernel

def pointerCell : State :=
  ⟨[(0, ⟨16, .pointer true false word, [(0, .pointer (.pointer true false word) ⟨1, 0⟩)], true, false⟩)], 1, 24⟩
def pointerToPointer : Value := .pointer (.pointer true false (.pointer true false word)) ⟨0, 0⟩
theorem pointer_bytes_reject : read .little pointerCell pointerToPointer 0 = .error .unsupported := by decide +kernel
theorem pointer_byte_write_reject : write .little pointerCell pointerToPointer 0 0 = .error .unsupported := by decide +kernel

-- Closed native fixtures follow; both target byte orders are checked.
theorem case_0_0_little : observe .little 0 0 0 =
    expected [0, 0, 0, 0] [0, 0, 0, 0] 0 := by decide +kernel
theorem case_0_1_little : observe .little 0 1 255 =
    expected [0, 0, 0, 0] [0, 255, 0, 0] 65280 := by decide +kernel
theorem case_0_2_little : observe .little 0 2 18 =
    expected [0, 0, 0, 0] [0, 0, 18, 0] 1179648 := by decide +kernel
theorem case_0_3_little : observe .little 0 3 129 =
    expected [0, 0, 0, 0] [0, 0, 0, 129] 2164260864 := by decide +kernel
theorem case_1_0_little : observe .little 4294967295 0 0 =
    expected [255, 255, 255, 255] [0, 255, 255, 255] 4294967040 := by decide +kernel
theorem case_1_1_little : observe .little 4294967295 1 255 =
    expected [255, 255, 255, 255] [255, 255, 255, 255] 4294967295 := by decide +kernel
theorem case_1_2_little : observe .little 4294967295 2 18 =
    expected [255, 255, 255, 255] [255, 255, 18, 255] 4279435263 := by decide +kernel
theorem case_1_3_little : observe .little 4294967295 3 129 =
    expected [255, 255, 255, 255] [255, 255, 255, 129] 2181038079 := by decide +kernel
theorem case_2_0_little : observe .little 3735928559 0 0 =
    expected [239, 190, 173, 222] [0, 190, 173, 222] 3735928320 := by decide +kernel
theorem case_2_1_little : observe .little 3735928559 1 255 =
    expected [239, 190, 173, 222] [239, 255, 173, 222] 3735945199 := by decide +kernel
theorem case_2_2_little : observe .little 3735928559 2 18 =
    expected [239, 190, 173, 222] [239, 190, 18, 222] 3725770479 := by decide +kernel
theorem case_2_3_little : observe .little 3735928559 3 129 =
    expected [239, 190, 173, 222] [239, 190, 173, 129] 2175647471 := by decide +kernel
theorem case_3_0_little : observe .little 2147483649 0 0 =
    expected [1, 0, 0, 128] [0, 0, 0, 128] 2147483648 := by decide +kernel
theorem case_3_1_little : observe .little 2147483649 1 255 =
    expected [1, 0, 0, 128] [1, 255, 0, 128] 2147548929 := by decide +kernel
theorem case_3_2_little : observe .little 2147483649 2 18 =
    expected [1, 0, 0, 128] [1, 0, 18, 128] 2148663297 := by decide +kernel
theorem case_3_3_little : observe .little 2147483649 3 129 =
    expected [1, 0, 0, 128] [1, 0, 0, 129] 2164260865 := by decide +kernel
theorem case_0_0_big : observe .big 0 0 0 =
    expected [0, 0, 0, 0] [0, 0, 0, 0] 0 := by decide +kernel
theorem case_0_1_big : observe .big 0 1 255 =
    expected [0, 0, 0, 0] [0, 255, 0, 0] 16711680 := by decide +kernel
theorem case_0_2_big : observe .big 0 2 18 =
    expected [0, 0, 0, 0] [0, 0, 18, 0] 4608 := by decide +kernel
theorem case_0_3_big : observe .big 0 3 129 =
    expected [0, 0, 0, 0] [0, 0, 0, 129] 129 := by decide +kernel
theorem case_1_0_big : observe .big 4294967295 0 0 =
    expected [255, 255, 255, 255] [0, 255, 255, 255] 16777215 := by decide +kernel
theorem case_1_1_big : observe .big 4294967295 1 255 =
    expected [255, 255, 255, 255] [255, 255, 255, 255] 4294967295 := by decide +kernel
theorem case_1_2_big : observe .big 4294967295 2 18 =
    expected [255, 255, 255, 255] [255, 255, 18, 255] 4294906623 := by decide +kernel
theorem case_1_3_big : observe .big 4294967295 3 129 =
    expected [255, 255, 255, 255] [255, 255, 255, 129] 4294967169 := by decide +kernel
theorem case_2_0_big : observe .big 3735928559 0 0 =
    expected [222, 173, 190, 239] [0, 173, 190, 239] 11386607 := by decide +kernel
theorem case_2_1_big : observe .big 3735928559 1 255 =
    expected [222, 173, 190, 239] [222, 255, 190, 239] 3741302511 := by decide +kernel
theorem case_2_2_big : observe .big 3735928559 2 18 =
    expected [222, 173, 190, 239] [222, 173, 18, 239] 3735884527 := by decide +kernel
theorem case_2_3_big : observe .big 3735928559 3 129 =
    expected [222, 173, 190, 239] [222, 173, 190, 129] 3735928449 := by decide +kernel
theorem case_3_0_big : observe .big 2147483649 0 0 =
    expected [128, 0, 0, 1] [0, 0, 0, 1] 1 := by decide +kernel
theorem case_3_1_big : observe .big 2147483649 1 255 =
    expected [128, 0, 0, 1] [128, 255, 0, 1] 2164195329 := by decide +kernel
theorem case_3_2_big : observe .big 2147483649 2 18 =
    expected [128, 0, 0, 1] [128, 0, 18, 1] 2147488257 := by decide +kernel
theorem case_3_3_big : observe .big 2147483649 3 129 =
    expected [128, 0, 0, 1] [128, 0, 0, 129] 2147483777 := by decide +kernel

end Compiler.ZigAir.Memory.WordByteView.Tests
