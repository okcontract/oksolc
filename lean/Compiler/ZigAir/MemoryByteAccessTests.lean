/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryBytePointers
import Compiler.ZigAir.MemoryByteAirLaws
import Compiler.ZigAir.MemoryWordBytesTests

namespace Compiler.ZigAir.Memory.ByteAccess.Tests
open WordArray
namespace Fixture
abbrev caller := WordByteView.Tests.caller
abbrev view := WordByteView.Tests.view
abbrev source := WordByteView.Tests.pointer
abbrev empty := WordByteView.Tests.empty
abbrev readonly := WordByteView.Tests.readonly
end Fixture
open Fixture

-- These compositions bind the native byte fixtures to the cast, slice and
-- element operations. They are model clients, not generated AIR functions.
def element (state : State) (index : Nat) : Except Fault Value := do
  let raw ← cast state true true 4 source
  let bytes ← makeSlice state (.slice true byte) raw 4
  sliceElementPointer state bytes index

def readByte (order : WordBytes.Order) (state : State) (index : Nat) : Except Fault (BitVec 8) := do
  let .scalar (.int false 8 value) ← read order state (← element state index) | .error .malformed
  .ok (BitVec.ofInt 8 value)

def writeByte (order : WordBytes.Order) (state : State) (index : Nat) (value : BitVec 8) : Except Fault State := do
  write order state (← element state index) (ByteAccess.number value)

def bytes (order : WordBytes.Order) (state : State) : List (Except Fault (BitVec 8)) :=
  (List.range 4).map (readByte order state)

def observe (order : WordBytes.Order) (value : BitVec 32) (index : Nat) (byte : BitVec 8) : WordByteView.Tests.Observation :=
  let before := caller value
  let (result, after) := match writeByte order before index byte with
    | .error reason => (.error reason, before)
    | .ok after => (.ok (), after)
  ⟨bytes order before, result, WordByteView.Tests.words after, bytes order after⟩

theorem cast_uninitialized : cast empty true true 4 source = .ok (pointer true true ⟨0, 4⟩) := by decide +kernel
theorem read_uninitialized : readByte .little empty 0 = .error .uninitialized := by decide +kernel
theorem write_uninitialized : writeByte .little empty 0 1 = .error .uninitialized := by decide +kernel
theorem cast_readonly : cast readonly false true 4 source = .ok (pointer false true ⟨0, 4⟩) := by decide +kernel
theorem read_readonly : readByte .little readonly 0 = .ok 0 := by decide +kernel
theorem write_readonly : writeByte .little readonly 0 1 = .error .readOnly := by decide +kernel
theorem cast_const_upgrade : cast (caller 0) true true 4 (.pointer (.pointer false false word) ⟨0, 4⟩) =
    .error .readOnly := by decide +kernel
theorem write_const : write .little (caller 0) (pointer false false ⟨0, 4⟩) (ByteAccess.number 1) =
    .error .readOnly := by decide +kernel
theorem cast_alignment_zero : cast (caller 0) true true 0 source = .error .unsupported := by decide +kernel
theorem cast_alignment_three : cast (caller 0) true true 3 source = .error .unsupported := by decide +kernel
theorem cast_alignment_eight : cast (caller 0) true true 8 source = .error .unsupported := by decide +kernel
theorem cast_alignment_one : cast (caller 0) true true 1 source = .ok (pointer true true ⟨0, 4⟩) := by decide +kernel
theorem cast_alignment_two : cast (caller 0) true true 2 source = .ok (pointer true true ⟨0, 4⟩) := by decide +kernel
theorem cast_unaligned : cast (caller 0) true true 4 (.pointer (.pointer true false word) ⟨0, 5⟩) =
    .error .memoryValidity := by decide +kernel
theorem cast_dead : cast {} true true 4 source = .error .unallocated := by decide +kernel
theorem cast_outside : cast (caller 0) true true 4 (.pointer (.pointer true false word) ⟨0, 12⟩) =
    .error .memoryValidity := by decide +kernel

def byteArray : State := ⟨[(0, ⟨16, .array 12 byte, [], true, false⟩)], 1, 28⟩
theorem cast_wrong_subobject : cast byteArray true true 4 source = .error .unsupported := by decide +kernel
theorem read_byte_array : read .little byteArray (pointer true false ⟨0, 4⟩) = .error .unsupported := by decide +kernel
theorem read_pointer_bytes : read .little WordByteView.Tests.pointerCell (pointer true false ⟨0, 0⟩) =
    .error .unsupported := by decide +kernel
theorem element_exact_bound : element (caller 0) 4 = .error .sourceBounds := by decide +kernel
theorem read_last_byte : read .little (caller 0) (pointer true false ⟨0, 11⟩) = .ok (ByteAccess.number 186) := by decide +kernel
theorem read_outside : read .little (caller 0) (pointer true false ⟨0, 12⟩) = .error .memoryValidity := by decide +kernel
theorem write_malformed : write .little (caller 0) (pointer true false ⟨0, 4⟩) (.scalar (.int false 8 256)) =
    .error .malformed := by decide +kernel
theorem write_negative : write .little (caller 0) (pointer true false ⟨0, 4⟩) (.scalar (.int false 8 (-1))) =
    .error .malformed := by decide +kernel

theorem air_cast :
    (MemoryAir.Prim.wordByteCast true true 4 (.constant source)).eval [] (fun _ => none) (caller 0) =
      (.ok (pointer true true ⟨0, 4⟩), caller 0) := by decide +kernel
theorem air_load :
    (MemoryAir.Prim.wordByteLoad .big (.constant (pointer true false ⟨0, 4⟩))).eval [] (fun _ => none) (caller 305419896) =
      (.ok (ByteAccess.number 18), caller 305419896) := by decide +kernel
theorem air_failure_retains_heap :
    (MemoryAir.Prim.wordByteStore .little (.constant (pointer false false ⟨0, 4⟩)) (.constant (ByteAccess.number 1))).eval
      [] (fun _ => none) (caller 0) = (.error .readOnly, caller 0) := by decide +kernel
theorem air_missing_operand :
    (MemoryAir.Prim.wordByteLoad .little (.local 0)).eval [] (fun _ => none) (caller 0) =
      (.error .malformed, caller 0) := by decide +kernel

theorem case_0_0_little : observe .little 0 0 0 =
    WordByteView.Tests.expected [0, 0, 0, 0] [0, 0, 0, 0] 0 := by decide +kernel
theorem case_0_1_little : observe .little 0 1 255 =
    WordByteView.Tests.expected [0, 0, 0, 0] [0, 255, 0, 0] 65280 := by decide +kernel
theorem case_0_2_little : observe .little 0 2 18 =
    WordByteView.Tests.expected [0, 0, 0, 0] [0, 0, 18, 0] 1179648 := by decide +kernel
theorem case_0_3_little : observe .little 0 3 129 =
    WordByteView.Tests.expected [0, 0, 0, 0] [0, 0, 0, 129] 2164260864 := by decide +kernel
theorem case_1_0_little : observe .little 4294967295 0 0 =
    WordByteView.Tests.expected [255, 255, 255, 255] [0, 255, 255, 255] 4294967040 := by decide +kernel
theorem case_1_1_little : observe .little 4294967295 1 255 =
    WordByteView.Tests.expected [255, 255, 255, 255] [255, 255, 255, 255] 4294967295 := by decide +kernel
theorem case_1_2_little : observe .little 4294967295 2 18 =
    WordByteView.Tests.expected [255, 255, 255, 255] [255, 255, 18, 255] 4279435263 := by decide +kernel
theorem case_1_3_little : observe .little 4294967295 3 129 =
    WordByteView.Tests.expected [255, 255, 255, 255] [255, 255, 255, 129] 2181038079 := by decide +kernel
theorem case_2_0_little : observe .little 3735928559 0 0 =
    WordByteView.Tests.expected [239, 190, 173, 222] [0, 190, 173, 222] 3735928320 := by decide +kernel
theorem case_2_1_little : observe .little 3735928559 1 255 =
    WordByteView.Tests.expected [239, 190, 173, 222] [239, 255, 173, 222] 3735945199 := by decide +kernel
theorem case_2_2_little : observe .little 3735928559 2 18 =
    WordByteView.Tests.expected [239, 190, 173, 222] [239, 190, 18, 222] 3725770479 := by decide +kernel
theorem case_2_3_little : observe .little 3735928559 3 129 =
    WordByteView.Tests.expected [239, 190, 173, 222] [239, 190, 173, 129] 2175647471 := by decide +kernel
theorem case_3_0_little : observe .little 2147483649 0 0 =
    WordByteView.Tests.expected [1, 0, 0, 128] [0, 0, 0, 128] 2147483648 := by decide +kernel
theorem case_3_1_little : observe .little 2147483649 1 255 =
    WordByteView.Tests.expected [1, 0, 0, 128] [1, 255, 0, 128] 2147548929 := by decide +kernel
theorem case_3_2_little : observe .little 2147483649 2 18 =
    WordByteView.Tests.expected [1, 0, 0, 128] [1, 0, 18, 128] 2148663297 := by decide +kernel
theorem case_3_3_little : observe .little 2147483649 3 129 =
    WordByteView.Tests.expected [1, 0, 0, 128] [1, 0, 0, 129] 2164260865 := by decide +kernel
theorem case_0_0_big : observe .big 0 0 0 =
    WordByteView.Tests.expected [0, 0, 0, 0] [0, 0, 0, 0] 0 := by decide +kernel
theorem case_0_1_big : observe .big 0 1 255 =
    WordByteView.Tests.expected [0, 0, 0, 0] [0, 255, 0, 0] 16711680 := by decide +kernel
theorem case_0_2_big : observe .big 0 2 18 =
    WordByteView.Tests.expected [0, 0, 0, 0] [0, 0, 18, 0] 4608 := by decide +kernel
theorem case_0_3_big : observe .big 0 3 129 =
    WordByteView.Tests.expected [0, 0, 0, 0] [0, 0, 0, 129] 129 := by decide +kernel
theorem case_1_0_big : observe .big 4294967295 0 0 =
    WordByteView.Tests.expected [255, 255, 255, 255] [0, 255, 255, 255] 16777215 := by decide +kernel
theorem case_1_1_big : observe .big 4294967295 1 255 =
    WordByteView.Tests.expected [255, 255, 255, 255] [255, 255, 255, 255] 4294967295 := by decide +kernel
theorem case_1_2_big : observe .big 4294967295 2 18 =
    WordByteView.Tests.expected [255, 255, 255, 255] [255, 255, 18, 255] 4294906623 := by decide +kernel
theorem case_1_3_big : observe .big 4294967295 3 129 =
    WordByteView.Tests.expected [255, 255, 255, 255] [255, 255, 255, 129] 4294967169 := by decide +kernel
theorem case_2_0_big : observe .big 3735928559 0 0 =
    WordByteView.Tests.expected [222, 173, 190, 239] [0, 173, 190, 239] 11386607 := by decide +kernel
theorem case_2_1_big : observe .big 3735928559 1 255 =
    WordByteView.Tests.expected [222, 173, 190, 239] [222, 255, 190, 239] 3741302511 := by decide +kernel
theorem case_2_2_big : observe .big 3735928559 2 18 =
    WordByteView.Tests.expected [222, 173, 190, 239] [222, 173, 18, 239] 3735884527 := by decide +kernel
theorem case_2_3_big : observe .big 3735928559 3 129 =
    WordByteView.Tests.expected [222, 173, 190, 239] [222, 173, 190, 129] 3735928449 := by decide +kernel
theorem case_3_0_big : observe .big 2147483649 0 0 =
    WordByteView.Tests.expected [128, 0, 0, 1] [0, 0, 0, 1] 1 := by decide +kernel
theorem case_3_1_big : observe .big 2147483649 1 255 =
    WordByteView.Tests.expected [128, 0, 0, 1] [128, 255, 0, 1] 2164195329 := by decide +kernel
theorem case_3_2_big : observe .big 2147483649 2 18 =
    WordByteView.Tests.expected [128, 0, 0, 1] [128, 0, 18, 1] 2147488257 := by decide +kernel
theorem case_3_3_big : observe .big 2147483649 3 129 =
    WordByteView.Tests.expected [128, 0, 0, 1] [128, 0, 0, 129] 2147483777 := by decide +kernel

end Compiler.ZigAir.Memory.ByteAccess.Tests
