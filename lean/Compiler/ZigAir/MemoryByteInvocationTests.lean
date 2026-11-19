/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryByteInvocation
import Compiler.ZigAir.MemoryByteAccessTests

namespace Compiler.ZigAir.MemoryByteInvocation
open Memory MemoryAir GeneratedMemory
open Memory.WordArray (word)

-- The imported symbolic results establish functional refinement and caller
-- framing under initialized-view premises. These general validity results and
-- closed observations also retain malformed-input and failure coverage.
theorem read_preserves_valid (args : List Value) (state : State) (initial : state.valid = true) :
    (fn_read_word_byte.run args state).2.valid = true :=
  Program.preserves_valid fn_read_word_byte args state initial

theorem write_preserves_valid (args : List Value) (state : State) (initial : state.valid = true) :
    (fn_write_word_byte.run args state).2.valid = true :=
  Program.preserves_valid fn_write_word_byte args state initial

namespace Tests
abbrev caller := WordByteView.Tests.caller
abbrev empty := WordByteView.Tests.empty
abbrev readonly := WordByteView.Tests.readonly

def readArgs (index : Nat) : List Value :=
  [.pointer (.pointer false false word) ⟨0, 4⟩, .scalar (.int false 64 index)]
def writeArgs (index : Nat) (byte : BitVec 8) : List Value :=
  [.pointer (.pointer true false word) ⟨0, 4⟩, .scalar (.int false 64 index), ByteAccess.number byte]

def readByte (state : State) (index : Nat) : Except Fault (BitVec 8) := do
  let .scalar (.int false 8 value) ← (fn_read_word_byte.run (readArgs index) state).1 | .error .malformed
  .ok (BitVec.ofInt 8 value)

def bytes (state : State) : List (Except Fault (BitVec 8)) := (List.range 4).map (readByte state)
def readHeaps (state : State) : List Bool :=
  (List.range 4).map (fun index => (fn_read_word_byte.run (readArgs index) state).2.heap == state.heap)

structure Observation where
  bytes : WordByteView.Tests.Observation
  readHeaps : List Bool
  after : State
  deriving DecidableEq, Repr

def observe (value : BitVec 32) (index : Nat) (byte : BitVec 8) : Observation :=
  let before := caller value
  let (result, after) := fn_write_word_byte.run (writeArgs index byte) before
  let status := match result with | .ok (.scalar .unit) => .ok () | .ok _ => .error .malformed | .error reason => .error reason
  ⟨⟨bytes before, status, WordByteView.Tests.words after, bytes after⟩, readHeaps before ++ readHeaps after, after⟩

def writtenHeap (value : BitVec 32) : Heap :=
  [(0, { WordByteView.Tests.cell value with cells :=
    [(4, WordArray.number value), (0, WordArray.number 3735928559), (8, WordArray.number 3131961357)] })]

def expected (before after : List (BitVec 8)) (value : BitVec 32) : Observation :=
  ⟨WordByteView.Tests.expected before after value, List.replicate 8 true, ⟨writtenHeap value, 2, 48⟩⟩

theorem read_uninitialized : fn_read_word_byte.run (readArgs 0) empty =
    (.error .uninitialized, ⟨empty.heap, 2, 48⟩) := by decide +kernel
theorem write_uninitialized : fn_write_word_byte.run (writeArgs 0 255) empty =
    (.error .uninitialized, ⟨empty.heap, 2, 48⟩) := by decide +kernel
theorem readonly_read : fn_read_word_byte.run (readArgs 0) readonly =
    (.ok (ByteAccess.number 0), ⟨readonly.heap, 2, 48⟩) := by decide +kernel
theorem readonly_write : fn_write_word_byte.run (writeArgs 0 255) readonly =
    (.error .readOnly, ⟨readonly.heap, 2, 48⟩) := by decide +kernel
theorem read_exact_bound : fn_read_word_byte.run (readArgs 4) (caller 0) =
    (.error .sourceBounds, ⟨(caller 0).heap, 2, 48⟩) := by decide +kernel
theorem write_exact_bound : fn_write_word_byte.run (writeArgs 4 255) (caller 0) =
    (.error .sourceBounds, ⟨(caller 0).heap, 2, 48⟩) := by decide +kernel

def exhausted : State := { caller 0 with nextAddress := addressLimit }
theorem valid_exhausted : exhausted.valid = true := by decide +kernel
theorem read_allocation_exhausted : fn_read_word_byte.run (readArgs 0) exhausted =
    (.error .outOfMemory, exhausted) := by decide +kernel
theorem write_allocation_exhausted : fn_write_word_byte.run (writeArgs 0 255) exhausted =
    (.error .outOfMemory, exhausted) := by decide +kernel
theorem dead_read : fn_read_word_byte.run (readArgs 0) {} = (.error .unallocated, {}) := by decide +kernel
theorem dead_write : fn_write_word_byte.run (writeArgs 0 255) {} = (.error .unallocated, {}) := by decide +kernel
theorem const_write_argument : fn_write_word_byte.run
    [.pointer (.pointer false false word) ⟨0, 4⟩, .scalar (.int false 64 0), ByteAccess.number 1] (caller 0) =
    (.error .malformed, caller 0) := by decide +kernel

/-- A concrete inhabited caller discharges every premise of the universal read. -/
theorem read_total_witness :
    ∃ result after, fn_read_word_byte.run (readArgs 1) (caller 305419896) = (result, after) ∧
      after.valid = true ∧ after.heap = (caller 305419896).heap ∧
      (result = .ok (ByteAccess.number 86) ∨ result = .error .outOfMemory) := by
  have checked := read_result (caller 305419896) WordByteView.Tests.view [305419896] 0 1
    WordByteView.Tests.valid_caller WordByteView.Tests.writable_caller WordByteView.Tests.represented_caller (by decide)
  have byte : WordBytes.read .little (305419896 : BitVec 32) 1 = 86 := by decide +kernel
  simpa only [List.getElem_cons_zero, byte] using checked

/-- The universal write theorem supplies the list relation; a concrete run
rules out exhaustion for this caller without adding a premise to that theorem. -/
theorem write_total_witness :
    ∃ after, fn_write_word_byte.run (writeArgs 1 255) (caller 305419896) = (.ok (.scalar .unit), after) ∧
      after.valid = true ∧ WordArray.Represents after WordByteView.Tests.view [305463160] := by
  obtain ⟨result, after, ran, valid, outcome⟩ :=
    write_result (caller 305419896) WordByteView.Tests.view [305419896] 0 1 255
      WordByteView.Tests.valid_caller WordByteView.Tests.writable_caller WordByteView.Tests.represented_caller (by decide)
  have executed : fn_write_word_byte.run (writeArgs 1 255) (caller 305419896) =
      (.ok (.scalar .unit), ⟨writtenHeap 305463160, 2, 48⟩) := by decide +kernel
  have resultEq : result = .ok (.scalar .unit) := (Prod.mk.inj (ran.symm.trans executed)).1
  refine ⟨after, by simpa only [resultEq] using ran, valid, ?_⟩
  rcases outcome with ⟨failed, _⟩ | ⟨direct, _, _, _, _, represented, _⟩
  · rw [resultEq] at failed
    cases failed
  · change WordArray.Represents after WordByteView.Tests.view [WordBytes.write .little 305419896 1 255] at represented
    have computed : WordBytes.write .little (305419896 : BitVec 32) 1 255 = 305463160 := by decide +kernel
    rw [computed] at represented
    exact represented

theorem case_0_0 : observe 0 0 0 =
    expected [0, 0, 0, 0] [0, 0, 0, 0] 0 := by
  have written : fn_write_word_byte.run (writeArgs 0 0) (caller 0) =
      (.ok (.scalar .unit), ⟨writtenHeap 0, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_0_1 : observe 0 1 255 =
    expected [0, 0, 0, 0] [0, 255, 0, 0] 65280 := by
  have written : fn_write_word_byte.run (writeArgs 1 255) (caller 0) =
      (.ok (.scalar .unit), ⟨writtenHeap 65280, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_0_2 : observe 0 2 18 =
    expected [0, 0, 0, 0] [0, 0, 18, 0] 1179648 := by
  have written : fn_write_word_byte.run (writeArgs 2 18) (caller 0) =
      (.ok (.scalar .unit), ⟨writtenHeap 1179648, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_0_3 : observe 0 3 129 =
    expected [0, 0, 0, 0] [0, 0, 0, 129] 2164260864 := by
  have written : fn_write_word_byte.run (writeArgs 3 129) (caller 0) =
      (.ok (.scalar .unit), ⟨writtenHeap 2164260864, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_1_0 : observe 4294967295 0 0 =
    expected [255, 255, 255, 255] [0, 255, 255, 255] 4294967040 := by
  have written : fn_write_word_byte.run (writeArgs 0 0) (caller 4294967295) =
      (.ok (.scalar .unit), ⟨writtenHeap 4294967040, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_1_1 : observe 4294967295 1 255 =
    expected [255, 255, 255, 255] [255, 255, 255, 255] 4294967295 := by
  have written : fn_write_word_byte.run (writeArgs 1 255) (caller 4294967295) =
      (.ok (.scalar .unit), ⟨writtenHeap 4294967295, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_1_2 : observe 4294967295 2 18 =
    expected [255, 255, 255, 255] [255, 255, 18, 255] 4279435263 := by
  have written : fn_write_word_byte.run (writeArgs 2 18) (caller 4294967295) =
      (.ok (.scalar .unit), ⟨writtenHeap 4279435263, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_1_3 : observe 4294967295 3 129 =
    expected [255, 255, 255, 255] [255, 255, 255, 129] 2181038079 := by
  have written : fn_write_word_byte.run (writeArgs 3 129) (caller 4294967295) =
      (.ok (.scalar .unit), ⟨writtenHeap 2181038079, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_2_0 : observe 3735928559 0 0 =
    expected [239, 190, 173, 222] [0, 190, 173, 222] 3735928320 := by
  have written : fn_write_word_byte.run (writeArgs 0 0) (caller 3735928559) =
      (.ok (.scalar .unit), ⟨writtenHeap 3735928320, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_2_1 : observe 3735928559 1 255 =
    expected [239, 190, 173, 222] [239, 255, 173, 222] 3735945199 := by
  have written : fn_write_word_byte.run (writeArgs 1 255) (caller 3735928559) =
      (.ok (.scalar .unit), ⟨writtenHeap 3735945199, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_2_2 : observe 3735928559 2 18 =
    expected [239, 190, 173, 222] [239, 190, 18, 222] 3725770479 := by
  have written : fn_write_word_byte.run (writeArgs 2 18) (caller 3735928559) =
      (.ok (.scalar .unit), ⟨writtenHeap 3725770479, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_2_3 : observe 3735928559 3 129 =
    expected [239, 190, 173, 222] [239, 190, 173, 129] 2175647471 := by
  have written : fn_write_word_byte.run (writeArgs 3 129) (caller 3735928559) =
      (.ok (.scalar .unit), ⟨writtenHeap 2175647471, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_3_0 : observe 2147483649 0 0 =
    expected [1, 0, 0, 128] [0, 0, 0, 128] 2147483648 := by
  have written : fn_write_word_byte.run (writeArgs 0 0) (caller 2147483649) =
      (.ok (.scalar .unit), ⟨writtenHeap 2147483648, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_3_1 : observe 2147483649 1 255 =
    expected [1, 0, 0, 128] [1, 255, 0, 128] 2147548929 := by
  have written : fn_write_word_byte.run (writeArgs 1 255) (caller 2147483649) =
      (.ok (.scalar .unit), ⟨writtenHeap 2147548929, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_3_2 : observe 2147483649 2 18 =
    expected [1, 0, 0, 128] [1, 0, 18, 128] 2148663297 := by
  have written : fn_write_word_byte.run (writeArgs 2 18) (caller 2147483649) =
      (.ok (.scalar .unit), ⟨writtenHeap 2148663297, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

theorem case_3_3 : observe 2147483649 3 129 =
    expected [1, 0, 0, 128] [1, 0, 0, 129] 2164260865 := by
  have written : fn_write_word_byte.run (writeArgs 3 129) (caller 2147483649) =
      (.ok (.scalar .unit), ⟨writtenHeap 2164260865, 2, 48⟩) := by decide +kernel
  dsimp only [observe]
  rw [written]
  decide +kernel

end Tests
end Compiler.ZigAir.MemoryByteInvocation
