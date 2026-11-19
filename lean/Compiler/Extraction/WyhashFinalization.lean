/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.WyhashLocal
import Compiler.ZigAir.MemoryByteSlice

set_option maxRecDepth 4096

namespace Compiler.Extraction.WyhashFinalization
open Compiler.ZigAir.Memory WyhashLocal

def final0 (ops : Ops) (cells : Cells) : Except Fault Cells := do
  let s0 ← ops.read cells 2
  let s1 ← ops.read cells 3
  let s2 ← ops.read cells 4
  ops.write cells 2 (s0 ^^^ (s1 ^^^ s2))

def round (ops : Ops) (input : Cells) (view : ByteSlice.View) (offset : Nat) (cells : Cells) : Except Fault Cells := do
  let a ← ByteSlice.readLE input view offset 8
  let b ← ByteSlice.readLE input view (offset + 8) 8
  let s0 ← ops.read cells 2
  ops.write cells 2 (mix (a ^^^ secret1) (b ^^^ s0))

/-- The native strict loop condition and 16-byte induction, with no supplied
iteration schedule or fuel. The local slice already retains its actual extent. -/
def loop (ops : Ops) (input : Cells) (view : ByteSlice.View) (start index : Nat) (cells : Cells) : Except Fault Cells :=
  if index + 16 < view.length - start then do
    let after ← round ops input view (start + index) cells
    loop ops input view start (index + 16) after
  else .ok cells
termination_by view.length - start - index
decreasing_by omega

def rounds (bytes : Nat → BitVec 8) (length start index : Nat) (state : BitVec 64) : BitVec 64 :=
  if index + 16 < length - start then
    rounds bytes length start (index + 16)
      (mix (ByteSlice.decode bytes (start + index) 8 ^^^ secret1)
        (ByteSlice.decode bytes (start + index + 8) 8 ^^^ state))
  else state
termination_by length - start - index
decreasing_by omega

/-- Keep the two tail loads and writes in source order. The copied core and
input are distinct local objects, so writes cannot change the input bytes. -/
def tail (ops : Ops) (input : Cells) (view : ByteSlice.View) (cells : Cells) : Except Fault (BitVec 64) := do
  let a ← ByteSlice.readLE input view (view.length - 16) 8
  let cells ← ops.write cells 0 a
  let b ← ByteSlice.readLE input view (view.length - 8) 8
  let cells ← ops.write cells 1 b
  final2 ops cells

def finish (ops : Ops) (input : Cells) (view : ByteSlice.View) (start : Nat) (cells : Cells) : Except Fault (BitVec 64) := do
  if view.length < 16 ∨ view.length < start ∨ 48 < view.length - start then .error .sourceBounds else
  let cells ← final0 ops cells
  let cells ← loop ops input view start 0 cells
  tail ops input view cells

def result (bytes : Nat → BitVec 8) (length start : Nat) (s0 s1 s2 total : BitVec 64) : BitVec 64 :=
  WyhashLocal.result (ByteSlice.decode bytes (length - 16) 8) (ByteSlice.decode bytes (length - 8) 8)
    (rounds bytes length start 0 (s0 ^^^ (s1 ^^^ s2))) total

theorem final0_verified (cells : Cells) (s0 s1 s2 total : BitVec 64)
    (h0 : cells.lookup 16 = some (word s0)) (h1 : cells.lookup 24 = some (word s1))
    (h2 : cells.lookup 32 = some (word s2)) (ht : cells.lookup 40 = some (word total)) :
    ∃ after, final0 localOps cells = .ok after ∧
      after.lookup 16 = some (word (s0 ^^^ (s1 ^^^ s2))) ∧ after.lookup 40 = some (word total) := by
  refine ⟨cells.set 16 (word (s0 ^^^ (s1 ^^^ s2))), ?_, Cells.lookup_set .., ?_⟩
  · simp only [final0, localOps, show 8 * (2 : Fin 6).val = 16 from rfl,
      show 8 * (3 : Fin 6).val = 24 from rfl, show 8 * (4 : Fin 6).val = 32 from rfl,
      read_word _ _ _ h0, read_word _ _ _ h1, read_word _ _ _ h2,
      write_word _ 16 _ (by decide), bind, Except.bind]
  · simpa only [Cells.lookup_set_other _ _ _ _ (by decide : 40 ≠ 16)] using ht

theorem round_verified (input cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents input view bytes)
    (offset : Nat) (bound : offset + 16 ≤ view.length) (state total : BitVec 64)
    (hs : cells.lookup 16 = some (word state)) (ht : cells.lookup 40 = some (word total)) :
    ∃ after, round localOps input view offset cells = .ok after ∧
      after.lookup 16 = some (word (mix (ByteSlice.decode bytes offset 8 ^^^ secret1)
        (ByteSlice.decode bytes (offset + 8) 8 ^^^ state))) ∧ after.lookup 40 = some (word total) := by
  refine ⟨cells.set 16 (word (mix (ByteSlice.decode bytes offset 8 ^^^ secret1)
    (ByteSlice.decode bytes (offset + 8) 8 ^^^ state))), ?_, Cells.lookup_set .., ?_⟩
  · simp only [round, ByteSlice.readLE_verified input view bytes geometry represented offset 8 (by omega),
      ByteSlice.readLE_verified input view bytes geometry represented (offset + 8) 8 (by omega),
      localOps, show 8 * (2 : Fin 6).val = 16 from rfl, read_word _ _ _ hs,
      write_word _ 16 _ (by decide), bind, Except.bind]
  · simpa only [Cells.lookup_set_other _ _ _ _ (by decide : 40 ≠ 16)] using ht

theorem loop_verified (input cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents input view bytes)
    (start index : Nat) (state total : BitVec 64)
    (hs : cells.lookup 16 = some (word state)) (ht : cells.lookup 40 = some (word total)) :
    ∃ after, loop localOps input view start index cells = .ok after ∧
      after.lookup 16 = some (word (rounds bytes view.length start index state)) ∧
      after.lookup 40 = some (word total) := by
  rw [loop, rounds]
  by_cases more : index + 16 < view.length - start
  · rw [if_pos more, if_pos more]
    obtain ⟨middle, ran, ms, mt⟩ := round_verified input cells view bytes geometry represented
      (start + index) (by omega) state total hs ht
    obtain ⟨after, finished, resultState, resultTotal⟩ := loop_verified input middle view bytes geometry represented
      start (index + 16) _ total ms mt
    exact ⟨after, by simp only [ran, bind, Except.bind, finished], resultState, resultTotal⟩
  · exact ⟨cells, by simp only [if_neg more], by simpa only [if_neg more] using hs, ht⟩
termination_by view.length - start - index
decreasing_by omega

theorem tail_of_reads (ops : Ops) (input cells : Cells) (view : ByteSlice.View) (a b : BitVec 64)
    (readA : ByteSlice.readLE input view (view.length - 16) 8 = .ok a)
    (readB : ByteSlice.readLE input view (view.length - 8) 8 = .ok b) :
    tail ops input view cells = finishTail ops cells a b := by
  simp only [tail, readA, readB, finishTail, overwriteTail, bind]
  cases first : ops.write cells 0 a <;> simp only [Except.bind, first]

theorem tail_verified (input cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents input view bytes)
    (long : 16 ≤ view.length) (state total : BitVec 64)
    (hs : cells.lookup 16 = some (word state)) (ht : cells.lookup 40 = some (word total)) :
    tail localOps input view cells = .ok (WyhashLocal.result
      (ByteSlice.decode bytes (view.length - 16) 8) (ByteSlice.decode bytes (view.length - 8) 8) state total) := by
  exact (tail_of_reads localOps input cells view _ _
    (ByteSlice.readLE_verified input view bytes geometry represented (view.length - 16) 8 (by omega))
    (ByteSlice.readLE_verified input view bytes geometry represented (view.length - 8) 8 (by omega))).trans
    (finishTail_verified cells _ _ state total hs ht)

/-- Native operations are derived, not an assumed callback. The source bytes
determine both the loop's state and the final pair consumed by the existing tail. -/
theorem finish_verified (input cells : Cells) (view : ByteSlice.View) (bytes : Nat → BitVec 8)
    (geometry : ByteSlice.Geometry view) (represented : ByteSlice.Represents input view bytes)
    (start : Nat) (long : 16 ≤ view.length) (starts : start ≤ view.length) (bounded : view.length - start ≤ 48)
    (s0 s1 s2 total : BitVec 64)
    (h0 : cells.lookup 16 = some (word s0)) (h1 : cells.lookup 24 = some (word s1))
    (h2 : cells.lookup 32 = some (word s2)) (ht : cells.lookup 40 = some (word total)) :
    finish nativeOps input view start cells = .ok (result bytes view.length start s0 s1 s2 total) := by
  rw [nativeOps_eq]
  obtain ⟨middle, first, ms, mt⟩ := final0_verified cells s0 s1 s2 total h0 h1 h2 ht
  obtain ⟨after, ran, hs, ht⟩ := loop_verified input middle view bytes geometry represented start 0 _ total ms mt
  simp only [finish, if_neg (by omega : ¬(view.length < 16 ∨ view.length < start ∨ 48 < view.length - start)),
    first, ran, bind, Except.bind]
  exact tail_verified input after view bytes geometry represented long _ total hs ht

end Compiler.Extraction.WyhashFinalization
