/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapArgumentScan
import Compiler.ZigAir.MemoryWordBytes

namespace Compiler.Extraction.ExpressionMap.ArgumentScan
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryMemory (readId_of_load)

def encoded (values : Nat → BitVec 32) (start offset : Nat) : BitVec 8 :=
  Compiler.ZigAir.WordBytes.read .little (values (start + offset / 4)) ⟨offset % 4, by omega⟩

/-- All sixteen lanes of an actual SIMD read, through the existing initialized
word-byte view. Bytes of padding or pointers are never synthesized. -/
def bytes (state : State) (source : View) (start : Nat) (offsets : List Nat) : Except Fault (List (BitVec 8)) :=
  offsets.mapM (fun offset => WordByteView.read .little state (source.pointer (start + offset / 4)) (offset % 4))

def vector (state : State) (left right : View) (start : Nat) : Except Fault Bool := do
  let a ← bytes state left start (List.range 16)
  let b ← bytes state right start (List.range 16)
  .ok (decide (a = b))

def vectors (state : State) (left right : View) : List Nat → Except Fault Bool
  | [] => .ok true
  | start :: rest => do
    let equal ← vector state left right start
    if equal then vectors state left right rest else .ok false

theorem bytes_verified (state : State) (source : View) (start : Nat) (offsets : List Nat) (values : Nat → BitVec 32)
    (reads : ∀ offset ∈ offsets, load state (source.pointer (start + offset / 4)) = .ok (number (values (start + offset / 4)))) :
    bytes state source start offsets = .ok (offsets.map (encoded values start)) := by
  induction offsets with
  | nil => rfl
  | cons head tail ih =>
    have read := WordByteView.read_word .little state (source.pointer (start + head / 4))
      ⟨head % 4, by omega⟩ (values (start + head / 4)) (reads head (by simp))
    have rest := ih (fun offset member => reads offset (by simp [member]))
    simp only [bytes] at rest ⊢
    simp only [List.mapM_cons, read, rest, bind, Except.bind, pure, Except.pure, List.map_cons, encoded]

/-- Byte-lane equality determines every u32 in the chunk. This uses the proved
byte codec, rather than assuming that a byte-vector equality callback is correct. -/
theorem encoded_equal (a b : Nat → BitVec 32) (start : Nat) :
    (List.range 16).map (encoded a start) = (List.range 16).map (encoded b start) ↔
      ∀ i ∈ chunk start, a i = b i := by
  rw [List.map_inj_left]
  constructor
  · intro same i inside
    have bounds := (chunk_mem start i).mp inside
    apply Compiler.ZigAir.WordBytes.ext .little
    intro lane
    have laneBound := lane.isLt
    have offsetBound : (i - start) * 4 + lane.val < 16 := by omega
    have eq := same ((i - start) * 4 + lane.val) (List.mem_range.mpr offsetBound)
    have word : start + ((i - start) * 4 + lane.val) / 4 = i := by omega
    have byte : ((i - start) * 4 + lane.val) % 4 = lane.val := by omega
    simpa only [encoded, word, byte] using eq
  · intro same offset member
    have bound := List.mem_range.mp member
    have inside : start + offset / 4 ∈ chunk start := (chunk_mem _ _).mpr (by omega)
    simp only [encoded, same _ inside]

theorem vector_difference (state : State) (left right : View) (start : Nat) (a b : Nat → BitVec 32)
    (reads : ∀ i ∈ chunk start, load state (left.pointer i) = .ok (number (a i)) ∧
      load state (right.pointer i) = .ok (number (b i))) :
    ∃ value, difference state left right (chunk start) = .ok value ∧
      vector state left right start = .ok (decide (value = 0)) := by
  have lanes (offset : Nat) (member : offset ∈ List.range 16) : start + offset / 4 ∈ chunk start := by
    have := List.mem_range.mp member
    exact (chunk_mem _ _).mpr (by omega)
  have ar := bytes_verified state left start (List.range 16) a (fun offset member => (reads _ (lanes offset member)).1)
  have br := bytes_verified state right start (List.range 16) b (fun offset member => (reads _ (lanes offset member)).2)
  obtain ⟨value, ran, equal⟩ := difference_verified state left right (chunk start) a b (by
    intro i member
    exact ⟨readId_of_load _ _ _ _ (reads i member).1, readId_of_load _ _ _ _ (reads i member).2⟩)
  refine ⟨value, ran, ?_⟩
  have same : ((List.range 16).map (encoded a start) = (List.range 16).map (encoded b start)) = (value = 0) :=
    propext ((encoded_equal a b start).trans equal.symm)
  simp only [vector, ar, br, bind, Except.bind, same]

theorem vectors_eq_scan (state : State) (left right : View) (starts : List Nat) (a b : Nat → BitVec 32)
    (reads : ∀ start ∈ starts, ∀ i ∈ chunk start, load state (left.pointer i) = .ok (number (a i)) ∧
      load state (right.pointer i) = .ok (number (b i))) :
    vectors state left right starts = scan state left right (starts.map chunk) := by
  induction starts with
  | nil => rfl
  | cons start rest ih =>
    obtain ⟨value, difference, vector⟩ := vector_difference state left right start a b (reads start (by simp))
    have tail := ih (fun start member => reads start (by simp [member]))
    simp only [vectors, scan, List.map_cons, difference, vector, bind, Except.bind, tail, decide_eq_true_eq]

end Compiler.Extraction.ExpressionMap.ArgumentScan
