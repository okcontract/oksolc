/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerTemporaryMemory

namespace Compiler.Extraction.ExpressionMap.ArgumentScan
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryMemory (readId)

/-- The four u32 reads in the short eqlBytes branch, expressed in word offsets.
The source uses byte offsets [0, bytes-4, (bytes/8)*4,
bytes-4-(bytes/8)*4]. The admission profile binds sizeof(Id)=4. -/
def short (length : Nat) : List Nat := [0, length - 1, length / 2, length - 1 - length / 2]

def chunk (start : Nat) : List Nat := [start, start + 1, start + 2, start + 3]

/-- For the captured 16-byte SIMD scan: preceding complete chunks, then the
last overlapping chunk. This is the source's (bytes-1)/Scan.size loop bound. -/
def blocks (length : Nat) : List (List Nat) :=
  if length ≤ 4 then [short length]
  else (List.range ((length * 4 - 1) / 16)).map (fun i => chunk (i * 4)) ++ [chunk (length - 4)]

theorem short_offsets (length : Nat) (positive : 0 < length) :
    [0, length * 4 - 4, (length * 4 / 8) * 4, length * 4 - 4 - (length * 4 / 8) * 4] =
      (short length).map (· * 4) := by
  have half : length * 4 / 8 = length / 2 := by omega
  simp [short, half]
  omega

theorem chunk_mem (start i : Nat) : i ∈ chunk start ↔ start ≤ i ∧ i < start + 4 := by
  simp [chunk]
  omega

theorem short_mem (length i : Nat) (positive : 0 < length) (small : length ≤ 4) :
    i ∈ short length ↔ i < length := by
  have cases : length = 1 ∨ length = 2 ∨ length = 3 ∨ length = 4 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> simp [short] <;> omega

/-- The exact overlapping schedule reads every word and no word outside the
slice. A shortened or shifted final chunk cannot satisfy this property. -/
theorem coverage (length i : Nat) (positive : 0 < length) :
    (∃ block ∈ blocks length, i ∈ block) ↔ i < length := by
  by_cases small : length ≤ 4
  · simpa [blocks, small] using short_mem length i positive small
  · have large : 4 < length := by omega
    simp only [blocks, if_neg small, List.mem_append, List.mem_map, List.mem_singleton]
    constructor
    · rintro ⟨block, first | rfl, member⟩
      · obtain ⟨j, bound, rfl⟩ := first
        have := (chunk_mem (j * 4) i).mp member
        simp only [List.mem_range] at bound
        omega
      · have := (chunk_mem (length - 4) i).mp member
        omega
    · intro inside
      by_cases last : length - 4 ≤ i
      · exact ⟨chunk (length - 4), Or.inr rfl, (chunk_mem _ _).mpr (by omega)⟩
      · exact ⟨chunk (i / 4 * 4), Or.inl ⟨i / 4, List.mem_range.mpr (by omega), rfl⟩,
          (chunk_mem _ _).mpr (by omega)⟩

/-- The small-branch XOR/OR reduction and the equivalent scalar view of a
16-byte SIMD comparison. Every operand comes from the existing typed load. -/
def difference (state : State) (left right : View) : List Nat → Except Fault (BitVec 32)
  | [] => .ok 0
  | index :: rest => do
    let a ← readId state left index
    let b ← readId state right index
    let tail ← difference state left right rest
    .ok ((a ^^^ b) ||| tail)

def scan (state : State) (left right : View) : List (List Nat) → Except Fault Bool
  | [] => .ok true
  | block :: rest => do
    let value ← difference state left right block
    if value = 0 then scan state left right rest else .ok false

theorem difference_verified (state : State) (left right : View) (indices : List Nat)
    (a b : Nat → BitVec 32)
    (reads : ∀ i ∈ indices, readId state left i = .ok (a i) ∧
      readId state right i = .ok (b i)) :
    ∃ value, difference state left right indices = .ok value ∧
      (value = 0 ↔ ∀ i ∈ indices, a i = b i) := by
  induction indices with
  | nil => exact ⟨0, rfl, by simp⟩
  | cons head tail ih =>
    obtain ⟨value, ran, equal⟩ := ih (fun i member => reads i (by simp [member]))
    obtain ⟨ra, rb⟩ := reads head (by simp)
    refine ⟨(a head ^^^ b head) ||| value, ?_, ?_⟩
    · simp only [difference, ra, rb, ran, bind, Except.bind]
    · rw [List.forall_mem_cons]
      exact BitVec.or_eq_zero_iff.trans (and_congr BitVec.xor_eq_zero_iff equal)

theorem scan_verified (state : State) (left right : View) (schedule : List (List Nat))
    (a b : Nat → BitVec 32)
    (reads : ∀ block ∈ schedule, ∀ i ∈ block, readId state left i = .ok (a i) ∧
      readId state right i = .ok (b i)) :
    ∃ result, scan state left right schedule = .ok result ∧
      (result = true ↔ ∀ block ∈ schedule, ∀ i ∈ block, a i = b i) := by
  induction schedule with
  | nil => exact ⟨true, rfl, by simp⟩
  | cons block rest ih =>
    obtain ⟨value, ran, equal⟩ := difference_verified state left right block a b (reads block (by simp))
    by_cases zero : value = 0
    · obtain ⟨result, scanned, complete⟩ := ih (fun block member => reads block (by simp [member]))
      refine ⟨result, by simp only [scan, ran, bind, Except.bind, if_pos zero, scanned], ?_⟩
      constructor
      · intro yes selected member
        rcases List.mem_cons.mp member with rfl | member
        · exact equal.mp zero
        · exact complete.mp yes selected member
      · intro all
        exact complete.mpr (fun selected member => all selected (by simp [member]))
    · refine ⟨false, by simp only [scan, ran, bind, Except.bind, if_neg zero], ?_⟩
      constructor
      · intro impossible; cases impossible
      · intro all
        exact False.elim (zero (equal.mpr (all block (by simp))))

end Compiler.Extraction.ExpressionMap.ArgumentScan
