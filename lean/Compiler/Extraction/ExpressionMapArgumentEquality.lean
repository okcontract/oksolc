/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapArgumentVector

namespace Compiler.Extraction.ExpressionMap.ArgumentScan
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.TemporaryMemory (readId readId_of_load)

def starts (length : Nat) : List Nat :=
  (List.range ((length * 4 - 1) / 16)).map (· * 4) ++ [length - 4]

theorem blocks_large (length : Nat) (large : ¬length ≤ 4) : blocks length = (starts length).map chunk := by
  simp only [blocks, if_neg large, starts, List.map_append, List.map_map, List.map_cons, List.map_nil]
  rfl

def nativeScan (state : State) (left right : View) : Except Fault Bool :=
  if left.length ≤ 4 then scan state left right [short left.length]
  else vectors state left right (starts left.length)

/-- The admitted runtime u32 specialization of std.mem.eql/eqlBytes, including
its length, empty and identical-pointer shortcuts. The source profile supplies
the 16-byte scan choice; arithmetic admission is derived separately. -/
def run (state : State) (left right : View) : Except Fault Bool :=
  if ¬(left.length * 4 < addressLimit ∧ right.length * 4 < addressLimit) then .error .memoryValidity
  else if left.length ≠ right.length then .ok false
  else if left.length = 0 ∨ left.address 0 = right.address 0 then .ok true
  else nativeScan state left right

theorem different_lengths (state : State) (left right : View) (different : left.length ≠ right.length)
    (bounded : left.length * 4 < addressLimit ∧ right.length * 4 < addressLimit) :
    run state left right = .ok false := by simp only [run, if_neg (not_not_intro bounded), if_pos different]

theorem empty (state : State) (left right : View) (leftEmpty : left.length = 0) (rightEmpty : right.length = 0) :
    run state left right = .ok true := by simp [run, leftEmpty, rightEmpty, addressLimit]

theorem same_pointer (state : State) (left right : View) (length : left.length = right.length)
    (same : left.address 0 = right.address 0) (bounded : left.length * 4 < addressLimit) : run state left right = .ok true := by
  have both : left.length * 4 < addressLimit ∧ right.length * 4 < addressLimit := ⟨bounded, length ▸ bounded⟩
  simp [run, both, length, same]

theorem represented_alias (state : State) (left right : View) (a b : List (BitVec 32))
    (leftRead : Represents state left a) (rightRead : Represents state right b)
    (length : left.length = right.length) (same : left.address 0 = right.address 0) : a = b := by
  have addresses : ∀ i, left.pointer i = right.pointer i := by
    have allocation := congrArg Address.allocation same
    have offset := congrArg Address.offset same
    simp only [View.address, Nat.add_zero] at allocation offset
    have first : left.first = right.first := by omega
    intro i
    simp only [View.pointer, View.address, allocation, first]
  apply List.ext_getElem (leftRead.1.trans (length.trans rightRead.1.symm))
  intro i ha hb
  have ra := leftRead.2 i ha
  have rb := rightRead.2 i hb
  rw [addresses] at ra
  exact BitVec.eq_of_toNat_eq (Int.ofNat.inj (by simpa [number] using Except.ok.inj (ra.symm.trans rb)))

/-- Equality is derived from initialized native reads. No correct comparison
callback, logical equality result or successful scan is supplied. -/
theorem run_verified (state : State) (left right : View) (a b : List (BitVec 32))
    (leftRead : Represents state left a) (rightRead : Represents state right b)
    (bounded : left.length * 4 < addressLimit ∧ right.length * 4 < addressLimit) :
    run state left right = .ok (decide (a = b)) := by
  simp only [run, if_neg (not_not_intro bounded)]
  have leftLength := leftRead.1
  have rightLength := rightRead.1
  by_cases length : left.length = right.length
  · by_cases shortcut : left.length = 0 ∨ left.address 0 = right.address 0
    · have equal : a = b := by
        rcases shortcut with zero | same
        · have az : a = [] := List.eq_nil_of_length_eq_zero (leftRead.1.trans zero)
          have bz : b = [] := List.eq_nil_of_length_eq_zero (rightRead.1.trans (length.symm.trans zero))
          rw [az, bz]
        · exact represented_alias state left right a b leftRead rightRead length same
      simp only [if_neg (not_not_intro length), if_pos shortcut, equal, decide_true]
    · have positive : 0 < left.length := by omega
      let av (i : Nat) := a[i]?.getD 0
      let bv (i : Nat) := b[i]?.getD 0
      have loads (block : List Nat) (member : block ∈ blocks left.length) (i : Nat) (inside : i ∈ block) :
          load state (left.pointer i) = .ok (number (av i)) ∧ load state (right.pointer i) = .ok (number (bv i)) := by
        have bound := (coverage left.length i positive).mp ⟨block, member, inside⟩
        have al : i < a.length := by omega
        have bl : i < b.length := by omega
        simpa only [av, bv, List.getElem?_eq_getElem al, List.getElem?_eq_getElem bl, Option.getD_some] using
          And.intro (leftRead.2 i al) (rightRead.2 i bl)
      have reads (block : List Nat) (member : block ∈ blocks left.length) (i : Nat) (inside : i ∈ block) :
          readId state left i = .ok (av i) ∧ readId state right i = .ok (bv i) :=
        ⟨readId_of_load _ _ _ _ (loads block member i inside).1, readId_of_load _ _ _ _ (loads block member i inside).2⟩
      have sourceScan : nativeScan state left right = scan state left right (blocks left.length) := by
        unfold nativeScan
        split
        · rename_i small; rw [blocks, if_pos small]
        · rename_i large
          rw [blocks_large left.length large]
          exact vectors_eq_scan state left right (starts left.length) av bv (by
            intro start member
            apply loads (chunk start)
            rw [blocks_large left.length large]
            exact List.mem_map_of_mem member)
      obtain ⟨result, scanned, equal⟩ := scan_verified state left right (blocks left.length) av bv reads
      have iff : result = true ↔ a = b := by
        constructor
        · intro yes
          apply List.ext_getElem (leftRead.1.trans (length.trans rightRead.1.symm))
          intro i ha hb
          obtain ⟨block, member, inside⟩ := (coverage left.length i positive).mpr (by omega)
          have same := equal.mp yes block member i inside
          simpa only [av, bv, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, Option.getD_some] using same
        · intro same; subst b
          exact equal.mpr (by intro block member i inside; rfl)
      have resultEq : result = decide (a = b) := by
        apply Bool.eq_iff_iff.mpr
        simpa using iff
      simp only [if_neg (not_not_intro length), if_neg shortcut, sourceScan, scanned, resultEq]
  · have different : a ≠ b := by
      intro same
      apply length
      rw [← leftRead.1, ← rightRead.1, same]
    simp only [if_pos length, decide_false, different]

/-- The compiler must supply native storage that makes sliceAsBytes' usize
multiplication defined. Existing allocation validity discharges it for a writable
view; it is not a newly trusted memcpy/equality precondition. -/
theorem byte_length_bound (state : State) (source : View) (valid : state.valid = true)
    (writable : Writable state source) : source.length * 4 < addressLimit := by
  obtain ⟨extent, cell, found, typed, _, inside⟩ := writable
  obtain ⟨_, basePositive, layout, shaped, _, extentBound, _⟩ := valid_lookup state source.allocation cell valid found
  have shape : layout = ⟨extent * 4, 4⟩ := Option.some.inj (shaped.symm.trans (typed ▸ array_layout extent))
  subst layout
  dsimp only at extentBound
  omega

end Compiler.Extraction.ExpressionMap.ArgumentScan
