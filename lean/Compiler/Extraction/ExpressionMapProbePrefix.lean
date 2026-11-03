/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapProbeIndex
import Compiler.Extraction.ExpressionMapCandidateInspection

namespace Compiler.Extraction.ExpressionMap.Probe
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Buckets
open Compiler.Extraction.Cache (Key)

/-- The native else-if: a matching used fingerprint leaves the remembered
tombstone untouched, even when key equality subsequently returns false. -/
def remember (capacity : BitVec 32) (index first : Nat) (fp : BitVec 7) (bits : BitVec 8) : Nat :=
  if Metadata.isUsed bits && bits.toNat % 128 == fp.toNat then first
  else if first == capacity.toNat && bits == 1 then index else first

theorem remember_exact (capacity : BitVec 32) (index first : Nat) (fp : BitVec 7) (bits : BitVec 8) :
    remember capacity index first fp bits = if first = capacity.toNat ∧ bits = 1 then index else first := by
  by_cases tombstone : bits = 1
  · subst bits; simp [remember, Metadata.isUsed]
  · simp [remember]
    intro _ _ _ wrong
    exact False.elim (tombstone wrong)

/-- The actual candidate proof for each skipped slot. This records no guessed
logical key and retains the source's remaining-count guard. -/
def Passed (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64)
    (query : Key) (table : OwnedKeys.Table) (distance : Nat) : Prop :=
  ∀ j, j < distance → ∃ bits, Metadata.readByte state bucket (slot capacity hash j) = .ok bits ∧
    Candidate.Correct state capacity bucket (slot capacity hash j) (capacity.toNat - j)
      (fingerprint hash) query table bits .next

/-- Either no tombstone has been seen, or the remembered index is precisely
the earliest one. The sentinel is capacity, as in the native loop. -/
def Remembered (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64)
    (distance first : Nat) : Prop :=
  (first = capacity.toNat ∧ ∀ j, j < distance → Metadata.readByte state bucket (slot capacity hash j) ≠ .ok 1) ∨
  ∃ j, j < distance ∧ first = slot capacity hash j ∧ Metadata.readByte state bucket first = .ok 1 ∧
    ∀ k, k < j → Metadata.readByte state bucket (slot capacity hash k) ≠ .ok 1

variable {state : State} {capacity : BitVec 32} {bucket : Nat} {hash : BitVec 64}
    {query : Key} {table : OwnedKeys.Table} {distance first remaining : Nat} {bits : BitVec 8}

theorem passed_zero : Passed state capacity bucket hash query table 0 := by intro j impossible; omega
theorem remembered_zero : Remembered state capacity bucket hash 0 capacity.toNat :=
  Or.inl ⟨rfl, by intro j impossible; omega⟩

theorem Passed.succ (prior : Passed state capacity bucket hash query table distance)
    (budget : distance + remaining = capacity.toNat)
    (read : Metadata.readByte state bucket (slot capacity hash distance) = .ok bits)
    (correct : Candidate.Correct state capacity bucket (slot capacity hash distance) remaining
      (fingerprint hash) query table bits .next) : Passed state capacity bucket hash query table (distance + 1) := by
  intro j inside
  by_cases earlier : j < distance
  · exact prior j earlier
  · have same : j = distance := by omega
    subst j
    have left : capacity.toNat - distance = remaining := by omega
    exact ⟨bits, read, left ▸ correct⟩

theorem Remembered.succ (power : Power capacity) (prior : Remembered state capacity bucket hash distance first)
    (read : Metadata.readByte state bucket (slot capacity hash distance) = .ok bits) :
    Remembered state capacity bucket hash (distance + 1)
      (remember capacity (slot capacity hash distance) first (fingerprint hash) bits) := by
  rw [remember_exact]
  rcases prior with ⟨sentinel, none⟩ | ⟨j, earlier, selected, tombstone, firstSeen⟩
  · subst first
    by_cases isTombstone : bits = 1
    · simp only [isTombstone, and_self, if_true]
      exact Or.inr ⟨distance, by omega, rfl, isTombstone ▸ read, none⟩
    · simp only [isTombstone, and_false, if_false]
      refine Or.inl ⟨rfl, ?_⟩
      intro j inside
      by_cases earlier : j < distance
      · exact none j earlier
      · have same : j = distance := by omega
        subst j
        intro wrong
        exact isTombstone (Except.ok.inj (read.symm.trans wrong))
  · have inside : first < capacity.toNat := selected ▸ slot_bound power
    rw [if_neg (by omega)]
    exact Or.inr ⟨j, by omega, selected, tombstone, firstSeen⟩

end Compiler.Extraction.ExpressionMap.Probe
