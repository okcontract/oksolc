/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapProbeRouting

namespace Compiler.Extraction.ExpressionMap.Probe
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Buckets

/-- Native metadata states produced by initialization, fill and remove.
An arbitrary initialized unused fingerprint is not silently treated as a tombstone. -/
def Canonical (state : State) (capacity : BitVec 32) (bucket : Nat) : Prop :=
  ∀ index, index < capacity.toNat → ∀ bits, Metadata.readByte state bucket index = .ok bits →
    bits = 0 ∨ bits = 1 ∨ Metadata.isUsed bits = true

def RouteTo (state : State) (capacity : BitVec 32) (bucket : Nat) (hash : BitVec 64) (index : Nat) : Prop :=
  ∃ distance, distance < capacity.toNat ∧ index = slot capacity hash distance ∧
    ∀ j, j < distance → NonFree state bucket (slot capacity hash j)

/-- The exact getOrPut selection after a miss. -/
def select (capacity : BitVec 32) (index first : Nat) : Nat := if first < capacity.toNat then first else index

variable {state : State} {capacity : BitVec 32} {bucket : Nat} {hash : BitVec 64}
    {query : Cache.Key} {table : OwnedKeys.Table} {distance index first : Nat}

theorem vacant_of_byte (read : Metadata.readByte state bucket index = .ok bits)
    (unused : Metadata.isUsed bits = false) : ¬Table.Used state bucket index := by
  simp [Table.Used, Metadata.observe_read_byte, read, Except.map, unused]

theorem exhausted_full (power : Power capacity) (canonical : Canonical state capacity bucket)
    (passed : Passed state capacity bucket hash query table capacity.toNat)
    (none : ∀ j, j < capacity.toNat → Metadata.readByte state bucket (slot capacity hash j) ≠ .ok 1) :
    Table.count capacity bucket state = capacity.toNat := by
  have allUsed (index : Nat) (inside : index < capacity.toNat) : Table.Used state bucket index := by
    obtain ⟨j, bound, selected⟩ := slot_covers (hash := hash) power inside
    obtain ⟨bits, read, correct⟩ := passed j bound
    have shape := canonical (slot capacity hash j) (slot_bound power) bits read
    have used : Metadata.isUsed bits = true := by
      rcases shape with zero | tombstone | used
      · subst bits; cases correct.1
      · exact False.elim (none j bound (tombstone ▸ read))
      · exact used
    rw [← selected]
    simp [Table.Used, Metadata.observe_read_byte, read, Except.map, correct.1, used]
  have complete := List.countP_eq_length.mpr (show ∀ i ∈ List.range capacity.toNat, Table.occupied state bucket i = true by
    intro i inside
    exact (Table.occupied_iff state bucket i).mpr (allUsed i (List.mem_range.mp inside)))
  simpa only [Table.count, List.length_range] using complete

/-- A real vacant slot follows from the complete scan and original occupancy
room. No successful selection, key absence or unused-slot premise is supplied. -/
theorem Completed.vacancy (power : Power capacity) (canonical : Canonical state capacity bucket)
    (room : Table.count capacity bucket state < capacity.toNat)
    (completed : Completed state capacity bucket hash query table (.miss index first)) :
    select capacity index first < capacity.toNat ∧ ¬Table.Used state bucket (select capacity index first) ∧
      RouteTo state capacity bucket hash (select capacity index first) := by
  obtain ⟨distance, bound, selected, passed, remembered, stopped⟩ := completed
  rcases remembered with ⟨sentinel, none⟩ | ⟨j, earlier, picked, read, _⟩
  · subst first
    simp only [select, Nat.lt_irrefl, if_false]
    have notFull : distance < capacity.toNat := by
      have different : distance ≠ capacity.toNat := by
        intro same
        subst distance
        have full := exhausted_full power canonical passed none
        omega
      omega
    have free := stopped.resolve_right (by omega)
    have read := Metadata.read_byte_free state bucket index free
    refine ⟨selected ▸ slot_bound power, vacant_of_byte read (by decide), distance, notFull, selected, ?_⟩
    intro j inside; exact passed.nonfree inside
  · have firstBound : first < capacity.toNat := picked ▸ slot_bound power
    rw [select, if_pos firstBound]
    refine ⟨firstBound, vacant_of_byte read (by decide), j, by omega, picked, ?_⟩
    intro k inside
    exact passed.nonfree (by omega)

theorem Canonical.of_ready (ready : Local.EmptyReady safety receiver bucket capacity base state) :
    Canonical state capacity bucket := by
  intro index inside bits read
  have zero := Metadata.read_byte_free state bucket index (ready.slots index inside)
  exact Or.inl (Except.ok.inj (read.symm.trans zero))

end Compiler.Extraction.ExpressionMap.Probe
