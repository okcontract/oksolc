/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapTableEntry

namespace Compiler.Extraction.ExpressionMap.Table
open Compiler.ZigAir.Memory Initialization Buckets Insertion
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)

abbrev Used (state : State) (bucket index : Nat) : Prop := Metadata.observe state bucket index = .ok (false, true)
def occupied (state : State) (bucket index : Nat) : Bool :=
  match Metadata.observe state bucket index with
  | .ok (free, used) => !free && used
  | .error _ => false

theorem occupied_iff (state : State) (bucket index : Nat) : occupied state bucket index = true ↔ Used state bucket index := by
  cases observed : Metadata.observe state bucket index with
  | error fault => simp [occupied, Used, observed]
  | ok pair => rcases pair with ⟨free, used⟩; cases free <;> cases used <;> simp [occupied, Used, observed]

/-- A finite measure of the existing native slots, not a compiler scan or a
second table. Binding below admits every metadata read before using the count. -/
def count (capacity : BitVec 32) (bucket : Nat) (state : State) : Nat :=
  (List.range capacity.toNat).countP (occupied state bucket)

theorem count_le (capacity : BitVec 32) (bucket : Nat) (state : State) : count capacity bucket state ≤ capacity.toNat := by
  simpa only [count, List.length_range] using (List.countP_le_length (p := occupied state bucket) (l := List.range capacity.toNat))

theorem count_bound (capacity : BitVec 32) (bucket : Nat) (state : State) : count capacity bucket state < 2 ^ 32 :=
  Nat.lt_of_le_of_lt (count_le capacity bucket state) capacity.isLt

theorem count_room (capacity : BitVec 32) (bucket index : Nat) (state : State)
    (inside : index < capacity.toNat) (vacant : ¬Used state bucket index) : count capacity bucket state + 1 ≤ capacity.toNat := by
  have bound := count_le capacity bucket state
  have different : count capacity bucket state ≠ capacity.toNat := by
    intro same
    have all := List.countP_eq_length.mp (show (List.range capacity.toNat).countP (occupied state bucket) =
      (List.range capacity.toNat).length by simpa [count] using same)
    have present := all index (by simpa using inside)
    simp only [occupied_iff] at present
    exact vacant present
  omega

/-- Both directions and uniqueness bind the existing function table to every
occupied native slot. Count and initialized metadata are independent obligations;
no hash/probe path is assumed or claimed by this storage relation. -/
structure Binding (place : Placement) (safety : Bool) (receiver bucket : Nat) (capacity : BitVec 32)
    (state : State) (table : OwnedKeys.Table) : Prop where
  layout : Layout place safety receiver bucket capacity state
  metadata : ∀ i, i < capacity.toNat → ∃ bits, Metadata.readByte state bucket i = .ok bits
  size : load state (Counter.field place safety receiver .size) = .ok (number (BitVec.ofNat 32 (count capacity bucket state)))
  slots : ∀ i, i < capacity.toNat → Used state bucket i → ∃ key entry, table key = some entry ∧ EntryView capacity bucket i state key entry
  entries : ∀ key entry, table key = some entry → ∃ i, i < capacity.toNat ∧ Used state bucket i ∧ EntryView capacity bucket i state key entry
  unique : ∀ i j key entry, i < capacity.toNat → j < capacity.toNat → Used state bucket i → Used state bucket j →
    EntryView capacity bucket i state key entry → EntryView capacity bucket j state key entry → i = j

theorem byte_of_used (used : Used state bucket index) : ∃ bits, Metadata.readByte state bucket index = .ok bits := by
  rw [Used, Metadata.observe_read_byte] at used
  cases read : Metadata.readByte state bucket index with
  | error fault => simp [read, Except.map] at used
  | ok bits => exact ⟨bits, rfl⟩

theorem used_frame (same : Metadata.readByte after bucket index = Metadata.readByte before bucket index) :
    Used after bucket index ↔ Used before bucket index := by
  simp only [Used, Metadata.observe_read_byte, same]

/-- Initial metadata clearing and zero size derive the empty relation without
assuming an initialized entry or supplying a native/logical correspondence. -/
theorem Binding.of_ready (ready : Local.EmptyReady safety receiver bucket capacity base state) :
    Binding .localMap safety receiver bucket capacity state (fun _ => none) := by
  have unused (i : Nat) (inside : i < capacity.toNat) : ¬Used state bucket i := by
    simp [Used, ready.slots i inside]
  have zero : count capacity bucket state = 0 := by
    apply List.countP_eq_zero.mpr
    intro i member
    simpa only [occupied_iff] using unused i (by simpa using member)
  refine ⟨Layout.of_ready ready, ?_, ?_, ?_, ?_, ?_⟩
  · intro i inside
    exact ⟨0, Metadata.read_byte_free state bucket i (ready.slots i inside)⟩
  · simpa only [zero, Counter.field, Placement.offset, Nat.zero_add, Local.field] using ready.size
  · intro i inside used; exact False.elim (unused i inside used)
  · intro key entry absent; cases absent
  · intro i j key entry inside _ used; exact False.elim (unused i inside used)

end Compiler.Extraction.ExpressionMap.Table
