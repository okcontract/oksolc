/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapTable

namespace Compiler.Extraction.ExpressionMap.Table
open Compiler.ZigAir.Memory Initialization Buckets Insertion
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache (Key)

theorem count_changed (old new : Nat → Bool) (index : Nat) (xs : List Nat) (distinct : xs.Nodup)
    (member : index ∈ xs) (vacant : old index = false) (filled : new index = true)
    (others : ∀ i ∈ xs, i ≠ index → new i = old i) : xs.countP new = xs.countP old + 1 := by
  induction xs with
  | nil => simp at member
  | cons head tail ih =>
    obtain ⟨notMember, nodup⟩ := List.nodup_cons.mp distinct
    by_cases same : head = index
    · subst head
      have rest : tail.countP new = tail.countP old := List.countP_congr (by
        intro i inside
        rw [others i (by simp [inside]) (by intro eq; subst i; exact notMember inside)])
      simp [vacant, filled, rest]
    · have inTail : index ∈ tail := by simpa [same, Ne.symm same] using member
      have updated := ih nodup inTail (fun i inside apart => others i (by simp [inside]) apart)
      rw [List.countP_cons, List.countP_cons, others head (by simp) same, updated]
      omega

theorem publication_count (incoming : OwnedKeys.Entry)
    (binding : Binding place safety receiver bucket capacity before table)
    (post : Published place safety receiver bucket index capacity fp available size key ⟨incoming.address, 0⟩ incoming.id before after)
    (inside : index < capacity.toNat) (vacant : ¬Used before bucket index) :
    count capacity bucket after = count capacity bucket before + 1 := by
  apply count_changed (occupied before bucket) (occupied after bucket) index (List.range capacity.toNat)
    List.nodup_range (by simpa using inside)
  · exact Bool.eq_false_iff.mpr (fun used => vacant ((occupied_iff before bucket index).mp used))
  · exact (occupied_iff after bucket index).mpr post.metadata
  · intro i member apart
    have same := used_frame (post.metadata_other binding.layout i (by simpa using member) apart)
    apply Bool.eq_iff_iff.mpr
    simpa only [occupied_iff] using same

/-- A selected unused slot with an absent key implements the existing logical
store, including complete coverage of occupied slots and the actual size field.
The native argument observations supplied here are derived by the owning caller. -/
theorem Binding.after_new_slot (incoming : OwnedKeys.Entry)
    (binding : Binding place safety receiver bucket capacity before table)
    (post : Published place safety receiver bucket index capacity fp available (BitVec.ofNat 32 (count capacity bucket before))
      key ⟨incoming.address, 0⟩ incoming.id before after)
    (inside : index < capacity.toNat) (vacant : ¬Used before bucket index) (absent : table key = none)
    (incomingView : EntryView capacity bucket index after key incoming) :
    Binding place safety receiver bucket capacity after (OwnedKeys.store table key incoming) := by
  have used : Used after bucket index := post.metadata
  have otherUsed (i : Nat) (inRange : i < capacity.toNat) (apart : i ≠ index) :
      Used after bucket i ↔ Used before bucket i := used_frame (post.metadata_other binding.layout i inRange apart)
  have previous (i : Nat) (inRange : i < capacity.toNat) (apart : i ≠ index) (used : Used after bucket i)
      (query : Key) (entry : OwnedKeys.Entry) (view : EntryView capacity bucket i after query entry) :
      table query = some entry ∧ EntryView capacity bucket i before query entry := by
    obtain ⟨oldKey, oldEntry, found, oldView⟩ := binding.slots i inRange ((otherUsed i inRange apart).mp used)
    have framed := oldView.frame incoming.id post binding.layout inside inRange apart
    obtain ⟨rfl, rfl⟩ := view.unique framed
    exact ⟨found, oldView⟩
  refine ⟨post.layout, ?_, ?_, ?_, ?_, ?_⟩
  · intro i inRange
    by_cases same : i = index
    · subst i; exact byte_of_used used
    · obtain ⟨bits, read⟩ := binding.metadata i inRange
      exact ⟨bits, (post.metadata_other binding.layout i inRange same).trans read⟩
  · have changed := publication_count incoming binding post inside vacant
    have word : BitVec.ofNat 32 (count capacity bucket after) = BitVec.ofNat 32 (count capacity bucket before) + 1#32 := by
      rw [changed]
      exact BitVec.ofNat_add _ _
    rw [word]
    exact post.sizeRead
  · intro i inRange resident
    by_cases same : i = index
    · subst i; exact ⟨key, incoming, by simp [OwnedKeys.store], incomingView⟩
    · obtain ⟨oldKey, oldEntry, found, view⟩ := binding.slots i inRange ((otherUsed i inRange same).mp resident)
      have different : oldKey ≠ key := by intro eq; subst oldKey; rw [absent] at found; cases found
      exact ⟨oldKey, oldEntry, by simpa [OwnedKeys.store, different] using found,
        view.frame incoming.id post binding.layout inside inRange same⟩
  · intro query entry found
    by_cases same : query = key
    · subst query
      have sameEntry : entry = incoming := by simpa [OwnedKeys.store, eq_comm] using found
      subst entry
      exact ⟨index, inside, used, incomingView⟩
    · have old : table query = some entry := by simpa [OwnedKeys.store, same] using found
      obtain ⟨i, inRange, resident, view⟩ := binding.entries query entry old
      have apart : i ≠ index := by intro eq; subst i; exact vacant resident
      exact ⟨i, inRange, (otherUsed i inRange apart).mpr resident,
        view.frame incoming.id post binding.layout inside inRange apart⟩
  · intro i j query entry ir jr iu ju iv jv
    by_cases first : i = index
    · subst i
      by_cases second : j = index
      · exact second.symm
      · obtain ⟨same, _⟩ := iv.unique incomingView
        have old := (previous j jr second ju query entry jv).1
        rw [same, absent] at old
        cases old
    · by_cases second : j = index
      · subst j
        obtain ⟨same, _⟩ := jv.unique incomingView
        have old := (previous i ir first iu query entry iv).1
        rw [same, absent] at old
        cases old
      · exact binding.unique i j query entry ir jr ((otherUsed i ir first).mp iu) ((otherUsed j jr second).mp ju)
          (previous i ir first iu query entry iv).2 (previous j jr second ju query entry jv).2

end Compiler.Extraction.ExpressionMap.Table
