/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapBucketStorage

namespace Compiler.Extraction.ExpressionMap.Buckets.Metadata
open Compiler.ZigAir.Memory

def byte : Ty := .scalar (.int false 8)
def zero : Value := .scalar (.int false 8 0)
def pointer (id index : Nat) : Value := .pointer (.pointer true false byte) ⟨id, 24 + index⟩

/-- The packed record's captured backing leaf, not an unrestricted byte alias. -/
theorem byte_views (capacity index : Nat) (positive : 0 < capacity) (inside : index < capacity) :
    acceptsView (storageType capacity) (24 + index) byte = true ∧
      leafType (storageType capacity) (24 + index) = some byte := by
  have checked := storage_valid capacity positive
  have outsideHeader : ¬24 + index < 24 := by omega
  simp [acceptsView, leafType, storageType, checked, byte]
  simp [storageFields, Field.contains, Field.layout, header_layout, Ty.layout, inside, metadataType,
    Ty.aggregateValid, checkFields, Field.layouts, Field.type, outsideHeader, Nat.mod_one]

theorem store_byte_total (before : State) (id : Nat) (cell : Allocation) (capacity : BitVec 32)
    (index : Nat) (bits : BitVec 8) (inside : index < capacity.toNat) (valid : before.valid = true)
    (found : before.heap.lookup id = some cell) (typed : cell.type = storageType capacity.toNat)
    (writable : cell.writable = true) : ∃ after, store before (pointer id index) (.scalar (.int false 8 bits.toNat)) = .ok after := by
  have target : pointer id index = .pointer (.pointer true false byte) ⟨id, 24 + index⟩ := rfl
  rw [target]
  have positive : 0 < capacity.toNat := by omega
  have geometry := Buckets.geometry capacity.toNat capacity.isLt
  have root := root_access before id cell ⟨bytes capacity.toNat, 16⟩ true valid found
    (typed ▸ storage_layout capacity.toNat positive) geometry.2.2.2.2.2.2.1 (fun _ => writable)
  have accessed := access_subregion before ⟨id, 0⟩ ⟨bytes capacity.toNat, 16⟩ ⟨1, 1⟩ (24 + index) true cell
    root (by decide) (by dsimp; omega) (by change (24 + index) % 1 = 0; exact Nat.mod_one _)
      (by change 16 % 1 = 0; decide)
  refine store_subobject_total before ⟨id, 24 + index⟩ ⟨1, 1⟩ cell (.scalar (.int false 8 bits.toNat)) (by
    simp [Value.valid, Compiler.ZigAir.Scalar.Value.valid, Compiler.ZigAir.Scalar.Ty.contains,
      Compiler.ZigAir.Scalar.Ty.lower, Compiler.ZigAir.Scalar.Ty.upper]; have := bits.isLt; omega) rfl
    (by simpa only [Nat.zero_add] using accessed) ?_ ?_
  · exact typed.symm ▸ (byte_views _ _ positive inside).1
  · intro entry member
    simp only [Value.leaves, List.mem_singleton] at member
    subst entry
    simpa only [Nat.add_zero] using typed.symm ▸ (byte_views _ _ positive inside).2

theorem store_total (before : State) (id : Nat) (cell : Allocation) (capacity : BitVec 32)
    (index : Nat) (inside : index < capacity.toNat) (valid : before.valid = true)
    (found : before.heap.lookup id = some cell) (typed : cell.type = storageType capacity.toNat)
    (writable : cell.writable = true) : ∃ after, store before (pointer id index) zero = .ok after := by
  have cleared : zero = .scalar (.int false 8 (0#8).toNat) := rfl
  rw [cleared]
  exact store_byte_total before id cell capacity index 0 inside valid found typed writable

theorem read_other (before after : State) (id index queried : Nat) (different : queried ≠ index)
    (stored : store before (pointer id index) zero = .ok after) :
    load after (pointer id queried) = load before (pointer id queried) := by
  apply load_disjoint_after_store before true false byte _ zero after true false byte (24 + queried) stored
  simp [zero, Value.leaves, byte, Ty.readOffsets]
  omega

theorem header_frame (before after : State) (id index : Nat) (capacity : BitVec 32) (slot : Header.Slot)
    (stored : store before (pointer id index) zero = .ok after) :
    load after (slot.pointer capacity id) = load before (slot.pointer capacity id) := by
  apply load_disjoint_after_store before true false byte _ zero after true false _ slot.offset stored
  cases slot <;> simp [zero, Value.leaves, Header.Slot.value, Header.Slot.offset, Value.type,
    Compiler.ZigAir.Scalar.Value.type, Ty.readOffsets]
  all_goals omega

/-- Sequential byte effects of memset, with the actual prefix retained on a
verification rejection. No counter allocation is invented for this builtin. -/
def fill (id : Nat) : Nat → Nat → State → Except Fault Unit × State
  | 0, _, before => (.ok (), before)
  | count + 1, index, before => match store before (pointer id index) zero with
    | .error fault => (.error fault, before)
    | .ok after => fill id count (index + 1) after

structure Filled (id index count : Nat) (capacity : BitVec 32) (before after : State) : Prop where
  valid : after.valid = true
  shape : before.heap.RetainsShape after.heap
  frame : ∀ other, other ≠ id → after.heap.lookup other = before.heap.lookup other
  nextId : after.nextId = before.nextId
  nextAddress : after.nextAddress = before.nextAddress
  reads : ∀ queried, index ≤ queried → queried < index + count → load after (pointer id queried) = .ok zero
  others : ∀ queried, queried < index ∨ index + count ≤ queried → load after (pointer id queried) = load before (pointer id queried)
  headers : ∀ slot : Header.Slot, load after (slot.pointer capacity id) = load before (slot.pointer capacity id)

theorem fill_verified (id index count : Nat) (capacity : BitVec 32) (before : State) (cell : Allocation)
    (bounded : index + count ≤ capacity.toNat) (valid : before.valid = true)
    (found : before.heap.lookup id = some cell) (typed : cell.type = storageType capacity.toNat)
    (writable : cell.writable = true) :
    ∃ after, fill id count index before = (.ok (), after) ∧ Filled id index count capacity before after := by
  induction count generalizing index before cell with
  | zero => exact ⟨before, rfl, valid, Heap.RetainsShape.refl _, fun _ _ => rfl, rfl, rfl,
      (by intro _ lower upper; omega), fun _ _ => rfl, fun _ => rfl⟩
  | succ count ih =>
    obtain ⟨middle, stored⟩ := store_total before id cell capacity index (by omega) valid found typed writable
    have shape := store_retains_shape _ _ _ _ stored
    have middleValid := store_preserves_valid _ _ _ _ valid stored
    obtain ⟨middleCell, middleFound, middleShape⟩ := shape id cell found
    obtain ⟨after, ran, post⟩ := ih (index + 1) middle middleCell (by omega) middleValid middleFound
      (middleShape.2.1.trans typed) (middleShape.2.2.1.trans writable)
    refine ⟨after, by simp only [fill, stored]; exact ran, post.valid, shape.trans post.shape,
      fun other apart => (post.frame other apart).trans (heap_after_store_other _ true false byte _ _ _ stored other apart),
      post.nextId.trans (store_keeps_counters _ _ _ _ stored).1,
      post.nextAddress.trans (store_keeps_counters _ _ _ _ stored).2, ?_, ?_, ?_⟩
    · intro queried lower upper
      by_cases same : queried = index
      · subst queried
        exact (post.others index (Or.inl (by omega))).trans
          (load_alias_after_store before true false byte _ _ middle true false stored)
      · exact post.reads queried (by omega) (by omega)
    · intro queried apart
      exact (post.others queried (by omega)).trans (read_other before middle id index queried (by omega) stored)
    · intro slot
      exact (post.headers slot).trans (header_frame before middle id index capacity slot stored)

end Compiler.Extraction.ExpressionMap.Buckets.Metadata
