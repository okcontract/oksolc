/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapEntry
import Compiler.ZigAir.MemoryInvalidationFrame

namespace Compiler.Extraction.ExpressionMap.Buckets.Entry
open Compiler.ZigAir.Memory
open Compiler.ZigAir.Memory.WordArray (word)

/-- Assignment of undefined forgets initialized leaves. It never chooses a
byte pattern or frees a pointed-to argument allocation. -/
def undefine (before : State) (target : Value) : Except Fault State :=
  match target with
  | .pointer (.pointer writable false child) address => invalidate before writable child address
  | _ => .error .unsupported

def reset (keyPointer valuePointer : Value) (before : State) : Except Fault Unit × State :=
  match undefine before keyPointer with
  | .error fault => (.error fault, before)
  | .ok middle => match undefine middle valuePointer with
    | .error fault => (.error fault, middle)
    | .ok after => (.ok (), after)

structure Reset (capacity : BitVec 32) (bucket index : Nat) (before middle after : State) : Prop where
  valid : before.valid = true
  key : invalidate before true keyType (KeyFields.address capacity.toNat bucket index) = .ok middle
  value : invalidate middle true word (Values.address capacity.toNat bucket index) = .ok after

theorem reset_verified (capacity : BitVec 32) (bucket index : Nat) (before : State) (cell : Allocation)
    (inside : index < capacity.toNat) (valid : before.valid = true)
    (found : before.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity.toNat)
    (writable : cell.writable = true) :
    ∃ middle after, reset (.pointer (.pointer true false keyType) (KeyFields.address capacity.toNat bucket index))
      (Values.pointer capacity.toNat bucket index) before = (.ok (), after) ∧
      Reset capacity bucket index before middle after := by
  have first := invalidate_of_access before keyType (KeyFields.address capacity.toNat bucket index) ⟨64, 16⟩ cell
    key_layout (KeyFields.access_entry before capacity.toNat bucket index 64 cell capacity.isLt inside (by decide)
      valid found typed true (fun _ => writable)) (typed ▸ KeyFields.key_view capacity.toNat index capacity.isLt inside)
  let middle := { before with heap := (before.heap.replace bucket
    ({ cell with cells := cell.cells.forget (keysOffset capacity.toNat + index * 64) 64 })) }
  have first : invalidate before true keyType (KeyFields.address capacity.toNat bucket index) = .ok middle := first
  have middleValid := invalidate_valid _ _ _ _ _ valid first
  obtain ⟨middleCell, middleFound, shape⟩ := invalidate_retains_shape _ _ _ _ _ first bucket cell found
  have accessed := access_read_write middle (Values.address capacity.toNat bucket index) ⟨4, 4⟩ middleCell
    (Values.access_entry middle capacity.toNat bucket index middleCell capacity.isLt inside middleValid middleFound
      (shape.2.1.trans typed)) (shape.2.2.1.trans writable)
  have second := invalidate_of_access middle word (Values.address capacity.toNat bucket index) ⟨4, 4⟩ middleCell
    rfl accessed ((shape.2.1.trans typed) ▸ (Values.views capacity.toNat index capacity.isLt inside).1)
  exact ⟨middle, _, by simp only [reset, undefine, Values.pointer, first, second], valid, first, second⟩

variable {capacity : BitVec 32} {bucket index : Nat} {before middle after : State}

theorem Reset.native_frame (post : Reset capacity bucket index before middle after) :
    after.valid = true ∧ before.heap.RetainsShape after.heap ∧
      (∀ other, other ≠ bucket → after.heap.lookup other = before.heap.lookup other) ∧
      after.nextId = before.nextId ∧ after.nextAddress = before.nextAddress := by
  have first := invalidate_frame _ _ _ _ _ post.key
  have second := invalidate_frame _ _ _ _ _ post.value
  exact ⟨invalidate_valid _ _ _ _ _ (invalidate_valid _ _ _ _ _ post.valid post.key) post.value,
    (invalidate_retains_shape _ _ _ _ _ post.key).trans (invalidate_retains_shape _ _ _ _ _ post.value),
    fun other apart => (second.2.2 other apart).trans (first.2.2 other apart),
    second.1.trans first.1, second.2.1.trans first.2.1⟩

theorem Reset.outside (post : Reset capacity bucket index before middle after)
    (writable many : Bool) (child : Ty) (offset : Nat)
    (keyApart : KeyFields.Outside capacity.toNat index child offset)
    (valueApart : ∀ position ∈ child.readOffsets offset,
      position < valuesOffset capacity.toNat + index * 4 ∨ valuesOffset capacity.toNat + index * 4 + 4 ≤ position) :
    load after (.pointer (.pointer writable many child) ⟨bucket, offset⟩) =
      load before (.pointer (.pointer writable many child) ⟨bucket, offset⟩) :=
  (load_disjoint_after_invalidate middle after true word (Values.address capacity.toNat bucket index) ⟨4, 4⟩
    writable many child offset rfl post.value valueApart).trans
    (load_disjoint_after_invalidate before middle true keyType (KeyFields.address capacity.toNat bucket index) ⟨64, 16⟩
      writable many child offset key_layout post.key keyApart)

theorem Reset.headers (post : Reset capacity bucket index before middle after) (slot : Header.Slot) :
    load after (slot.pointer capacity bucket) = load before (slot.pointer capacity bucket) := by
  have geometry := Buckets.geometry capacity.toNat capacity.isLt
  apply post.outside true false (slot.value capacity bucket).type slot.offset
  all_goals cases slot <;> simp [KeyFields.Outside, Header.Slot.value, Header.Slot.offset, Value.type,
    Compiler.ZigAir.Scalar.Value.type, Ty.readOffsets] <;> omega

theorem Reset.metadata (post : Reset capacity bucket index before middle after) (other : Nat)
    (inside : other < capacity.toNat) :
    load after (Metadata.pointer bucket other) = load before (Metadata.pointer bucket other) := by
  have geometry := Buckets.geometry capacity.toNat capacity.isLt
  apply post.outside true false Metadata.byte (24 + other)
  all_goals simp only [KeyFields.Outside, Metadata.byte, Ty.readOffsets, List.mem_singleton]
  all_goals intro position same; subst position; left; omega

end Compiler.Extraction.ExpressionMap.Buckets.Entry
