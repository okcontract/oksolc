/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryRecordWrites
import Compiler.ZigAir.MemoryReadTyping

namespace Compiler.ZigAir.Memory

/-- Update only a loaded slice's length leaf in arbitrary declared storage,
including a captured struct. The original pointer and every other leaf remain
in the existing cells. This is not the exact-cell-list initialization law for
a standalone slice allocation. -/
theorem Cells.read_slice_after_length_write (cells contents : Cells) (owner : Ty) (offset : Nat)
    (writable : Bool) (child : Ty) (address : Address) (before after : Nat)
    (loaded : cells.read owner offset (.slice writable child) = .ok (.slice (.slice writable child) address before))
    (written : cells.write owner (offset + 8) (.scalar (.int false 64 after)) = .ok contents) :
    contents.read owner offset (.slice writable child) = .ok (.slice (.slice writable child) address after) := by
  have parts := cells.read_slice_parts owner offset writable child address before loaded
  have readback := cells.readLeaf_after_single_write owner (offset + 8) (.scalar (.int false 64 after)) contents written rfl
  obtain ⟨_, _, _, rfl⟩ := cells.write_success owner (offset + 8) (.scalar (.int false 64 after)) contents written
  apply Cells.read_slice_of_parts _ owner offset writable child address after parts.1
  · simpa only [Value.leaves, List.foldl_cons, List.foldl_nil, Cells.readLeaf,
      Cells.lookup_set_other cells _ _ _ (by omega : offset ≠ offset + 8)] using parts.2.1
  · exact readback

/-- Replacing the pointer leaf preserves the loaded length, including zero,
without touching adjacent header or descriptor fields. -/
theorem Cells.read_slice_after_pointer_write (cells contents : Cells) (owner : Ty) (offset : Nat)
    (writable : Bool) (child : Ty) (before after : Address) (length : Nat)
    (loaded : cells.read owner offset (.slice writable child) = .ok (.slice (.slice writable child) before length))
    (written : cells.write owner offset (.pointer (.pointer writable true child) after) = .ok contents) :
    contents.read owner offset (.slice writable child) = .ok (.slice (.slice writable child) after length) := by
  have parts := cells.read_slice_parts owner offset writable child before length loaded
  have readback := cells.readLeaf_after_single_write owner offset (.pointer (.pointer writable true child) after) contents written rfl
  obtain ⟨_, _, _, rfl⟩ := cells.write_success owner offset (.pointer (.pointer writable true child) after) contents written
  apply Cells.read_slice_of_parts _ owner offset writable child after length parts.1
  · exact readback
  · simpa only [Value.leaves, List.foldl_cons, List.foldl_nil, Cells.readLeaf,
      Cells.lookup_set_other cells _ _ _ (by omega : offset + 8 ≠ offset)] using parts.2.2

/-- Both leaf-update facades use the same checked containing allocation and
access frame. The callback is a proved sparse-cell transformation. -/
private theorem load_slice_after_leaf_store (state after : State) (address beforeData afterData : Address)
    (readWritable readMany writable : Bool) (child : Ty) (oldLength newLength offset : Nat) (value : Value)
    (loaded : load state (.pointer (.pointer readWritable readMany (.slice writable child)) address) =
      .ok (.slice (.slice writable child) beforeData oldLength))
    (stored : store state (.pointer (.pointer true false value.type) ⟨address.allocation, address.offset + offset⟩) value = .ok after)
    (readback : ∀ (cells contents : Cells) (owner : Ty), cells.read owner address.offset (.slice writable child) =
        .ok (.slice (.slice writable child) beforeData oldLength) →
      cells.write owner (address.offset + offset) value = .ok contents →
      contents.read owner address.offset (.slice writable child) = .ok (.slice (.slice writable child) afterData newLength)) :
    load after (.pointer (.pointer readWritable readMany (.slice writable child)) address) =
      .ok (.slice (.slice writable child) afterData newLength) := by
  obtain ⟨_, _, _, _, cell, contents, same, _, _, accessed, written, rfl⟩ :=
    store_success state _ _ after stored
  cases same
  have found := (access_success_region state ⟨address.allocation, address.offset + offset⟩ _ true cell accessed).1
  cases checked : access state address ⟨16, 8⟩ false with
  | error fault => simp [load, Ty.layout, checked, bind, Except.bind] at loaded
  | ok readCell =>
    have sameCell : readCell = cell := Option.some.inj
      (((access_success_region state address ⟨16, 8⟩ false readCell checked).1).symm.trans found)
    subst readCell
    have read : cell.cells.read cell.type address.offset (.slice writable child) =
        .ok (.slice (.slice writable child) beforeData oldLength) := by
      simpa [load, Ty.layout, checked, Memory.readCell, bind, Except.bind] using loaded
    have updated := access_replace_cells state address ⟨16, 8⟩ false cell contents found
    rw [checked] at updated
    have complete := readback cell.cells contents cell.type read written
    simpa [load, Ty.layout, updated, Memory.readCell, bind, Except.bind] using complete

theorem load_slice_after_length_store (state after : State) (address data : Address)
    (readWritable readMany writable : Bool) (child : Ty) (oldLength newLength : Nat)
    (loaded : load state (.pointer (.pointer readWritable readMany (.slice writable child)) address) =
      .ok (.slice (.slice writable child) data oldLength))
    (stored : store state (.pointer (.pointer true false usize) ⟨address.allocation, address.offset + 8⟩)
      (.scalar (.int false 64 newLength)) = .ok after) :
    load after (.pointer (.pointer readWritable readMany (.slice writable child)) address) =
      .ok (.slice (.slice writable child) data newLength) :=
  load_slice_after_leaf_store state after address data data readWritable readMany writable child oldLength newLength 8
    (.scalar (.int false 64 newLength)) loaded stored
    (fun cells contents owner read write => cells.read_slice_after_length_write contents owner address.offset writable child
      data oldLength newLength read write)

theorem load_slice_after_pointer_store (state after : State) (address beforeData afterData : Address)
    (readWritable readMany writable : Bool) (child : Ty) (length : Nat)
    (loaded : load state (.pointer (.pointer readWritable readMany (.slice writable child)) address) =
      .ok (.slice (.slice writable child) beforeData length))
    (stored : store state (.pointer (.pointer true false (.pointer writable true child)) address)
      (.pointer (.pointer writable true child) afterData) = .ok after) :
    load after (.pointer (.pointer readWritable readMany (.slice writable child)) address) =
      .ok (.slice (.slice writable child) afterData length) :=
  load_slice_after_leaf_store state after address beforeData afterData readWritable readMany writable child length length 0
    (.pointer (.pointer writable true child) afterData) loaded (by simpa only [Nat.add_zero] using stored)
    (fun cells contents owner read write => cells.read_slice_after_pointer_write contents owner address.offset writable child
      beforeData afterData length read (by simpa only [Nat.add_zero] using write))

end Compiler.ZigAir.Memory
