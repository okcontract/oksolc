/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapBucketHeaderReservation

namespace Compiler.Extraction.ExpressionMap.Receiver
open Compiler.ZigAir.Memory

/-- The nullable pointer stored by the last statement of native allocate. -/
def value (bucket : Nat) : Value :=
  .optionalObject metadataPointerType ⟨8, 8⟩
    (some (.leaf (.pointer metadataPointerType ⟨bucket, 24⟩)))

def checkedValue (capacity : BitVec 32) (bucket : Nat) (state : State) : Except Fault Value := do
  -- The complete packed backing is checked before retaining the native nominal
  -- pointer identity. This is scoped ABI admission, not a general pointer cast.
  let .pointer _ address ← Buckets.Header.arrayPointer state Buckets.metadataType capacity.toNat ⟨bucket, 24⟩
    | .error .unsupported
  let pointer := Value.pointer metadataPointerType address
  .ok (.optionalObject metadataPointerType ⟨8, 8⟩ (some (.leaf pointer)))

/-- grow passes a standalone local map as allocate's receiver. Selecting this
field must not use the compiler owner's embedded-map offset. -/
def pointer (safety : Bool) (state : State) (receiver : Address) (writable : Bool) : Except Fault Value :=
  fieldPointer state (.pointer (.pointer writable false (allocationType safety)) receiver) metadataOffset

def read (safety : Bool) (state : State) (receiver : Address) : Except Fault Value := do
  let field ← pointer safety state receiver false
  load state field

theorem read_eq_of_lookup (safety : Bool) (before after : State) (receiver : Address)
    (same : after.heap.lookup receiver.allocation = before.heap.lookup receiver.allocation) :
    read safety after receiver = read safety before receiver := by
  simp only [read, pointer,
    fieldPointer_eq_of_lookup before after false false (allocationType safety) receiver metadataOffset same]
  cases selected : fieldPointer before (.pointer (.pointer false false (allocationType safety)) receiver) metadataOffset with
  | error fault => rfl
  | ok value =>
    obtain ⟨child, _, rfl⟩ := fieldPointer_address before false false (allocationType safety) receiver metadataOffset value selected
    exact load_eq_of_lookup before after false false child ⟨receiver.allocation, receiver.offset + metadataOffset⟩ same

def publish (safety : Bool) (capacity : BitVec 32) (receiver : Address) (bucket : Nat)
    (state : State) : Except Fault State := do
  let metadata ← checkedValue capacity bucket state
  let field ← pointer safety state receiver true
  store state field metadata

theorem value_valid (bucket : Nat) : (value bucket).valid = true := by
  change (decide (metadataPointerType = metadataPointerType) && true) = true
  simp

theorem metadata_view (capacity : Nat) (positive : 0 < capacity) :
    acceptsView (Buckets.storageType capacity) 24 (.array capacity Buckets.metadataType) = true := by
  have valid := Buckets.storage_valid capacity positive
  simp [Buckets.storageType, acceptsView, valid]
  simp [Buckets.storageFields, Field.contains, Field.layout, Buckets.header_layout,
    Buckets.metadata_layout, Ty.layout, positive]

theorem checked_value (state : State) (bucket : Nat) (cell : Allocation) (capacity : BitVec 32)
    (positive : 0 < capacity.toNat) (valid : state.valid = true)
    (found : state.heap.lookup bucket = some cell) (typed : cell.type = Buckets.storageType capacity.toNat)
    (writable : cell.writable = true) : checkedValue capacity bucket state = .ok (value bucket) := by
  have ranges := Buckets.geometry capacity.toNat capacity.isLt
  have root := root_access state bucket cell ⟨Buckets.bytes capacity.toNat, 16⟩ true valid found
    (typed ▸ Buckets.storage_layout capacity.toNat positive) ranges.2.2.2.2.2.2.1 (fun _ => writable)
  have accessed := access_subregion state ⟨bucket, 0⟩ ⟨Buckets.bytes capacity.toNat, 16⟩ ⟨capacity.toNat, 1⟩
    24 true cell root positive (by dsimp; omega) (by change 24 % 1 = 0; decide) (by change 16 % 1 = 0; decide)
  have layout : (Ty.array capacity.toNat Buckets.metadataType).layout = some ⟨capacity.toNat, 1⟩ := by
    simp [Ty.layout, Buckets.metadata_layout]
  simp only [Nat.zero_add] at accessed
  simp only [checkedValue, Buckets.Header.arrayPointer, layout, accessed, bind, Except.bind, typed,
    metadata_view capacity.toNat positive, Bool.not_true, Bool.false_eq_true, ↓reduceIte, value]

theorem root_pointer (safety : Bool) (state : State) (receiver : Nat) (cell : Allocation) (writable : Bool)
    (valid : state.valid = true) (found : state.heap.lookup receiver = some cell)
    (typed : cell.type = allocationType safety) :
    pointer safety state ⟨receiver, 0⟩ writable =
      .ok (.pointer (.pointer writable false metadataType) ⟨receiver, 0⟩) := by
  exact root_fieldPointer state receiver cell (allocationType safety) metadataType
    (Initialization.Placement.localMap.layout safety) 0 writable false valid found typed
    (Initialization.Placement.localMap.layout_checked safety) (by cases safety <;> decide)
    (by cases safety <;> rfl)

/-- The store derives the reached state and reads from original typed receivers
and bucket storage. It neither assumes successful publication nor erases a write. -/
theorem publish_verified (safety : Bool) (before : State) (receiver bucket : Nat)
    (localCell bucketCell : Allocation) (capacity : BitVec 32) (positive : 0 < capacity.toNat)
    (valid : before.valid = true) (localFound : before.heap.lookup receiver = some localCell)
    (localType : localCell.type = allocationType safety) (localWritable : localCell.writable = true)
    (bucketFound : before.heap.lookup bucket = some bucketCell)
    (bucketType : bucketCell.type = Buckets.storageType capacity.toNat) (bucketWritable : bucketCell.writable = true) :
    ∃ after, publish safety capacity ⟨receiver, 0⟩ bucket before = .ok after ∧
      store before (.pointer (.pointer true false metadataType) ⟨receiver, 0⟩) (value bucket) = .ok after ∧
      after.valid = true ∧ before.heap.RetainsShape after.heap ∧
      read safety after ⟨receiver, 0⟩ = .ok (value bucket) ∧
      (∀ other, other ≠ receiver → after.heap.lookup other = before.heap.lookup other) ∧
      after.nextId = before.nextId ∧ after.nextAddress = before.nextAddress := by
  obtain ⟨after, stored⟩ := Initialization.store_value_at_total .localMap safety before receiver localCell .metadata
    (value bucket) rfl (value_valid bucket) (by intro impossible; cases impossible) valid localFound localType localWritable
  have selected := root_pointer safety before receiver localCell true valid localFound localType
  have resultValid := store_preserves_valid _ _ _ _ valid stored
  have shape := store_retains_shape _ _ _ _ stored
  obtain ⟨resultCell, resultFound, resultShape⟩ := shape receiver localCell localFound
  refine ⟨after, ?_, stored, resultValid, shape, ?_, heap_after_store_other _ true false metadataType _ _ _ stored,
    (store_keeps_counters _ _ _ _ stored).1, (store_keeps_counters _ _ _ _ stored).2⟩
  · simp only [publish, checked_value before bucket bucketCell capacity positive valid bucketFound bucketType bucketWritable,
      selected, bind, Except.bind]
    exact stored
  · simp only [read, root_pointer safety after receiver resultCell false resultValid resultFound (resultShape.2.1.trans localType),
      bind, Except.bind]
    exact load_alias_after_store before true false metadataType _ _ after false false stored

end Compiler.Extraction.ExpressionMap.Receiver
