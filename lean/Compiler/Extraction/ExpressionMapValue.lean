/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapKeyWrites

namespace Compiler.Extraction.ExpressionMap.Buckets.Values
open Compiler.ZigAir.Memory
open Compiler.ZigAir.Memory.WordArray (word number)

def address (capacity bucket index : Nat) : Address := ⟨bucket, valuesOffset capacity + index * 4⟩
def pointer (capacity bucket index : Nat) : Value := .pointer (.pointer true false word) (address capacity bucket index)

def entryPointer (state : State) (capacity : BitVec 32) (bucket index : Nat) : Except Fault Value := do
  let values ← load state (Header.Slot.values.pointer capacity bucket)
  elementPointer state values index

def read (state : State) (capacity : BitVec 32) (bucket index : Nat) : Except Fault Value := do
  let target ← entryPointer state capacity bucket index
  load state target

theorem views (capacity index : Nat) (bounded : capacity < 2 ^ 32) (inside : index < capacity) :
    acceptsView (storageType capacity) (valuesOffset capacity + index * 4) word = true ∧
      leafType (storageType capacity) (valuesOffset capacity + index * 4) = some word := by
  have checked := storage_valid capacity (by omega)
  have geometry := Buckets.geometry capacity bounded
  have header : ¬valuesOffset capacity + index * 4 < 24 := by omega
  have metadata : ¬valuesOffset capacity + index * 4 < 24 + capacity := by omega
  have keys : ¬valuesOffset capacity + index * 4 < keysOffset capacity + capacity * 64 := by omega
  have nonzero : valuesOffset capacity + index * 4 ≠ 0 := by omega
  have values : valuesOffset capacity + index * 4 < valuesOffset capacity + capacity * 4 := by omega
  have lower : valuesOffset capacity ≤ valuesOffset capacity + index * 4 := by omega
  have difference : valuesOffset capacity + index * 4 - valuesOffset capacity = index * 4 := by omega
  simp only [acceptsView, leafType, storageType, Ty.project, nonzero, decide_false,
    Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, checked]
  simp [storageFields, Field.contains, Field.layout, header_layout, metadata_layout, key_layout, Ty.layout,
    header, metadata, keys, values, lower, difference, word, Ty.project, inside]

theorem access_entry (state : State) (capacity bucket index : Nat) (cell : Allocation)
    (bounded : capacity < 2 ^ 32) (inside : index < capacity) (valid : state.valid = true)
    (found : state.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity) :
    access state (address capacity bucket index) ⟨4, 4⟩ false = .ok cell := by
  have geometry := Buckets.geometry capacity bounded
  have root := root_access state bucket cell ⟨bytes capacity, 16⟩ false valid found
    (typed ▸ storage_layout capacity (by omega)) (by dsimp; omega) (by simp)
  have aligned : (valuesOffset capacity + index * 4) % 4 = 0 := by omega
  simpa only [address, Nat.zero_add] using access_subregion state ⟨bucket, 0⟩ ⟨bytes capacity, 16⟩ ⟨4, 4⟩
    (valuesOffset capacity + index * 4) false cell root (by decide) (by dsimp; omega) aligned
    (by change 16 % 4 = 0; decide)

theorem entry_pointer (state : State) (capacity : BitVec 32) (bucket index : Nat) (cell : Allocation)
    (inside : index < capacity.toNat) (valid : state.valid = true)
    (found : state.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity.toNat)
    (header : load state (Header.Slot.values.pointer capacity bucket) = .ok (Header.Slot.values.value capacity bucket)) :
    entryPointer state capacity bucket index = .ok (pointer capacity.toNat bucket index) := by
  have start := access_narrow state (address capacity.toNat bucket 0) ⟨4, 4⟩ 0 false cell
    (access_entry state capacity.toNat bucket 0 cell capacity.isLt (by omega) valid found typed) (by decide)
  have finish := access_entry state capacity.toNat bucket index cell capacity.isLt inside valid found typed
  simp only [address, Nat.zero_mul, Nat.add_zero] at start finish
  simp only [entryPointer, header, Header.Slot.value, bind, Except.bind]
  exact elementPointer_of_access state true word ⟨bucket, valuesOffset capacity.toNat⟩ index ⟨4, 4⟩ cell
    rfl (by decide) start finish

theorem store_total (state : State) (capacity bucket index : Nat) (cell : Allocation) (id : BitVec 32)
    (bounded : capacity < 2 ^ 32) (inside : index < capacity) (valid : state.valid = true)
    (found : state.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity)
    (writable : cell.writable = true) :
    ∃ after, store state (pointer capacity bucket index) (number id) = .ok after := by
  have accessed := access_read_write state (address capacity bucket index) ⟨4, 4⟩ cell
    (access_entry state capacity bucket index cell bounded inside valid found typed) writable
  have viewed := views capacity index bounded inside
  exact store_subobject_total state (address capacity bucket index) ⟨4, 4⟩ cell (number id)
    (WordArray.number_valid id) rfl accessed (typed ▸ viewed.1)
    (by intro entry member; simp only [number, Value.leaves, List.mem_singleton] at member; subst entry
        simpa only [address, Nat.add_zero, typed] using viewed.2)

theorem store_frame (before after : State) (capacity bucket index : Nat) (id : BitVec 32)
    (stored : store before (pointer capacity bucket index) (number id) = .ok after)
    (writable many : Bool) (child : Ty) (queried : Nat)
    (apart : ∀ position ∈ child.readOffsets queried, position ≠ valuesOffset capacity + index * 4) :
    load after (.pointer (.pointer writable many child) ⟨bucket, queried⟩) =
      load before (.pointer (.pointer writable many child) ⟨bucket, queried⟩) := by
  apply load_disjoint_after_store before true false word (address capacity bucket index) (number id)
    after writable many child queried stored
  intro position member entry written
  simp only [number, Value.leaves, List.mem_singleton] at written
  subst entry
  exact apart position member

theorem header_frame (before after : State) (capacity bucket index : Nat) (id : BitVec 32)
    (bounded : capacity < 2 ^ 32)
    (stored : store before (pointer capacity bucket index) (number id) = .ok after)
    (word : BitVec 32) (slot : Header.Slot) :
    load after (slot.pointer word bucket) = load before (slot.pointer word bucket) := by
  apply store_frame before after capacity bucket index id stored true false (slot.value word bucket).type slot.offset
  have geometry := Buckets.geometry capacity bounded
  cases slot <;> simp [Header.Slot.value, Header.Slot.offset, Value.type, Compiler.ZigAir.Scalar.Value.type,
    Ty.readOffsets] <;> omega

/-- A value store preserves every key in the component, not just its paired
key. Both slice leaves are retained, including the borrowed pointer identity. -/
theorem key_frame (before after : State) (capacity bucket index : Nat) (id : BitVec 32)
    (bounded : capacity < 2 ^ 32)
    (stored : store before (pointer capacity bucket index) (number id) = .ok after)
    (other : Nat) (inside : other < capacity) (key : Compiler.Extraction.Cache.Key) (arguments : Address) (slot : KeyFields.Slot) :
    load after (KeyFields.field capacity bucket other key arguments slot) =
      load before (KeyFields.field capacity bucket other key arguments slot) := by
  apply store_frame before after capacity bucket index id stored true false
    (KeyFields.value key arguments slot).type ((KeyFields.address capacity bucket other).offset + KeyFields.offset slot)
  have geometry := Buckets.geometry capacity bounded
  cases slot <;> simp [KeyFields.value, KeyFields.address, KeyFields.offset, Value.type,
    Compiler.ZigAir.Scalar.Value.type, Ty.readOffsets] <;> omega

theorem value_frame (before after : State) (capacity bucket index : Nat) (id : BitVec 32)
    (stored : store before (pointer capacity bucket index) (number id) = .ok after)
    (other : Nat) (apart : other ≠ index) :
    load after (pointer capacity bucket other) = load before (pointer capacity bucket other) := by
  apply store_frame before after capacity bucket index id stored true false word (valuesOffset capacity + other * 4)
  simp only [Ty.readOffsets, List.mem_singleton]
  intro position same
  omega

theorem read_eq (state : State) (capacity : BitVec 32) (bucket index : Nat) (cell : Allocation)
    (inside : index < capacity.toNat) (valid : state.valid = true)
    (found : state.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity.toNat)
    (header : load state (Header.Slot.values.pointer capacity bucket) = .ok (Header.Slot.values.value capacity bucket)) :
    read state capacity bucket index = load state (pointer capacity.toNat bucket index) := by
  simp only [read, entry_pointer state capacity bucket index cell inside valid found typed header, bind, Except.bind]

end Compiler.Extraction.ExpressionMap.Buckets.Values
