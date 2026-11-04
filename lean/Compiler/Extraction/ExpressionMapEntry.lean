/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapValue
import Compiler.Extraction.ExpressionMapMetadata

namespace Compiler.Extraction.ExpressionMap.Buckets.Entry
open Compiler.ZigAir.Memory
open Compiler.ZigAir.Memory.WordArray (word number)
open Compiler.Extraction.Cache (Key)

/-- Stores through the two pointers already returned by native getOrPut. -/
def writePointers (keyPointer valuePointer : Value) (key : Key) (arguments : Address) (id : BitVec 32)
    (before : State) : Except Fault Unit × State :=
  match KeyFields.writes keyPointer key arguments KeyFields.order before with
  | (.error fault, keyed) => (.error fault, keyed)
  | (.ok (), keyed) => match store keyed valuePointer (number id) with
    | .error fault => (.error fault, keyed)
    | .ok after => (.ok (), after)

/-- The defined assignment tail after getOrPut and any old-argument release.
Both entry pointers are selected before either store, as in the native result;
probing and release are separate preceding obligations. -/
def assign (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address) (id : BitVec 32)
    (before : State) : Except Fault Unit × State :=
  match KeyFields.entryPointer before capacity bucket index with
  | .error fault => (.error fault, before)
  | .ok keyPointer => match Values.entryPointer before capacity bucket index with
    | .error fault => (.error fault, before)
    | .ok valuePointer => writePointers keyPointer valuePointer key arguments id before

structure Stored (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address) (id : BitVec 32)
    (state : State) : Prop where
  keys : ∀ slot, KeyFields.read capacity bucket index slot state = .ok (KeyFields.value key arguments slot)
  value : Values.read state capacity bucket index = .ok (number id)

/-- The actual intermediate key state is retained. The final value store must
consume it; successful execution of either assignment is not an input premise. -/
structure Completed (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address) (id : BitVec 32)
    (before keyed after : State) : Prop where
  keyRun : KeyFields.assign capacity bucket index key arguments before = (.ok (), keyed)
  keys : KeyFields.Written capacity.toNat bucket index key arguments KeyFields.order before keyed
  valueStore : store keyed (Values.pointer capacity.toNat bucket index) (number id) = .ok after

theorem writePointers_steps (keyPointer valuePointer : Value) (key : Key) (arguments : Address) (id : BitVec 32)
    (before keyed after : State)
    (writes : KeyFields.writes keyPointer key arguments KeyFields.order before = (.ok (), keyed))
    (stored : store keyed valuePointer (number id) = .ok after) :
    writePointers keyPointer valuePointer key arguments id before = (.ok (), after) := by
  simp only [writePointers, writes, stored]

theorem assign_steps (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address) (id : BitVec 32)
    (before keyed after : State) (keyPointer valuePointer : Value)
    (keys : KeyFields.entryPointer before capacity bucket index = .ok keyPointer)
    (values : Values.entryPointer before capacity bucket index = .ok valuePointer)
    (writes : KeyFields.writes keyPointer key arguments KeyFields.order before = (.ok (), keyed))
    (stored : store keyed valuePointer (number id) = .ok after) :
    assign capacity bucket index key arguments id before = (.ok (), after) := by
  simp only [assign, writePointers, keys, values, writes, stored]

theorem write_pointers_verified (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address) (id : BitVec 32)
    (before : State) (cell : Allocation) (inside : index < capacity.toNat)
    (valid : before.valid = true) (found : before.heap.lookup bucket = some cell)
    (typed : cell.type = storageType capacity.toNat) (writable : cell.writable = true)
    (length : key.arguments.length < addressLimit)
    (headers : ∀ slot, load before (Header.Slot.pointer slot capacity bucket) = .ok (Header.Slot.value slot capacity bucket)) :
    ∃ keyed after, writePointers (.pointer (.pointer true false keyType) (KeyFields.address capacity.toNat bucket index))
      (Values.pointer capacity.toNat bucket index) key arguments id before = (.ok (), after) ∧
      Completed capacity bucket index key arguments id before keyed after := by
  obtain ⟨keyed, keyRun, keys, _⟩ := KeyFields.assign_verified capacity bucket index key arguments before cell
    inside valid found typed writable length (headers .keys)
  obtain ⟨keyedCell, keyedFound, shape⟩ := keys.shape bucket cell found
  obtain ⟨after, valueStore⟩ := Values.store_total keyed capacity.toNat bucket index keyedCell id capacity.isLt inside
    keys.valid keyedFound (shape.2.1.trans typed) (shape.2.2.1.trans writable)
  have keyPointer := KeyFields.entry_pointer before capacity bucket index cell inside valid found typed (headers .keys)
  have writes := keyRun
  simp only [KeyFields.assign, keyPointer] at writes
  exact ⟨keyed, after, writePointers_steps _ _ key arguments id before keyed after writes valueStore, ⟨keyRun, keys, valueStore⟩⟩

theorem assign_verified (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address) (id : BitVec 32)
    (before : State) (cell : Allocation) (inside : index < capacity.toNat)
    (valid : before.valid = true) (found : before.heap.lookup bucket = some cell)
    (typed : cell.type = storageType capacity.toNat) (writable : cell.writable = true)
    (length : key.arguments.length < addressLimit)
    (headers : ∀ slot, load before (Header.Slot.pointer slot capacity bucket) = .ok (Header.Slot.value slot capacity bucket)) :
    ∃ keyed after, assign capacity bucket index key arguments id before = (.ok (), after) ∧
      Completed capacity bucket index key arguments id before keyed after := by
  obtain ⟨keyed, after, _, post⟩ := write_pointers_verified capacity bucket index key arguments id before cell
    inside valid found typed writable length headers
  have keyPointer := KeyFields.entry_pointer before capacity bucket index cell inside valid found typed (headers .keys)
  have valuePointer := Values.entry_pointer before capacity bucket index cell inside valid found typed (headers .values)
  have writes := post.keyRun
  simp only [KeyFields.assign, keyPointer] at writes
  exact ⟨keyed, after, assign_steps capacity bucket index key arguments id before keyed after _ _
    keyPointer valuePointer writes post.valueStore, post⟩

variable {capacity : BitVec 32} {bucket index : Nat} {key : Key} {arguments : Address} {id : BitVec 32}
  {before keyed after : State}

theorem Completed.native_frame (post : Completed capacity bucket index key arguments id before keyed after) :
    after.valid = true ∧ before.heap.RetainsShape after.heap ∧
      (∀ other, other ≠ bucket → after.heap.lookup other = before.heap.lookup other) ∧
      after.nextId = before.nextId ∧ after.nextAddress = before.nextAddress := by
  exact ⟨store_preserves_valid _ _ _ _ post.keys.valid post.valueStore,
    post.keys.shape.trans (store_retains_shape _ _ _ _ post.valueStore),
    fun other apart => (heap_after_store_other _ true false word _ _ _ post.valueStore other apart).trans (post.keys.frame other apart),
    (store_keeps_counters _ _ _ _ post.valueStore).1.trans post.keys.nextId,
    (store_keeps_counters _ _ _ _ post.valueStore).2.trans post.keys.nextAddress⟩

theorem Completed.headers (post : Completed capacity bucket index key arguments id before keyed after) (slot : Header.Slot) :
    load after (slot.pointer capacity bucket) = load before (slot.pointer capacity bucket) :=
  (Values.header_frame _ _ capacity.toNat bucket index id capacity.isLt post.valueStore capacity slot).trans
    (post.keys.header capacity.isLt capacity slot)

/-- The complete pair retains every read outside its two footprints, including
uninitialized or rejected reads. This includes all other key/value entries. -/
theorem Completed.outside (post : Completed capacity bucket index key arguments id before keyed after)
    (writable many : Bool) (child : Ty) (queried : Nat)
    (keyApart : KeyFields.Outside capacity.toNat index child queried)
    (valueApart : ∀ position ∈ child.readOffsets queried, position ≠ valuesOffset capacity.toNat + index * 4) :
    load after (.pointer (.pointer writable many child) ⟨bucket, queried⟩) =
      load before (.pointer (.pointer writable many child) ⟨bucket, queried⟩) :=
  (Values.store_frame _ _ capacity.toNat bucket index id post.valueStore writable many child queried valueApart).trans
    (post.keys.outside writable many child queried keyApart)

theorem Completed.other_values (post : Completed capacity bucket index key arguments id before keyed after)
    (inside : index < capacity.toNat) (other : Nat) (apart : other ≠ index) :
    load after (Values.pointer capacity.toNat bucket other) = load before (Values.pointer capacity.toNat bucket other) := by
  have geometry := Buckets.geometry capacity.toNat capacity.isLt
  have keyApart : KeyFields.Outside capacity.toNat index word (valuesOffset capacity.toNat + other * 4) := by
    intro position member
    simp only [Ty.readOffsets, List.mem_singleton] at member
    subst position
    right
    omega
  exact (Values.value_frame _ _ capacity.toNat bucket index id post.valueStore other apart).trans
    (post.keys.outside true false word (valuesOffset capacity.toNat + other * 4) keyApart)

theorem Completed.metadata_load (post : Completed capacity bucket index key arguments id before keyed after)
    (other : Nat) (inside : other < capacity.toNat) :
    load after (Metadata.pointer bucket other) = load before (Metadata.pointer bucket other) := by
  have geometry := Buckets.geometry capacity.toNat capacity.isLt
  have keyApart : KeyFields.Outside capacity.toNat index Metadata.byte (24 + other) := by
    intro position member
    simp only [Metadata.byte, Ty.readOffsets, List.mem_singleton] at member
    subst position
    left
    omega
  have valueApart : ∀ position ∈ Metadata.byte.readOffsets (24 + other),
      position ≠ valuesOffset capacity.toNat + index * 4 := by
    simp only [Metadata.byte, Ty.readOffsets, List.mem_singleton]
    intro position same
    omega
  have loaded := post.outside true false Metadata.byte (24 + other) keyApart valueApart
  change load after (Metadata.pointer bucket other) = load before (Metadata.pointer bucket other) at loaded
  exact loaded

theorem Completed.metadata_frame (post : Completed capacity bucket index key arguments id before keyed after)
    (other : Nat) (inside : other < capacity.toNat) :
    Metadata.observe after bucket other = Metadata.observe before bucket other := by
  simp only [Metadata.observe, post.metadata_load other inside]

theorem Completed.stored (post : Completed capacity bucket index key arguments id before keyed after)
    (cell : Allocation) (inside : index < capacity.toNat) (found : before.heap.lookup bucket = some cell)
    (typed : cell.type = storageType capacity.toNat)
    (headers : ∀ slot : Header.Slot, load before (slot.pointer capacity bucket) = .ok (slot.value capacity bucket)) :
    Stored capacity bucket index key arguments id after := by
  have frame := post.native_frame
  obtain ⟨afterCell, afterFound, shape⟩ := frame.2.1 bucket cell found
  constructor
  · intro slot
    rw [KeyFields.read_eq capacity bucket index slot after afterCell key arguments inside frame.1 afterFound
      (shape.2.1.trans typed) ((post.headers .keys).trans (headers .keys))]
    rw [Values.key_frame _ _ capacity.toNat bucket index id capacity.isLt post.valueStore index inside key arguments slot,
      post.keys.reads]
    have member : slot ∈ KeyFields.order := by cases slot <;> simp [KeyFields.order]
    simp only [member, ↓reduceIte]
  · rw [Values.read_eq after capacity bucket index afterCell inside frame.1 afterFound
      (shape.2.1.trans typed) ((post.headers .values).trans (headers .values))]
    exact load_after_store _ _ _ _ post.valueStore

/-- Failed selection does not begin assignment; later failures preserve the
actual completed prefix. These equations do not turn memory faults into OOM. -/
theorem selection_rejected (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address) (id : BitVec 32)
    (before : State) (keyPointer : Value) (fault : Fault)
    (keys : KeyFields.entryPointer before capacity bucket index = .ok keyPointer)
    (values : Values.entryPointer before capacity bucket index = .error fault) :
    assign capacity bucket index key arguments id before = (.error fault, before) := by
  simp only [assign, keys, values]

theorem value_rejected (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address) (id : BitVec 32)
    (before keyed : State) (keyPointer valuePointer : Value) (fault : Fault)
    (keys : KeyFields.entryPointer before capacity bucket index = .ok keyPointer)
    (values : Values.entryPointer before capacity bucket index = .ok valuePointer)
    (writes : KeyFields.writes keyPointer key arguments KeyFields.order before = (.ok (), keyed))
    (rejected : store keyed valuePointer (number id) = .error fault) :
    assign capacity bucket index key arguments id before = (.error fault, keyed) := by
  simp only [assign, writePointers, keys, values, writes, rejected]

end Compiler.Extraction.ExpressionMap.Buckets.Entry
