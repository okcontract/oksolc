/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapBucketStorage
import Compiler.Extraction.CacheIR

namespace Compiler.Extraction.ExpressionMap.Buckets.KeyFields
open Compiler.ZigAir.Memory
open Compiler.Extraction.Cache (Key)
abbrev Slot := Compiler.Extraction.Cache.Field

def value (key : Key) (arguments : Address) : Slot → Value
  | .kind => .scalar (.int false 32 key.kind.toNat)
  | .instruction => .scalar (.int false 8 key.instruction.toNat)
  | .data => .scalar (.int false 256 key.data.toNat)
  | .arguments => .slice (.slice false (.scalar (.int false 32))) arguments key.arguments.length
  | .sequence => .scalar (.int false 32 key.sequence.toNat)

def address (capacity bucket index : Nat) : Address := ⟨bucket, keysOffset capacity + index * 64⟩
def field (capacity bucket index : Nat) (key : Key) (arguments : Address) (slot : Slot) : Value :=
  .pointer (.pointer true false (value key arguments slot).type)
    ⟨bucket, (address capacity bucket index).offset + offset slot⟩

def select (state : State) (capacity bucket index : Nat) (slot : Slot) : Except Fault Value :=
  fieldPointer state (.pointer (.pointer true false keyType) (address capacity bucket index)) (offset slot)

theorem value_valid (key : Key) (arguments : Address) (bounded : key.arguments.length < addressLimit) (slot : Slot) :
    (value key arguments slot).valid = true := by
  have kind := key.kind.isLt
  have instruction := key.instruction.isLt
  have data := key.data.isLt
  have sequence := key.sequence.isLt
  cases slot <;> simp [value, Value.valid, Compiler.ZigAir.Scalar.Value.valid,
    Compiler.ZigAir.Scalar.Ty.contains, Compiler.ZigAir.Scalar.Ty.lower, Compiler.ZigAir.Scalar.Ty.upper]
  all_goals omega

theorem region (capacity index : Nat) (bounded : capacity < 2 ^ 32) (inside : index < capacity) :
    keysOffset capacity + index * 64 + 64 ≤ bytes capacity ∧
      (keysOffset capacity + index * 64) % 16 = 0 := by
  have geometry := Buckets.geometry capacity bounded
  constructor
  · have : index * 64 + 64 ≤ capacity * 64 := by omega
    omega
  · omega

/-- Every key subobject is selected inside the existing component array. The
same projection serves whole-key selectors, field views and slice leaves. -/
theorem project_key (capacity index relative : Nat) (bounded : capacity < 2 ^ 32)
    (inside : index < capacity) (member : relative < 64) (choose : Ty → Bool)
    (notArray : choose (.array capacity keyType) = false) :
    Ty.project choose (storageType capacity) (keysOffset capacity + index * 64 + relative) =
      Ty.project choose keyType relative := by
  have checked := storage_valid capacity (by omega)
  have geometry := Buckets.geometry capacity bounded
  have header : ¬keysOffset capacity + index * 64 + relative < 24 := by omega
  have metadata : ¬keysOffset capacity + index * 64 + relative < 24 + capacity := by omega
  have nonzero : keysOffset capacity + index * 64 + relative ≠ 0 := by omega
  have keys : keysOffset capacity + index * 64 + relative < keysOffset capacity + capacity * 64 := by omega
  have lower : keysOffset capacity ≤ keysOffset capacity + index * 64 + relative := by omega
  have difference : keysOffset capacity + index * 64 + relative - keysOffset capacity = index * 64 + relative := by omega
  have quotient : (index * 64 + relative) / 64 = index := by omega
  have remainder : (index * 64 + relative) % 64 = relative := by omega
  simp only [storageType, Ty.project, nonzero, decide_false, Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte, checked]
  simp [storageFields, Field.contains, Field.layout, header_layout, metadata_layout, key_layout, Ty.layout,
    header, metadata, keys, lower, difference, notArray, quotient, remainder, inside]

theorem key_view (capacity index : Nat) (bounded : capacity < 2 ^ 32) (inside : index < capacity) :
    acceptsView (storageType capacity) (keysOffset capacity + index * 64) keyType = true := by
  have projected := project_key capacity index 0 bounded inside (by decide) (fun t => decide (t = keyType))
    (by simp [keyType])
  change (Ty.project (fun t => decide (t = keyType)) _ _).isSome = true
  simpa only [Nat.add_zero, Ty.project_root (fun t => decide (t = keyType)) keyType (by simp), Option.isSome_some] using congrArg Option.isSome projected

theorem field_views (capacity index : Nat) (bounded : capacity < 2 ^ 32) (inside : index < capacity)
    (key : Key) (arguments : Address) (slot : Slot) :
    acceptsView (storageType capacity) (keysOffset capacity + index * 64 + offset slot) (value key arguments slot).type = true ∧
      ∀ entry ∈ (value key arguments slot).leaves 0,
        leafType (storageType capacity) (keysOffset capacity + index * 64 + offset slot + entry.1) = some entry.2.type := by
  constructor
  · unfold acceptsView
    rw [project_key capacity index (offset slot) bounded inside (by cases slot <;> decide) _
      (by cases slot <;> rfl)]
    cases slot <;> rfl
  · intro entry member
    have small : offset slot + entry.1 < 64 := by
      cases slot <;> simp_all [value, Value.leaves, offset]
      rcases member with rfl | rfl <;> omega
    unfold leafType
    rw [Nat.add_assoc, project_key capacity index (offset slot + entry.1) bounded inside small _ rfl]
    cases slot <;> simp_all [value, Value.leaves, offset] <;> rcases member with rfl | rfl <;> rfl

theorem field_selected (key : Key) (arguments : Address) (slot : Slot) :
    fieldType keyType (offset slot) = some (value key arguments slot).type := by
  cases slot <;> rfl

/-- Checked native element arithmetic, including the zero-byte checks used
by many-pointer arithmetic. The complete key remains inside its component. -/
theorem access_entry (state : State) (capacity bucket index width : Nat) (cell : Allocation)
    (bounded : capacity < 2 ^ 32) (inside : index < capacity) (widthBound : width ≤ 64)
    (valid : state.valid = true) (found : state.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity)
    (write : Bool) (permitted : write = true → cell.writable = true) :
    access state (address capacity bucket index) ⟨width, 16⟩ write = .ok cell := by
  obtain ⟨_, basePositive, actual, actualShape, aligned, extentBound, limit⟩ := valid_lookup state bucket cell valid found
  have shaped := typed ▸ storage_layout capacity (by omega)
  have same := Option.some.inj (actualShape.symm.trans shaped)
  subst actual
  have region := region capacity index bounded inside
  have geometry := Buckets.geometry capacity bounded
  have entryAligned : (cell.base + (keysOffset capacity + index * 64)) % 16 = 0 := by
    change cell.base % 16 = 0 at aligned
    omega
  have checks : ¬(cell.base = 0 ∨ cell.base + bytes capacity > addressLimit ∨
      cell.base + (keysOffset capacity + index * 64) ≥ addressLimit ∨
      keysOffset capacity + index * 64 + width > bytes capacity ∨
      (cell.base + (keysOffset capacity + index * 64)) % 16 ≠ 0) := by
    dsimp only at extentBound
    omega
  cases write <;> simp only [access, address, found, shaped, Bool.false_and, Bool.false_eq_true, ↓reduceIte, if_neg checks]
  simp only [permitted rfl, Bool.not_true, Bool.true_and, Bool.false_eq_true, ↓reduceIte]

/-- Read the actual keys pointer, then execute the memory model's checked
pointer offset and element cast. No selected entry pointer is a premise. -/
def entryPointer (state : State) (capacity : BitVec 32) (bucket index : Nat) : Except Fault Value := do
  let keys ← load state (Header.Slot.keys.pointer capacity bucket)
  elementPointer state keys index

theorem entry_pointer (state : State) (capacity : BitVec 32) (bucket index : Nat) (cell : Allocation)
    (inside : index < capacity.toNat) (valid : state.valid = true)
    (found : state.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity.toNat)
    (header : load state (Header.Slot.keys.pointer capacity bucket) = .ok (Header.Slot.keys.value capacity bucket)) :
    entryPointer state capacity bucket index =
      .ok (.pointer (.pointer true false keyType) (address capacity.toNat bucket index)) := by
  have start := access_entry state capacity.toNat bucket 0 0 cell capacity.isLt (by omega) (by decide) valid found typed false (by simp)
  have complete := access_entry state capacity.toNat bucket index 64 cell capacity.isLt inside (by decide) valid found typed false (by simp)
  simp only [address, Nat.zero_mul, Nat.add_zero] at start complete
  simp only [entryPointer, header, Header.Slot.value, bind, Except.bind]
  exact elementPointer_of_access state true keyType ⟨bucket, keysOffset capacity.toNat⟩ index ⟨64, 16⟩ cell
    key_layout (by decide) start complete

theorem select_verified (state : State) (capacity bucket index : Nat) (cell : Allocation) (key : Key) (arguments : Address)
    (bounded : capacity < 2 ^ 32) (inside : index < capacity) (valid : state.valid = true)
    (found : state.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity) (slot : Slot) :
    select state capacity bucket index slot = .ok (field capacity bucket index key arguments slot) := by
  exact fieldPointer_of_access state (address capacity bucket index) cell keyType (value key arguments slot).type
    ⟨64, 16⟩ (offset slot) true false key_layout
    (access_entry state capacity bucket index 64 cell bounded inside (by decide) valid found typed false (by simp))
    (typed ▸ key_view capacity index bounded inside) (field_selected key arguments slot)

def layout : Slot → Layout
  | .kind | .sequence => ⟨4, 4⟩ | .instruction => ⟨1, 1⟩ | .data => ⟨32, 16⟩ | .arguments => ⟨16, 8⟩

theorem field_geometry (key : Key) (arguments : Address) (slot : Slot) :
    (value key arguments slot).type.layout = some (layout slot) ∧
      0 < (layout slot).bytes ∧ offset slot + (layout slot).bytes ≤ 64 ∧
      offset slot % (layout slot).alignment = 0 ∧ 16 % (layout slot).alignment = 0 := by
  cases slot <;> simp [layout, offset, value, Value.type, Compiler.ZigAir.Scalar.Value.type, Ty.layout]

theorem store_total (state : State) (capacity bucket index : Nat) (cell : Allocation) (key : Key) (arguments : Address)
    (bounded : capacity < 2 ^ 32) (inside : index < capacity) (valid : state.valid = true)
    (found : state.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity)
    (writable : cell.writable = true) (length : key.arguments.length < addressLimit) (slot : Slot) :
    ∃ after, store state (field capacity bucket index key arguments slot) (value key arguments slot) = .ok after := by
  have keyAccess := access_entry state capacity bucket index 64 cell bounded inside (by decide)
    valid found typed true (fun _ => writable)
  obtain ⟨shaped, positive, endBound, aligned, divided⟩ := field_geometry key arguments slot
  have fieldAccess := access_subregion state (address capacity bucket index) ⟨64, 16⟩ (layout slot)
    (offset slot) true cell keyAccess positive endBound aligned divided
  have views := field_views capacity index bounded inside key arguments slot
  exact store_subobject_total state _ (layout slot) cell (value key arguments slot)
    (value_valid key arguments length slot) shaped fieldAccess (typed ▸ views.1) (typed ▸ views.2)

def writeAt (source : Value) (key : Key) (arguments : Address) (slot : Slot) (state : State) : Except Fault State := do
  let target ← fieldPointer state source (offset slot)
  store state target (value key arguments slot)

def write (capacity bucket index : Nat) (key : Key) (arguments : Address) (slot : Slot) (state : State) : Except Fault State :=
  writeAt (.pointer (.pointer true false keyType) (address capacity bucket index)) key arguments slot state

theorem write_total (state : State) (capacity bucket index : Nat) (cell : Allocation) (key : Key) (arguments : Address)
    (bounded : capacity < 2 ^ 32) (inside : index < capacity) (valid : state.valid = true)
    (found : state.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity)
    (writable : cell.writable = true) (length : key.arguments.length < addressLimit) (slot : Slot) :
    ∃ after, write capacity bucket index key arguments slot state = .ok after ∧
      store state (field capacity bucket index key arguments slot) (value key arguments slot) = .ok after := by
  obtain ⟨after, stored⟩ := store_total state capacity bucket index cell key arguments bounded inside valid found typed writable length slot
  refine ⟨after, ?_, stored⟩
  change (do let target ← select state capacity bucket index slot; store state target (value key arguments slot)) = .ok after
  simp only [select_verified state capacity bucket index cell key arguments bounded inside valid found typed slot, bind, Except.bind, stored]

theorem read_other (before after : State) (capacity bucket index : Nat) (key : Key) (arguments : Address) (written read : Slot)
    (stored : store before (field capacity bucket index key arguments written) (value key arguments written) = .ok after)
    (apart : read ≠ written) :
    load after (field capacity bucket index key arguments read) = load before (field capacity bucket index key arguments read) := by
  apply load_disjoint_after_store before true false _ _ _ after true false _ _ stored
  cases written <;> cases read <;> simp_all [field, address, offset, value, Value.leaves, Value.type,
    Compiler.ZigAir.Scalar.Value.type, Ty.readOffsets] <;> omega

end Compiler.Extraction.ExpressionMap.Buckets.KeyFields
