/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapBucketStorageLayout
import Compiler.Extraction.ExpressionMapBucketReservation

namespace Compiler.Extraction.ExpressionMap.Buckets
open Compiler.ZigAir.Memory

theorem key_layout : keyType.layout = some ⟨64, 16⟩ := by rfl

theorem header_layout : headerType.layout = some ⟨24, 8⟩ := by rfl

theorem metadata_layout : metadataType.layout = some ⟨1, 1⟩ := by rfl

theorem storage_valid (capacity : Nat) (positive : 0 < capacity) :
    Ty.aggregateValid ⟨bytes capacity, 16⟩ (storageFields capacity) = true := by
  simp [Ty.aggregateValid, checkFields, storageFields, Field.layouts, Field.layout,
    header_layout, metadata_layout, key_layout, Ty.layout, List.pairwise_cons,
    bytes, valuesOffset, keysOffset, alignForward, headerBytes, metadataBytes,
    keyBytes, keyAlignment, valueBytes, valueAlignment, allocationAlignment]
  omega

theorem storage_layout (capacity : Nat) (positive : 0 < capacity) :
    (storageType capacity).layout = some ⟨bytes capacity, 16⟩ := by
  have checked : checkFields ⟨bytes capacity, 16⟩ (Field.layouts (storageFields capacity)) = true :=
    storage_valid capacity positive
  simp only [storageType, Ty.layout, checked, ↓reduceIte]

namespace Header

inductive Slot where
  | values | keys | capacity
  deriving DecidableEq, Repr

def Slot.offset : Slot → Nat
  | .values => 0 | .keys => 8 | .capacity => 16

def Slot.value (slot : Slot) (capacity : BitVec 32) (id : Nat) : Value := match slot with
  | .values => .pointer (.pointer true true (.scalar (.int false 32))) ⟨id, valuesOffset capacity.toNat⟩
  | .keys => .pointer (.pointer true true keyType) ⟨id, keysOffset capacity.toNat⟩
  | .capacity => .scalar (.int false 32 capacity.toNat)

theorem slot_views (capacity : Nat) (positive : 0 < capacity) (slot : Slot) (word : BitVec 32) (id : Nat) :
    acceptsView (storageType capacity) slot.offset (slot.value word id).type = true ∧
    leafType (storageType capacity) slot.offset = some (slot.value word id).type := by
  have valid := storage_valid capacity positive
  cases slot <;>
    simp [Slot.offset, Slot.value, Value.type, Compiler.ZigAir.Scalar.Value.type,
      acceptsView, leafType, storageType, valid]
  all_goals
    simp [storageFields, Field.contains, Field.layout, headerType,
      Ty.aggregateValid, checkFields, Field.layouts, Ty.layout, Field.type]

def Slot.pointer (slot : Slot) (capacity : BitVec 32) (id : Nat) : Value :=
  .pointer (.pointer true false (slot.value capacity id).type) ⟨id, slot.offset⟩

theorem value_valid (slot : Slot) (capacity : BitVec 32) (id : Nat) :
    (slot.value capacity id).valid = true := by
  cases slot with
  | values | keys => rfl
  | capacity => exact WordArray.number_valid capacity

/-- A proof-side view of the native pointer/alignment casts. It checks the
complete declared array in the original allocation; it supplies no payload. -/
def arrayPointer (state : State) (child : Ty) (capacity : Nat) (address : Address) : Except Fault Value := do
  let target := Ty.array capacity child
  let some layout := target.layout | .error .unsupported
  let cell ← access state address layout true
  if !acceptsView cell.type address.offset target then .error .unsupported else
  .ok (.pointer (.pointer true true child) address)

def Slot.checkedValue (slot : Slot) (capacity : BitVec 32) (id : Nat) (state : State) : Except Fault Value := match slot with
  | .values => arrayPointer state (.scalar (.int false 32)) capacity.toNat ⟨id, (sourceValues capacity).toNat⟩
  | .keys => arrayPointer state keyType capacity.toNat ⟨id, (sourceKeys capacity).toNat⟩
  | .capacity => .ok (slot.value capacity id)

theorem array_views (capacity : Nat) (positive : 0 < capacity) (bounded : capacity < 2 ^ 32) :
    acceptsView (storageType capacity) (keysOffset capacity) (.array capacity keyType) = true ∧
    acceptsView (storageType capacity) (valuesOffset capacity) (.array capacity (.scalar (.int false 32))) = true := by
  have checked := storage_valid capacity positive
  have ranges := geometry capacity bounded
  have keyHeader : ¬keysOffset capacity < 24 := by omega
  have valueHeader : ¬valuesOffset capacity < 24 := by omega
  have keyMeta : ¬keysOffset capacity < 24 + capacity := by omega
  have valueMeta : ¬valuesOffset capacity < 24 + capacity := by omega
  have valueKey : ¬valuesOffset capacity < keysOffset capacity + capacity * 64 := by omega
  simp [storageType, acceptsView, checked]
  simp [storageFields, Field.contains, Field.layout, header_layout, metadata_layout, key_layout, Ty.layout,
    keyHeader, valueHeader, keyMeta, valueMeta, valueKey, positive]

theorem checked_value (state : State) (id : Nat) (cell : Allocation) (capacity : BitVec 32)
    (slot : Slot) (positive : 0 < capacity.toNat) (valid : state.valid = true)
    (found : state.heap.lookup id = some cell) (typed : cell.type = storageType capacity.toNat)
    (writable : cell.writable = true) : slot.checkedValue capacity id state = .ok (slot.value capacity id) := by
  have ranges := geometry capacity.toNat capacity.isLt
  have root := root_access state id cell ⟨bytes capacity.toNat, 16⟩ true valid found
    (typed ▸ storage_layout capacity.toNat positive) ranges.2.2.2.2.2.2.1 (fun _ => writable)
  have views := array_views capacity.toNat positive capacity.isLt
  cases slot with
  | capacity => rfl
  | keys =>
    have accessed := access_subregion state ⟨id, 0⟩ ⟨bytes capacity.toNat, 16⟩ ⟨capacity.toNat * 64, 16⟩
      (keysOffset capacity.toNat) true cell root (by dsimp; omega) (by dsimp; omega) ranges.2.2.2.1
      (by change 16 % 16 = 0; decide)
    have layout : (Ty.array capacity.toNat keyType).layout = some ⟨capacity.toNat * 64, 16⟩ := rfl
    simp only [Nat.zero_add] at accessed
    simp only [Slot.checkedValue, (source_layout capacity).1, arrayPointer, layout, accessed, bind, Except.bind, typed, views.1,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, Slot.value]
  | values =>
    have accessed := access_subregion state ⟨id, 0⟩ ⟨bytes capacity.toNat, 16⟩ ⟨capacity.toNat * 4, 4⟩
      (valuesOffset capacity.toNat) true cell root (by dsimp; omega) ranges.2.2.1 ranges.2.2.2.2.1
      (by change 16 % 4 = 0; decide)
    have layout : (Ty.array capacity.toNat (.scalar (.int false 32))).layout = some ⟨capacity.toNat * 4, 4⟩ := rfl
    simp only [Nat.zero_add] at accessed
    simp only [Slot.checkedValue, (source_layout capacity).2.1, arrayPointer, layout, accessed, bind, Except.bind, typed, views.2,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, Slot.value]

def write (capacity : BitVec 32) (id : Nat) (slot : Slot) (state : State) : Except Fault State := do
  let value ← slot.checkedValue capacity id state
  store state (slot.pointer capacity id) value

/-- The actual three header stores, retaining the reached heap on rejection. -/
def writes (capacity : BitVec 32) (id : Nat) : List Slot → State → Except Fault Unit × State
  | [], state => (.ok (), state)
  | slot :: rest, state => match write capacity id slot state with
    | .error fault => (.error fault, state)
    | .ok after => writes capacity id rest after

def run (capacity : BitVec 32) (id : Nat) (state : State) : Except Fault Unit × State :=
  writes capacity id [.values, .keys, .capacity] state

theorem store_total (state : State) (id : Nat) (cell : Allocation) (capacity : BitVec 32)
    (slot : Slot) (positive : 0 < capacity.toNat) (valid : state.valid = true)
    (found : state.heap.lookup id = some cell) (typed : cell.type = storageType capacity.toNat)
    (writable : cell.writable = true) :
    ∃ after, store state (slot.pointer capacity id) (slot.value capacity id) = .ok after := by
  have geometry := geometry capacity.toNat capacity.isLt
  have root := root_access state id cell ⟨bytes capacity.toNat, 16⟩ true valid found
    (typed ▸ storage_layout capacity.toNat positive) geometry.2.2.2.2.2.2.1 (fun _ => writable)
  have views := slot_views capacity.toNat positive slot capacity id
  have leaves : (slot.value capacity id).leaves 0 = [(0, slot.value capacity id)] := by cases slot <;> rfl
  have region : ∃ layout, (slot.value capacity id).type.layout = some layout ∧
      0 < layout.bytes ∧ slot.offset + layout.bytes ≤ bytes capacity.toNat ∧
      slot.offset % layout.alignment = 0 ∧ 16 % layout.alignment = 0 := by
    have headerBound := geometry.1
    cases slot
    · exact ⟨⟨8, 8⟩, rfl, by decide, by dsimp [Slot.offset]; omega, rfl, rfl⟩
    · exact ⟨⟨8, 8⟩, rfl, by decide, by dsimp [Slot.offset]; omega, rfl, rfl⟩
    · exact ⟨⟨4, 4⟩, rfl, by decide, by dsimp [Slot.offset]; omega, rfl, rfl⟩
  obtain ⟨layout, shaped, nonempty, inside, aligned, divided⟩ := region
  have accessed := access_subregion state ⟨id, 0⟩ ⟨bytes capacity.toNat, 16⟩ layout slot.offset true cell
    root nonempty inside aligned divided
  exact store_subobject_total state ⟨id, slot.offset⟩ layout cell (slot.value capacity id)
    (value_valid slot capacity id) shaped (by simpa using accessed) (typed ▸ views.1)
    (by intro entry member; simp only [leaves, List.mem_singleton] at member; subst entry; simpa [typed] using views.2)

theorem read_other (before after : State) (capacity : BitVec 32) (id : Nat) (written read : Slot)
    (stored : store before (written.pointer capacity id) (written.value capacity id) = .ok after)
    (apart : read ≠ written) :
    load after (read.pointer capacity id) = load before (read.pointer capacity id) := by
  apply load_disjoint_after_store before true false _ ⟨id, written.offset⟩ _ after true false _ read.offset stored
  cases written <;> cases read <;> simp_all [Slot.value, Slot.offset, Value.leaves, Value.type,
    Compiler.ZigAir.Scalar.Value.type, Ty.readOffsets]

theorem writes_cons (capacity : BitVec 32) (id : Nat) (slot : Slot) (rest : List Slot) (before after : State)
    (checked : slot.checkedValue capacity id before = .ok (slot.value capacity id))
    (stored : store before (slot.pointer capacity id) (slot.value capacity id) = .ok after) :
    writes capacity id (slot :: rest) before = writes capacity id rest after := by
  rw [writes.eq_def]
  dsimp only
  rw [write, checked]
  dsimp only [bind, Except.bind]
  rw [stored]

theorem run_steps (capacity : BitVec 32) (id : Nat) (before values keys after : State)
    (firstCast : Slot.values.checkedValue capacity id before = .ok (Slot.values.value capacity id))
    (secondCast : Slot.keys.checkedValue capacity id values = .ok (Slot.keys.value capacity id))
    (thirdCast : Slot.capacity.checkedValue capacity id keys = .ok (Slot.capacity.value capacity id))
    (first : store before (Slot.values.pointer capacity id) (Slot.values.value capacity id) = .ok values)
    (second : store values (Slot.keys.pointer capacity id) (Slot.keys.value capacity id) = .ok keys)
    (third : store keys (Slot.capacity.pointer capacity id) (Slot.capacity.value capacity id) = .ok after) :
    run capacity id before = (.ok (), after) := by
  rw [run, writes_cons capacity id _ _ _ _ firstCast first, writes_cons capacity id _ _ _ _ secondCast second,
    writes_cons capacity id _ _ _ _ thirdCast third]
  rfl

/-- Initialize all actual header fields from the allocation identity and source
capacity. Initial payloads, successful stores and final reads are derived. -/
theorem run_verified (before : State) (id : Nat) (cell : Allocation) (capacity : BitVec 32)
    (positive : 0 < capacity.toNat) (valid : before.valid = true)
    (found : before.heap.lookup id = some cell) (typed : cell.type = storageType capacity.toNat)
    (writable : cell.writable = true) :
    ∃ after, run capacity id before = (.ok (), after) ∧ after.valid = true ∧
      before.heap.RetainsShape after.heap ∧
      (∀ slot : Slot, load after (slot.pointer capacity id) = .ok (slot.value capacity id)) ∧
      (∀ other, other ≠ id → after.heap.lookup other = before.heap.lookup other) ∧
      after.nextId = before.nextId ∧ after.nextAddress = before.nextAddress := by
  obtain ⟨values, first⟩ := store_total before id cell capacity .values positive valid found typed writable
  have valuesValid := store_preserves_valid _ _ _ _ valid first
  have valuesShape := store_retains_shape _ _ _ _ first
  obtain ⟨valueCell, valueFound, valueShape⟩ := valuesShape id cell found
  obtain ⟨keys, second⟩ := store_total values id valueCell capacity .keys positive valuesValid valueFound
    (valueShape.2.1.trans typed) (valueShape.2.2.1.trans writable)
  have keysValid := store_preserves_valid _ _ _ _ valuesValid second
  have keysShape := store_retains_shape _ _ _ _ second
  obtain ⟨keyCell, keyFound, keyShape⟩ := keysShape id valueCell valueFound
  obtain ⟨after, third⟩ := store_total keys id keyCell capacity .capacity positive keysValid keyFound
    (keyShape.2.1.trans (valueShape.2.1.trans typed)) (keyShape.2.2.1.trans (valueShape.2.2.1.trans writable))
  refine ⟨after, run_steps capacity id before values keys after
    (checked_value before id cell capacity .values positive valid found typed writable)
    (checked_value values id valueCell capacity .keys positive valuesValid valueFound
      (valueShape.2.1.trans typed) (valueShape.2.2.1.trans writable)) rfl first second third,
    store_preserves_valid _ _ _ _ keysValid third,
    valuesShape.trans (keysShape.trans (store_retains_shape _ _ _ _ third)), ?_, ?_, ?_, ?_⟩
  · intro slot
    cases slot with
    | values =>
      rw [read_other keys after capacity id .capacity .values third (by decide),
        read_other values keys capacity id .keys .values second (by decide)]
      exact load_after_store _ _ _ _ first
    | keys =>
      rw [read_other keys after capacity id .capacity .keys third (by decide)]
      exact load_after_store _ _ _ _ second
    | capacity => exact load_after_store _ _ _ _ third
  · intro other apart
    exact (heap_after_store_other _ true false _ ⟨id, Slot.capacity.offset⟩ _ _ third other apart).trans
      ((heap_after_store_other _ true false _ ⟨id, Slot.keys.offset⟩ _ _ second other apart).trans
        (heap_after_store_other _ true false _ ⟨id, Slot.values.offset⟩ _ _ first other apart))
  · exact (store_keeps_counters _ _ _ _ third).1.trans
      ((store_keeps_counters _ _ _ _ second).1.trans (store_keeps_counters _ _ _ _ first).1)
  · exact (store_keeps_counters _ _ _ _ third).2.trans
      ((store_keeps_counters _ _ _ _ second).2.trans (store_keeps_counters _ _ _ _ first).2)

end Header
end Compiler.Extraction.ExpressionMap.Buckets
