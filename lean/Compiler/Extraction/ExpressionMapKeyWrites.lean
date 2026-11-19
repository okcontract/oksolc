/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapKey

namespace Compiler.Extraction.ExpressionMap.Buckets.KeyFields
open Compiler.ZigAir.Memory
open Compiler.Extraction.Cache (Key)

/-- Interpreted member stores of the source key assignment. The evaluated key
is retained across writes; rejected writes preserve the exact completed prefix. -/
def writes (source : Value) (key : Key) (arguments : Address) : List Slot → State → Except Fault Unit × State
  | [], state => (.ok (), state)
  | slot :: rest, state => match writeAt source key arguments slot state with
    | .error fault => (.error fault, state)
    | .ok after => writes source key arguments rest after

def order : List Slot := [.kind, .instruction, .data, .arguments, .sequence]

def assign (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address) (before : State) :
    Except Fault Unit × State :=
  match entryPointer before capacity bucket index with
  | .error fault => (.error fault, before)
  | .ok source => writes source key arguments order before

/-- Read offsets outside the selected key survive, including rejected reads. -/
def Outside (capacity index : Nat) (child : Ty) (queried : Nat) : Prop :=
  ∀ position ∈ child.readOffsets queried,
    position < keysOffset capacity + index * 64 ∨ keysOffset capacity + index * 64 + 64 ≤ position

theorem store_frame (before after : State) (capacity bucket index : Nat) (key : Key) (arguments : Address) (slot : Slot)
    (stored : store before (field capacity bucket index key arguments slot) (value key arguments slot) = .ok after)
    (writable many : Bool) (child : Ty) (queried : Nat) (outside : Outside capacity index child queried) :
    load after (.pointer (.pointer writable many child) ⟨bucket, queried⟩) =
      load before (.pointer (.pointer writable many child) ⟨bucket, queried⟩) := by
  apply load_disjoint_after_store before true false _ _ _ after writable many child queried stored
  intro position member entry written
  have apart := outside position member
  have footprint : keysOffset capacity + index * 64 ≤ entry.1 ∧ entry.1 < keysOffset capacity + index * 64 + 64 := by
    cases slot <;> simp_all [value, Value.leaves, address, offset]
    rcases written with rfl | rfl <;> omega
  omega

structure Written (capacity bucket index : Nat) (key : Key) (arguments : Address)
    (slots : List Slot) (before after : State) : Prop where
  valid : after.valid = true
  shape : before.heap.RetainsShape after.heap
  frame : ∀ other, other ≠ bucket → after.heap.lookup other = before.heap.lookup other
  nextId : after.nextId = before.nextId
  nextAddress : after.nextAddress = before.nextAddress
  reads : ∀ slot, load after (field capacity bucket index key arguments slot) =
    if slot ∈ slots then .ok (value key arguments slot) else load before (field capacity bucket index key arguments slot)
  outside : ∀ writable many child queried, Outside capacity index child queried →
    load after (.pointer (.pointer writable many child) ⟨bucket, queried⟩) =
      load before (.pointer (.pointer writable many child) ⟨bucket, queried⟩)

theorem writes_verified (capacity bucket index : Nat) (key : Key) (arguments : Address) (slots : List Slot)
    (before : State) (cell : Allocation) (bounded : capacity < 2 ^ 32) (inside : index < capacity)
    (valid : before.valid = true) (found : before.heap.lookup bucket = some cell)
    (typed : cell.type = storageType capacity) (writable : cell.writable = true)
    (length : key.arguments.length < addressLimit) :
    ∃ after, writes (.pointer (.pointer true false keyType) (address capacity bucket index)) key arguments slots before = (.ok (), after) ∧
      Written capacity bucket index key arguments slots before after := by
  induction slots generalizing before cell with
  | nil => exact ⟨before, rfl, valid, Heap.RetainsShape.refl _, fun _ _ => rfl, rfl, rfl,
      by intro slot; simp, fun _ _ _ _ _ => rfl⟩
  | cons slot rest ih =>
    obtain ⟨middle, ran, stored⟩ := write_total before capacity bucket index cell key arguments bounded inside valid found typed writable length slot
    have shape := store_retains_shape _ _ _ _ stored
    have middleValid := store_preserves_valid _ _ _ _ valid stored
    obtain ⟨middleCell, middleFound, middleShape⟩ := shape bucket cell found
    obtain ⟨after, completed, post⟩ := ih middle middleCell middleValid middleFound
      (middleShape.2.1.trans typed) (middleShape.2.2.1.trans writable)
    refine ⟨after, ?_, post.valid, shape.trans post.shape, ?_,
      post.nextId.trans (store_keeps_counters _ _ _ _ stored).1,
      post.nextAddress.trans (store_keeps_counters _ _ _ _ stored).2, ?_, ?_⟩
    · have step : writeAt (.pointer (.pointer true false keyType) (address capacity bucket index))
          key arguments slot before = .ok middle := ran
      simp only [writes, step]
      exact completed
    · intro other apart
      exact (post.frame other apart).trans (heap_after_store_other _ true false _ _ _ _ stored other apart)
    · intro read
      rw [post.reads]
      by_cases later : read ∈ rest
      · simp only [later, List.mem_cons, or_true, ↓reduceIte]
      · simp only [later, List.mem_cons, or_false, ↓reduceIte]
        by_cases same : read = slot
        · subst read; simp only [↓reduceIte]; exact load_after_store _ _ _ _ stored
        · simp only [same, ↓reduceIte]; exact read_other _ _ capacity bucket index key arguments slot read stored same
    · intro readWritable many child queried outside
      exact (post.outside readWritable many child queried outside).trans
        (store_frame _ _ capacity bucket index key arguments slot stored readWritable many child queried outside)

theorem Written.header (post : Written capacity bucket index key arguments slots before after)
    (bounded : capacity < 2 ^ 32) (word : BitVec 32) (slot : Header.Slot) :
    load after (slot.pointer word bucket) = load before (slot.pointer word bucket) := by
  apply post.outside true false (slot.value word bucket).type slot.offset
  have geometry := Buckets.geometry capacity bounded
  cases slot <;> simp [Outside, Header.Slot.value, Header.Slot.offset, Value.type,
    Compiler.ZigAir.Scalar.Value.type, Ty.readOffsets] <;> omega

/-- Follow the same native header and field selection when observing the
stored key. Reading a key does not dereference its borrowed argument slice. -/
def read (capacity : BitVec 32) (bucket index : Nat) (slot : Slot) (state : State) : Except Fault Value := do
  let source ← entryPointer state capacity bucket index
  let target ← fieldPointer state source (offset slot)
  load state target

theorem read_eq (capacity : BitVec 32) (bucket index : Nat) (slot : Slot) (state : State)
    (cell : Allocation) (key : Key) (arguments : Address) (inside : index < capacity.toNat)
    (valid : state.valid = true) (found : state.heap.lookup bucket = some cell) (typed : cell.type = storageType capacity.toNat)
    (header : load state (Header.Slot.keys.pointer capacity bucket) = .ok (Header.Slot.keys.value capacity bucket)) :
    read capacity bucket index slot state = load state (field capacity.toNat bucket index key arguments slot) := by
  have selected := select_verified state capacity.toNat bucket index cell key arguments
    capacity.isLt inside valid found typed slot
  simp only [read, entry_pointer state capacity bucket index cell inside valid found typed header, bind, Except.bind]
  change (do let target ← select state capacity.toNat bucket index slot; load state target) = _
  simp only [selected, bind, Except.bind]

theorem Written.read (post : Written capacity.toNat bucket index key arguments order before after)
    (cell : Allocation) (inside : index < capacity.toNat) (found : before.heap.lookup bucket = some cell)
    (typed : cell.type = storageType capacity.toNat)
    (header : load before (Header.Slot.keys.pointer capacity bucket) = .ok (Header.Slot.keys.value capacity bucket)) (slot : Slot) :
    read capacity bucket index slot after = .ok (value key arguments slot) := by
  obtain ⟨afterCell, afterFound, shape⟩ := post.shape bucket cell found
  rw [read_eq capacity bucket index slot after afterCell key arguments inside post.valid afterFound
    (shape.2.1.trans typed) ((post.header capacity.isLt capacity .keys).trans header)]
  have loaded := post.reads slot
  have member : slot ∈ order := by cases slot <;> simp [order]
  simp only [member, ↓reduceIte] at loaded
  exact loaded

theorem assign_verified (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address)
    (before : State) (cell : Allocation) (inside : index < capacity.toNat)
    (valid : before.valid = true) (found : before.heap.lookup bucket = some cell)
    (typed : cell.type = storageType capacity.toNat) (writable : cell.writable = true)
    (length : key.arguments.length < addressLimit)
    (header : load before (Header.Slot.keys.pointer capacity bucket) = .ok (Header.Slot.keys.value capacity bucket)) :
    ∃ after, assign capacity bucket index key arguments before = (.ok (), after) ∧
      Written capacity.toNat bucket index key arguments order before after ∧
      ∀ slot, load after (field capacity.toNat bucket index key arguments slot) = .ok (value key arguments slot) := by
  obtain ⟨after, ran, post⟩ := writes_verified capacity.toNat bucket index key arguments order before cell
    capacity.isLt inside valid found typed writable length
  refine ⟨after, ?_, post, ?_⟩
  · simp only [assign, entry_pointer before capacity bucket index cell inside valid found typed header, ran]
  · intro slot
    rw [post.reads]
    have member : slot ∈ order := by cases slot <;> simp [order]
    simp only [member, ↓reduceIte]

theorem assign_rejected (capacity : BitVec 32) (bucket index : Nat) (key : Key) (arguments : Address)
    (before : State) (fault : Fault) (rejected : entryPointer before capacity bucket index = .error fault) :
    assign capacity bucket index key arguments before = (.error fault, before) := by simp only [assign, rejected]

end Compiler.Extraction.ExpressionMap.Buckets.KeyFields
