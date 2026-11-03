/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapCapacityMemory

namespace Compiler.Extraction.ExpressionMap.Counter
open Compiler.ZigAir.Memory Initialization RepresentativeArray
open Compiler.ZigAir.Memory.WordArray (word number)

inductive Field where
  | available | size
  deriving DecidableEq, Repr

def Field.slot : Field → Slot
  | .available => .available | .size => .size

def Field.next : Field → BitVec 32 → BitVec 32
  | .available, value => value - 1#32 | .size, value => value + 1#32

def Field.Admitted : Field → BitVec 32 → Prop
  | .available, value => 0 < value.toNat | .size, value => value.toNat + 1 < 2 ^ 32

def field (place : Placement) (safety : Bool) (receiver : Nat) (slot : Slot) : Value :=
  .pointer (.pointer true false slot.value.type) ⟨receiver, place.offset safety + slot.offset safety⟩

def pointer (place : Placement) (safety : Bool) (state : State) (receiver : Nat) (slot : Slot) : Except Fault Value :=
  match place with
  | .embedded => Initialization.pointer safety state ⟨receiver, 0⟩ true slot
  | .localMap => fieldPointer state (.pointer (.pointer true false (allocationType safety)) ⟨receiver, 0⟩) (slot.offset safety)

def write (place : Placement) (safety : Bool) (state : State) (receiver : Nat) (slot : Slot) (value : Value) : Except Fault State := do
  let target ← pointer place safety state receiver slot
  store state target value

theorem pointer_eq (place : Placement) (safety : Bool) (state : State) (receiver : Nat) (slot : Slot) (cell : Allocation)
    (valid : state.valid = true) (found : state.heap.lookup receiver = some cell)
    (typed : cell.type = place.type safety) (ordinary : slot ≠ .lock) :
    pointer place safety state receiver slot = .ok (field place safety receiver slot) := by
  cases place with
  | embedded =>
    exact Initialization.root_pointer safety state receiver cell true slot
      (by cases slot <;> simp_all [Slot.Active]) valid found typed
  | localMap =>
    simpa only [pointer, field, Placement.offset, Nat.zero_add] using root_fieldPointer state receiver cell (allocationType safety) slot.value.type
      (Placement.localMap.layout safety) (slot.offset safety) true false valid found typed
      (Placement.localMap.layout_checked safety) (by cases slot <;> cases safety <;> simp_all <;> decide)
      (by cases slot <;> cases safety <;> simp_all <;> rfl)

theorem read_eq (place : Placement) (safety : Bool) (state : State) (receiver : Nat) (slot : Slot) (cell : Allocation)
    (valid : state.valid = true) (found : state.heap.lookup receiver = some cell)
    (typed : cell.type = place.type safety) (ordinary : slot ≠ .lock) :
    Capacity.readField place safety state receiver slot = load state (field place safety receiver slot) := by
  cases place with
  | embedded =>
    simp only [Capacity.readField, Initialization.read, Initialization.root_pointer safety state receiver cell false slot
      (by cases slot <;> simp_all [Slot.Active]) valid found typed, bind, Except.bind]
    rfl
  | localMap =>
    simpa only [field, Placement.offset, Nat.zero_add, Local.field] using
      Capacity.local_read safety state receiver slot cell valid found typed ordinary

structure Stored (place : Placement) (safety : Bool) (receiver : Nat) (slot : Slot) (value : Value)
    (before after : State) : Prop where
  valid : before.valid = true
  typed : value.type = slot.value.type
  store : Compiler.ZigAir.Memory.store before (field place safety receiver slot) value = .ok after

variable {place : Placement} {safety : Bool} {receiver : Nat} {slot : Slot} {value : Value} {before after : State}

theorem Stored.native_frame (post : Stored place safety receiver slot value before after) :
    after.valid = true ∧ before.heap.RetainsShape after.heap ∧
      (∀ other, other ≠ receiver → after.heap.lookup other = before.heap.lookup other) ∧
      after.nextId = before.nextId ∧ after.nextAddress = before.nextAddress :=
  ⟨store_preserves_valid _ _ _ _ post.valid post.store, store_retains_shape _ _ _ _ post.store,
    heap_after_store_other _ true false slot.value.type _ _ _ post.store,
    (store_keeps_counters _ _ _ _ post.store).1, (store_keeps_counters _ _ _ _ post.store).2⟩

theorem Stored.read (post : Stored place safety receiver slot value before after) :
    load after (field place safety receiver slot) = .ok value := load_after_store _ _ _ _ post.store

theorem Stored.others (post : Stored place safety receiver slot value before after) (other : Slot) (apart : other ≠ slot) :
    load after (field place safety receiver other) = load before (field place safety receiver other) :=
  load_frame_at place safety before after receiver value slot other post.typed apart true post.store

theorem Stored.header (post : Stored .embedded safety receiver slot value before after) (cell : Allocation)
    (found : before.heap.lookup receiver = some cell) (typed : cell.type = Owner.viewType safety) :
    RepresentativeArray.readHeader after (Owner.headerAddress ⟨receiver, 0⟩) =
      RepresentativeArray.readHeader before (Owner.headerAddress ⟨receiver, 0⟩) := by
  apply header_frame_of_store safety before after receiver cell value (Owner.expressionsOffset safety + slot.offset safety)
    post.valid found typed (by simpa only [post.typed] using post.store)
  all_goals rw [slot.leaves value _ post.typed]; simp only [List.mem_singleton, forall_eq]
  all_goals cases slot <;> cases safety <;> decide

/-- Both compound assignments read their actual field before checked u32
arithmetic. Overflow/underflow rejects at the reached state, never as OOM. -/
def adjust (place : Placement) (safety : Bool) (receiver : Nat) (which : Field) (before : State) : Except Fault Unit × State :=
  match Capacity.readField place safety before receiver which.slot with
  | .error fault => (.error fault, before)
  | .ok (.scalar (.int false 32 bits)) =>
    let old := BitVec.ofInt 32 bits
    if !(match which with | .available => 0 < old.toNat | .size => old.toNat + 1 < 2 ^ 32) then
      (.error (Capacity.rejected safety), before)
    else match write place safety before receiver which.slot (number (which.next old)) with
      | .error fault => (.error fault, before)
      | .ok after => (.ok (), after)
  | .ok _ => (.error .unsupported, before)

theorem adjust_steps (place : Placement) (safety : Bool) (receiver : Nat) (which : Field) (old : BitVec 32)
    (before after : State)
    (read : Capacity.readField place safety before receiver which.slot = .ok (number old))
    (admitted : which.Admitted old)
    (written : write place safety before receiver which.slot (number (which.next old)) = .ok after) :
    adjust place safety receiver which before = (.ok (), after) := by
  cases which <;> simp_all [adjust, Field.Admitted, number]

theorem adjust_verified (place : Placement) (safety : Bool) (receiver : Nat) (which : Field) (old : BitVec 32)
    (before : State) (cell : Allocation) (valid : before.valid = true)
    (found : before.heap.lookup receiver = some cell) (typed : cell.type = place.type safety) (writable : cell.writable = true)
    (read : load before (field place safety receiver which.slot) = .ok (number old)) (admitted : which.Admitted old) :
    ∃ after, adjust place safety receiver which before = (.ok (), after) ∧
      Stored place safety receiver which.slot (number (which.next old)) before after := by
  have ordinary : which.slot ≠ .lock := by cases which <;> decide
  have valueType : (number (which.next old)).type = which.slot.value.type := by cases which <;> rfl
  obtain ⟨after, stored⟩ := store_value_at_total place safety before receiver cell which.slot (number (which.next old))
    valueType (WordArray.number_valid _) (by cases which <;> simp [Field.slot, Slot.Active]) valid found typed writable
  have selected := pointer_eq place safety before receiver which.slot cell valid found typed ordinary
  have loaded := (read_eq place safety before receiver which.slot cell valid found typed ordinary).trans read
  have written : write place safety before receiver which.slot (number (which.next old)) = .ok after := by
    simp only [write, selected, bind, Except.bind]
    exact stored
  exact ⟨after, adjust_steps place safety receiver which old before after loaded admitted written, valid, valueType, stored⟩

theorem adjust_rejected (place : Placement) (safety : Bool) (receiver : Nat) (which : Field) (old : BitVec 32)
    (before : State) (read : Capacity.readField place safety before receiver which.slot = .ok (number old))
    (blocked : ¬which.Admitted old) :
    adjust place safety receiver which before = (.error (Capacity.rejected safety), before) := by
  cases which <;> simp_all [adjust, Field.Admitted, number]

theorem next_exact (which : Field) (old : BitVec 32) (admitted : which.Admitted old) :
    match which with
    | .available => (which.next old).toNat + 1 = old.toNat
    | .size => (which.next old).toNat = old.toNat + 1 := by
  have bounded := old.isLt
  cases which <;> simp only [Field.Admitted] at admitted
  · simp only [Field.next, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · simp only [Field.next, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

end Compiler.Extraction.ExpressionMap.Counter
