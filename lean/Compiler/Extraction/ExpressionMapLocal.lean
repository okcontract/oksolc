/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapAllocation

namespace Compiler.Extraction.ExpressionMap.Local
open Compiler.ZigAir.Memory Initialization

/-- The source `.{}' defaults, including SafetyLock's stored counter only in
safety modes. All stores use the same typed field-store proof as the owner. -/
def slots (safety : Bool) : List Slot :=
  [.metadata, .size, .available] ++ if safety then [.lock] else []

def field (safety : Bool) (id : Nat) (slot : Slot) : Value :=
  .pointer (.pointer true false slot.value.type) ⟨id, slot.offset safety⟩

/-- Every local field store shares validity, shape, cursor and sibling-field
preservation, whether its value is a default or computed by grow. -/
structure Stored (safety : Bool) (id : Nat) (before after : State) (slot : Slot) (value : Value) : Prop where
  valid : after.valid = true
  shape : before.heap.RetainsShape after.heap
  frame : ∀ other, other ≠ id → after.heap.lookup other = before.heap.lookup other
  nextId : after.nextId = before.nextId
  nextAddress : after.nextAddress = before.nextAddress
  read : load after (field safety id slot) = .ok value
  others : ∀ queried, queried ≠ slot → load after (field safety id queried) = load before (field safety id queried)

theorem store_value_verified (safety : Bool) (before : State) (id : Nat) (cell : Allocation)
    (slot : Slot) (value : Value) (valueType : value.type = slot.value.type) (valueValid : value.valid = true)
    (active : slot.Active safety) (valid : before.valid = true) (found : before.heap.lookup id = some cell)
    (typed : cell.type = allocationType safety) (writable : cell.writable = true) :
    ∃ after, store before (field safety id slot) value = .ok after ∧ Stored safety id before after slot value := by
  obtain ⟨after, stored⟩ := store_value_at_total .localMap safety before id cell slot value valueType valueValid
    active valid found typed writable
  have stored : store before (field safety id slot) value = .ok after := by
    simpa only [Placement.offset, Nat.zero_add, field] using stored
  refine ⟨after, stored, store_preserves_valid _ _ _ _ valid stored, store_retains_shape _ _ _ _ stored,
    heap_after_store_other _ true false _ _ _ _ stored,
    (store_keeps_counters _ _ _ _ stored).1, (store_keeps_counters _ _ _ _ stored).2,
    load_alias_after_store before true false _ _ _ after true false stored, ?_⟩
  intro queried different
  simpa only [Placement.offset, Nat.zero_add, field] using
    load_frame_at .localMap safety before after id value slot queried valueType different true
      (by simpa only [Placement.offset, Nat.zero_add, field] using stored)

def writes (safety : Bool) (id : Nat) : List Slot → State → Except Fault Unit × State
  | [], state => (.ok (), state)
  | slot :: rest, state => match store state (field safety id slot) slot.value with
    | .error fault => (.error fault, state)
    | .ok after => writes safety id rest after

structure Written (safety : Bool) (id : Nat) (before after : State) (selected : List Slot) : Prop where
  valid : after.valid = true
  shape : before.heap.RetainsShape after.heap
  frame : ∀ other, other ≠ id → after.heap.lookup other = before.heap.lookup other
  nextId : after.nextId = before.nextId
  nextAddress : after.nextAddress = before.nextAddress
  reads : ∀ slot ∈ selected, load after (field safety id slot) = .ok slot.value
  others : ∀ slot, slot ∉ selected → load after (field safety id slot) = load before (field safety id slot)

theorem read_other (safety : Bool) (id : Nat) (before after : State) (written queried : Slot)
    (different : queried ≠ written)
    (stored : store before (field safety id written) written.value = .ok after) :
    load after (field safety id queried) = load before (field safety id queried) := by
  simpa only [Placement.offset, Nat.zero_add, field] using
    load_frame_at .localMap safety before after id written.value written queried rfl different true
      (by simpa only [Placement.offset, Nat.zero_add, field] using stored)

/-- List induction shares allocation/initialization/frame reasoning across all
fields; it does not assume their contents or a successful sequence of stores. -/
theorem writes_verified (safety : Bool) (id : Nat) (selected : List Slot)
    (active : ∀ slot ∈ selected, slot.Active safety) (before : State) (cell : Allocation)
    (valid : before.valid = true) (found : before.heap.lookup id = some cell)
    (typed : cell.type = allocationType safety) (writable : cell.writable = true) :
    ∃ after, writes safety id selected before = (.ok (), after) ∧ Written safety id before after selected := by
  induction selected generalizing before cell with
  | nil => exact ⟨before, rfl, valid, Heap.RetainsShape.refl _, fun _ _ => rfl, rfl, rfl,
      by simp, fun _ _ => rfl⟩
  | cons slot rest ih =>
    obtain ⟨middle, stored, written⟩ := store_value_verified safety before id cell slot slot.value rfl
      (by cases slot <;> decide) (active slot (by simp)) valid found typed writable
    have middleValid := written.valid
    have shape := written.shape
    obtain ⟨middleCell, middleFound, middleShape⟩ := shape id cell found
    obtain ⟨after, ran, post⟩ := ih (fun s member => active s (List.mem_cons_of_mem slot member)) middle middleCell
      middleValid middleFound (middleShape.2.1.trans typed) (middleShape.2.2.1.trans writable)
    refine ⟨after, ?_, post.valid, shape.trans post.shape, ?_,
      post.nextId.trans written.nextId, post.nextAddress.trans written.nextAddress, ?_, ?_⟩
    · rw [writes.eq_def]; dsimp only; rw [stored]; exact ran
    · intro other apart
      exact (post.frame other apart).trans (written.frame other apart)
    · intro queried member
      by_cases later : queried ∈ rest
      · exact post.reads queried later
      · have same : queried = slot := (List.mem_cons.mp member).resolve_right later
        subst queried
        exact (post.others slot later).trans written.read
    · intro queried absent
      have apart : queried ≠ slot := fun same => absent (same ▸ List.mem_cons_self)
      exact (post.others queried (fun member => absent (List.mem_cons_of_mem slot member))).trans
        (read_other safety id before middle slot queried apart stored)

def stackBase (state : State) : Nat := state.nextAddress + (8 - state.nextAddress % 8) % 8
def stackEnd (safety : Bool) (state : State) : Nat := stackBase state + (Placement.localMap.layout safety).bytes
def Room (safety : Bool) (state : State) : Prop := 0 < stackBase state ∧ stackEnd safety state < addressLimit

/-- The local declaration starts with uninitialized stack storage. Assignment
failure keeps its reached prefix; stack exhaustion leaves the input unchanged.
This is the declaration after grow's capacity guards, not all of grow. -/
def declare (safety : Bool) (before : State) : Except Fault Address × State :=
  match allocate before (allocationType safety) with
  | .error fault => (.error fault, before)
  | .ok (_, allocated) =>
    let (result, after) := writes safety before.nextId (slots safety) allocated
    (result.map (fun _ => ⟨before.nextId, 0⟩), after)

theorem declare_verified (safety : Bool) (before : State) (valid : before.valid = true) (room : Room safety before) :
    ∃ after cell, declare safety before = (.ok ⟨before.nextId, 0⟩, after) ∧
      after.valid = true ∧ before.heap.RetainsShape after.heap ∧
      after.heap.lookup before.nextId = some cell ∧ cell.base = stackBase before ∧ cell.type = allocationType safety ∧
      cell.writable = true ∧ cell.stack = true ∧
      (∀ slot, slot.Active safety → load after (field safety before.nextId slot) = .ok slot.value) ∧
      (∀ other, other ≠ before.nextId → after.heap.lookup other = before.heap.lookup other) ∧
      after.nextId = before.nextId + 1 ∧ after.nextAddress = stackEnd safety before := by
  let fresh : Allocation := ⟨stackBase before, allocationType safety, [], true, true⟩
  let allocated : State := ⟨(before.nextId, fresh) :: before.heap, before.nextId + 1, stackEnd safety before⟩
  have allocation : allocate before (allocationType safety) =
      .ok (.pointer (.pointer true false (allocationType safety)) ⟨before.nextId, 0⟩, allocated) := by
    have shaped := Placement.localMap.layout_checked safety
    change (allocationType safety).layout = some (Placement.localMap.layout safety) at shaped
    simp only [allocate, valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, shaped]
    have admitted : ¬(stackBase before = 0 ∨ stackEnd safety before ≥ addressLimit) := by
      rcases room with ⟨positive, bounded⟩; omega
    cases safety <;> simpa only [Placement.layout, stackBase, stackEnd, fresh, allocated] using
      (if_neg admitted : (if stackBase before = 0 ∨ stackEnd _ before ≥ addressLimit then _ else _) = _)
  have found : allocated.heap.lookup before.nextId = some fresh := by simp [allocated, Heap.lookup_cons]
  have active : ∀ slot ∈ slots safety, slot.Active safety := by
    cases safety <;> intro slot member <;> cases slot <;> simp_all [slots, Slot.Active]
  obtain ⟨after, ran, post⟩ := writes_verified safety before.nextId (slots safety) active allocated fresh
    (allocate_preserves_valid _ _ _ _ allocation) found rfl rfl
  obtain ⟨cell, located, same⟩ := post.shape before.nextId fresh found
  refine ⟨after, cell, ?_, post.valid, (allocate_retains_shape _ _ _ _ valid allocation).trans post.shape,
    located, same.1, same.2.1, same.2.2.1, same.2.2.2, ?_, ?_, post.nextId, post.nextAddress⟩
  · simp only [declare, allocation, ran, Except.map]
  · intro slot permitted
    apply post.reads slot
    cases safety <;> cases slot <;> simp_all [slots, Slot.Active]
  · intro other apart
    exact (post.frame other apart).trans (by simp [allocated, Heap.lookup_cons, Ne.symm apart])

/-- Preserve every admitted allocator region disjoint from the new stack cell,
including holes below the cursor. No monotone host-allocation policy is assumed. -/
theorem declare_region (safety : Bool) (before : State) (valid : before.valid = true) (room : Room safety before)
    (layout : Layout) (base : Nat) (fits : RegionAllocation.Fits before layout base)
    (apart : base + layout.bytes ≤ stackBase before ∨ stackEnd safety before ≤ base) :
    RegionAllocation.Fits (declare safety before).2 layout base := by
  obtain ⟨after, cell, ran, afterValid, _, found, baseEq, typed, _, _, _, frame, _⟩ := declare_verified safety before valid room
  rw [congrArg Prod.snd ran]
  refine ⟨fits.positive, fits.aligned, fits.bounded, ?_⟩
  intro entry member old shaped
  have located := lookup_of_mem_valid after entry.1 entry.2 afterValid member
  by_cases fresh : entry.1 = before.nextId
  · have same : entry.2 = cell := Option.some.inj (located.symm.trans (by rw [fresh]; exact found))
    have nativeShape := Placement.localMap.layout_checked safety
    change (allocationType safety).layout = some (Placement.localMap.layout safety) at nativeShape
    have oldEq : old = Placement.localMap.layout safety := Option.some.inj
      (shaped.symm.trans (by rw [same, typed]; exact nativeShape))
    simpa only [same, baseEq, oldEq, stackEnd] using apart
  · exact fits.separate entry (Heap.lookup_mem _ _ _ ((frame entry.1 fresh).symm.trans located)) old shaped

theorem declare_exhausted (safety : Bool) (before : State) (valid : before.valid = true) (room : ¬Room safety before) :
    declare safety before = (.error .outOfMemory, before) := by
  have shaped := Placement.localMap.layout_checked safety
  have exhausted : stackBase before = 0 ∨ stackEnd safety before ≥ addressLimit := by
    unfold Room at room; omega
  unfold declare
  simp only [allocate, valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Placement.type] at shaped ⊢
  rw [shaped]
  cases safety <;> simp_all [stackBase, stackEnd, Placement.layout]

end Compiler.Extraction.ExpressionMap.Local
