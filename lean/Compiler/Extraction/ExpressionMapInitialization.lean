/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapEmpty

namespace Compiler.Extraction.ExpressionMap.Initialization
open Compiler.ZigAir.Memory RepresentativeArray

/-- The complete source default assignment, including the default lock. The
zero-byte ReleaseFast lock has no storage operation. -/
inductive Slot where
  | metadata | size | available | lock
  deriving DecidableEq, Repr

def Slot.offset (slot : Slot) (runtimeSafety : Bool) : Nat := match slot with
  | .metadata => metadataOffset
  | .size => (sizeOffset runtimeSafety)
  | .available => (availableOffset runtimeSafety)
  | .lock => (lockOffset runtimeSafety)

def Slot.value : Slot → Value
  | .metadata => .optionalObject metadataPointerType ⟨8, 8⟩ none
  | .size | .available => .scalar (.int false 32 0)
  | .lock => .scalar (.int false 64 0)

def Slot.region : Slot → Layout
  | .metadata => ⟨8, 8⟩
  | .size | .available => ⟨4, 4⟩
  | .lock => ⟨8, 8⟩

def Slot.Active (slot : Slot) (runtimeSafety : Bool) : Prop :=
  slot = .lock → runtimeSafety = true

/-- Map fields are atomic typed leaves, including nonnull metadata. Validity
of the value is checked separately before a write can be admitted. -/
theorem Slot.leaves (slot : Slot) (value : Value) (offset : Nat)
    (typed : value.type = slot.value.type) :
    value.leaves offset = [(offset, value)] := by
  cases value <;> try rfl
  case slice type address length =>
    cases slot <;> simp only [Value.type, Slot.value, Compiler.ZigAir.Scalar.Value.type] at typed
    all_goals subst type; rfl

def pointer (runtimeSafety : Bool) (state : State) (owner : Address) (writable : Bool) (slot : Slot) : Except Fault Value := do
  let field ← cacheFieldPointer runtimeSafety state owner writable (slot.offset runtimeSafety)
  match slot with
  | .lock => fieldPointer state field 0
  | _ => .ok field

def read (runtimeSafety : Bool) (state : State) (owner : Address) (slot : Slot) : Except Fault Value := do
  let field ← pointer runtimeSafety state owner false slot
  load state field

def write (runtimeSafety : Bool) (state : State) (owner : Address) (slot : Slot) : Except Fault State := do
  let field ← pointer runtimeSafety state owner true slot
  store state field slot.value

/-- Store a native map field's evaluated value through the same captured owner
selector used by initialization. This does not model bucket allocation/probing. -/
def writeValue (runtimeSafety : Bool) (state : State) (owner : Address) (slot : Slot)
    (value : Value) : Except Fault State := do
  let field ← pointer runtimeSafety state owner true slot
  store state field value

theorem write_default (runtimeSafety : Bool) (state : State) (owner : Address) (slot : Slot) :
    write runtimeSafety state owner slot = writeValue runtimeSafety state owner slot slot.value := rfl

theorem root_pointer (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (writable : Bool) (slot : Slot) (active : slot.Active runtimeSafety)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) :
    pointer runtimeSafety state ⟨lifetime, 0⟩ writable slot =
      .ok (.pointer (.pointer writable false slot.value.type) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (slot.offset runtimeSafety)⟩) := by
  cases slot with
  | metadata =>
    have selected := root_field_pointer runtimeSafety state lifetime cell writable metadataOffset metadataType initial found typed
      (by cases runtimeSafety <;> rfl)
    simp only [pointer, Slot.offset, selected, bind, Except.bind]
    rfl
  | size =>
    have selected := root_field_pointer runtimeSafety state lifetime cell writable (sizeOffset runtimeSafety) countType initial found typed
      (by cases runtimeSafety <;> rfl)
    simp only [pointer, Slot.offset, selected, bind, Except.bind]
    rfl
  | available =>
    have selected := root_field_pointer runtimeSafety state lifetime cell writable (availableOffset runtimeSafety) countType initial found typed
      (by cases runtimeSafety <;> rfl)
    simp only [pointer, Slot.offset, selected, bind, Except.bind]
    rfl
  | lock =>
    have safety := active rfl
    subst runtimeSafety
    have selected := root_field_pointer true state lifetime cell writable (lockOffset true) lockType initial found typed (by rfl)
    have parent := root_access state lifetime cell (Owner.layout true) false initial found
      (typed ▸ Owner.view_layout_checked true) (by decide) (by simp)
    have accessed := access_subregion state ⟨lifetime, 0⟩ (Owner.layout true) ⟨8, 8⟩
      ((Owner.expressionsOffset true) + (lockOffset true)) false cell parent (by decide) (by decide) (by decide) (by decide)
    have selectedState := fieldPointer_of_access state ⟨lifetime, (Owner.expressionsOffset true) + (lockOffset true)⟩ cell lockType
      (.scalar (.int false 64)) ⟨8, 8⟩ 0 writable false rfl accessed
      (by rw [typed]; rfl) (by rfl)
    simpa only [pointer, Slot.offset, selected, bind, Except.bind, Nat.add_zero] using selectedState

/-- The same captured map can be embedded in the compiler owner or be grow's
standalone local receiver. Placement changes geometry, not field semantics. -/
inductive Placement where
  | embedded | localMap
  deriving DecidableEq, Repr

def Placement.type (place : Placement) (runtimeSafety : Bool) : Ty := match place with
  | .embedded => Owner.viewType runtimeSafety
  | .localMap => allocationType runtimeSafety

def Placement.layout (place : Placement) (runtimeSafety : Bool) : Layout := match place with
  | .embedded => Owner.layout runtimeSafety
  | .localMap => ⟨if runtimeSafety then 24 else 16, 8⟩

def Placement.offset (place : Placement) (runtimeSafety : Bool) : Nat := match place with
  | .embedded => Owner.expressionsOffset runtimeSafety
  | .localMap => 0

theorem Placement.layout_checked (place : Placement) (runtimeSafety : Bool) :
    (place.type runtimeSafety).layout = some (place.layout runtimeSafety) := by
  cases place with
  | embedded => exact Owner.view_layout_checked runtimeSafety
  | localMap => cases runtimeSafety <;> rfl

theorem slot_views_at (place : Placement) (runtimeSafety : Bool) (slot : Slot) (active : slot.Active runtimeSafety) :
    acceptsView (place.type runtimeSafety) (place.offset runtimeSafety + slot.offset runtimeSafety) slot.value.type = true ∧
      leafType (place.type runtimeSafety) (place.offset runtimeSafety + slot.offset runtimeSafety) = some slot.value.type := by
  cases place <;> cases slot <;> cases runtimeSafety <;>
    simp_all only [Slot.Active, reduceCtorEq, false_implies, true_implies, Bool.false_eq_true]
  all_goals constructor <;> decide +kernel

theorem slot_views (runtimeSafety : Bool) (slot : Slot) (active : slot.Active runtimeSafety) :
    acceptsView (Owner.viewType runtimeSafety) ((Owner.expressionsOffset runtimeSafety) + (slot.offset runtimeSafety)) slot.value.type = true ∧
      leafType (Owner.viewType runtimeSafety) ((Owner.expressionsOffset runtimeSafety) + (slot.offset runtimeSafety)) = some slot.value.type :=
  slot_views_at .embedded runtimeSafety slot active

theorem store_value_at_total (place : Placement) (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (slot : Slot)
    (value : Value) (valueType : value.type = slot.value.type) (valueValid : value.valid = true)
    (active : slot.Active runtimeSafety) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = place.type runtimeSafety)
    (writable : cell.writable = true) :
    ∃ after, store state (.pointer (.pointer true false slot.value.type) ⟨lifetime, (place.offset runtimeSafety) + (slot.offset runtimeSafety)⟩)
      value = .ok after := by
  have parent := root_access state lifetime cell (place.layout runtimeSafety) true initial found
    (typed ▸ place.layout_checked runtimeSafety) (by cases place <;> cases runtimeSafety <;> decide) (by intro _; exact writable)
  have bounded : (place.offset runtimeSafety) + (slot.offset runtimeSafety) + slot.region.bytes ≤ (place.layout runtimeSafety).bytes := by
    cases place <;> cases slot <;> cases runtimeSafety <;> simp_all [Slot.Active, Slot.offset, Slot.region, Owner.layout,
      Owner.expressionsOffset, Placement.layout, Placement.offset, metadataOffset, sizeOffset, availableOffset, lockOffset]
  have accessed := access_subregion state ⟨lifetime, 0⟩ (place.layout runtimeSafety) slot.region
    ((place.offset runtimeSafety) + (slot.offset runtimeSafety)) true cell parent (by cases place <;> cases slot <;> cases runtimeSafety <;> decide) bounded
    (by cases place <;> cases slot <;> cases runtimeSafety <;> decide) (by cases place <;> cases slot <;> cases runtimeSafety <;> decide)
  rw [← valueType]
  apply store_subobject_total state ⟨lifetime, (place.offset runtimeSafety) + (slot.offset runtimeSafety)⟩ slot.region cell value
    valueValid (by rw [valueType]; cases slot <;> rfl) (by simpa only [Nat.zero_add] using accessed)
  · rw [valueType]; exact typed.symm ▸ (slot_views_at place runtimeSafety slot active).1
  · intro entry member
    rw [slot.leaves value 0 valueType, List.mem_singleton] at member
    subst entry
    simpa only [Nat.add_zero, valueType] using typed.symm ▸ (slot_views_at place runtimeSafety slot active).2

theorem store_value_total (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (slot : Slot)
    (value : Value) (valueType : value.type = slot.value.type) (valueValid : value.valid = true)
    (active : slot.Active runtimeSafety) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (writable : cell.writable = true) :
    ∃ after, store state (.pointer (.pointer true false slot.value.type) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (slot.offset runtimeSafety)⟩)
      value = .ok after :=
  store_value_at_total .embedded runtimeSafety state lifetime cell slot value valueType valueValid active initial found typed writable

theorem store_total (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (slot : Slot)
    (active : slot.Active runtimeSafety) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (writable : cell.writable = true) :
    ∃ after, store state (.pointer (.pointer true false slot.value.type) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (slot.offset runtimeSafety)⟩)
      slot.value = .ok after :=
  store_value_total runtimeSafety state lifetime cell slot slot.value rfl (by cases slot <;> decide)
    active initial found typed writable

theorem read_after_store_value (runtimeSafety : Bool) (state after : State) (lifetime : Nat) (cell : Allocation)
    (slot : Slot) (value : Value) (active : slot.Active runtimeSafety) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (stored : store state (.pointer (.pointer true false slot.value.type) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (slot.offset runtimeSafety)⟩)
      value = .ok after) : read runtimeSafety after ⟨lifetime, 0⟩ slot = .ok value := by
  obtain ⟨finalCell, finalFound, shape⟩ := store_retains_shape _ _ _ _ stored lifetime cell found
  have valid := store_preserves_valid _ _ _ _ initial stored
  simp only [read, root_pointer runtimeSafety after lifetime finalCell false slot active valid finalFound (shape.2.1.trans typed),
    bind, Except.bind]
  exact load_alias_after_store state true false slot.value.type _ _ after false false stored

theorem read_after_store (runtimeSafety : Bool) (state after : State) (lifetime : Nat) (cell : Allocation)
    (slot : Slot) (active : slot.Active runtimeSafety) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (stored : store state (.pointer (.pointer true false slot.value.type) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (slot.offset runtimeSafety)⟩)
      slot.value = .ok after) : read runtimeSafety after ⟨lifetime, 0⟩ slot = .ok slot.value :=
  read_after_store_value runtimeSafety state after lifetime cell slot slot.value active initial found typed stored

/-- A field store preserves the other leaves in either placement, for every
value of the written field's type. Publication and initialization share this
frame; it does not depend on the new value being a default. -/
theorem load_frame_at (place : Placement) (runtimeSafety : Bool) (state after : State) (lifetime : Nat)
    (value : Value) (written queried : Slot) (valueType : value.type = written.value.type)
    (different : queried ≠ written) (readWritable : Bool)
    (stored : store state (.pointer (.pointer true false written.value.type)
      ⟨lifetime, place.offset runtimeSafety + written.offset runtimeSafety⟩) value = .ok after) :
    load after (.pointer (.pointer readWritable false queried.value.type)
      ⟨lifetime, place.offset runtimeSafety + queried.offset runtimeSafety⟩) =
    load state (.pointer (.pointer readWritable false queried.value.type)
      ⟨lifetime, place.offset runtimeSafety + queried.offset runtimeSafety⟩) := by
  apply load_disjoint_after_store state true false written.value.type _ _ after readWritable false queried.value.type
    (place.offset runtimeSafety + queried.offset runtimeSafety) stored
  rw [written.leaves value _ valueType]
  cases place <;> cases queried <;> cases written <;> cases runtimeSafety <;>
    simp_all [Placement.offset, Slot.offset, Slot.value, Ty.readOffsets, Value.type,
      Compiler.ZigAir.Scalar.Value.type, Owner.expressionsOffset, metadataOffset, sizeOffset, availableOffset, lockOffset]

theorem read_frame_value (runtimeSafety : Bool) (state after : State) (lifetime : Nat) (cell : Allocation)
    (value : Value) (written queried : Slot) (valueType : value.type = written.value.type)
    (active : queried.Active runtimeSafety) (different : queried ≠ written)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (stored : store state (.pointer (.pointer true false written.value.type) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (written.offset runtimeSafety)⟩)
      value = .ok after) : read runtimeSafety after ⟨lifetime, 0⟩ queried = read runtimeSafety state ⟨lifetime, 0⟩ queried := by
  obtain ⟨finalCell, finalFound, shape⟩ := store_retains_shape _ _ _ _ stored lifetime cell found
  have valid := store_preserves_valid _ _ _ _ initial stored
  simp only [read, root_pointer runtimeSafety after lifetime finalCell false queried active valid finalFound (shape.2.1.trans typed),
    root_pointer runtimeSafety state lifetime cell false queried active initial found typed, bind, Except.bind]
  exact load_frame_at .embedded runtimeSafety state after lifetime value written queried valueType different false stored

theorem read_frame (runtimeSafety : Bool) (state after : State) (lifetime : Nat) (cell : Allocation)
    (written queried : Slot) (active : queried.Active runtimeSafety) (different : queried ≠ written)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (stored : store state (.pointer (.pointer true false written.value.type) ⟨lifetime, (Owner.expressionsOffset runtimeSafety) + (written.offset runtimeSafety)⟩)
      written.value = .ok after) : read runtimeSafety after ⟨lifetime, 0⟩ queried = read runtimeSafety state ⟨lifetime, 0⟩ queried :=
  read_frame_value runtimeSafety state after lifetime cell written.value written queried rfl active different initial found typed stored

theorem size_write (runtimeSafety : Bool) (state : State) (owner : Address) :
    write runtimeSafety state owner .size = initializeSize runtimeSafety state owner := by
  unfold write pointer initializeSize sizePointer
  simp only [Slot.offset]
  cases cacheFieldPointer runtimeSafety state owner true (sizeOffset runtimeSafety) <;> rfl

theorem size_read (runtimeSafety : Bool) (state : State) (owner : Address) :
    read runtimeSafety state owner .size = readSize runtimeSafety state owner := by
  unfold read pointer readSize sizePointer
  simp only [Slot.offset]
  cases cacheFieldPointer runtimeSafety state owner false (sizeOffset runtimeSafety) <;> rfl

structure Frame (runtimeSafety : Bool) (before after : State) (lifetime : Nat) : Prop where
  valid : after.valid = true
  shape : before.heap.RetainsShape after.heap
  header : RepresentativeArray.readHeader after (Owner.headerAddress ⟨lifetime, 0⟩) =
    RepresentativeArray.readHeader before (Owner.headerAddress ⟨lifetime, 0⟩)
  nextId : after.nextId = before.nextId
  nextAddress : after.nextAddress = before.nextAddress
  allocations : ∀ other, other ≠ lifetime → after.heap.lookup other = before.heap.lookup other

theorem Frame.trans (first : Frame runtimeSafety before middle lifetime) (second : Frame runtimeSafety middle after lifetime) :
    Frame runtimeSafety before after lifetime :=
  ⟨second.valid, first.shape.trans second.shape, second.header.trans first.header,
    second.nextId.trans first.nextId, second.nextAddress.trans first.nextAddress,
    fun other different => (second.allocations other different).trans (first.allocations other different)⟩

structure Written (runtimeSafety : Bool) (before after : State) (lifetime : Nat) (slot : Slot) : Prop extends
    Frame runtimeSafety before after lifetime where
  value : read runtimeSafety after ⟨lifetime, 0⟩ slot = .ok slot.value
  others : ∀ queried, queried.Active runtimeSafety → queried ≠ slot →
    read runtimeSafety after ⟨lifetime, 0⟩ queried = read runtimeSafety before ⟨lifetime, 0⟩ queried

/-- The same frame permits changed native map fields, retaining every other
field, representative header, allocation and lifetime counter. -/
structure WrittenValue (runtimeSafety : Bool) (before after : State) (lifetime : Nat)
    (slot : Slot) (stored : Value) : Prop extends Frame runtimeSafety before after lifetime where
  value : read runtimeSafety after ⟨lifetime, 0⟩ slot = .ok stored
  others : ∀ queried, queried.Active runtimeSafety → queried ≠ slot →
    read runtimeSafety after ⟨lifetime, 0⟩ queried = read runtimeSafety before ⟨lifetime, 0⟩ queried

theorem write_value_verified (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (slot : Slot)
    (value : Value) (valueType : value.type = slot.value.type) (valueValid : value.valid = true)
    (active : slot.Active runtimeSafety) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (writable : cell.writable = true) :
    ∃ after, writeValue runtimeSafety state ⟨lifetime, 0⟩ slot value = .ok after ∧
      WrittenValue runtimeSafety state after lifetime slot value := by
  obtain ⟨after, stored⟩ := store_value_total runtimeSafety state lifetime cell slot value valueType valueValid active initial found typed writable
  refine ⟨after, ?_, ?_⟩
  · simp only [writeValue, root_pointer runtimeSafety state lifetime cell true slot active initial found typed, bind, Except.bind]
    exact stored
  · refine ⟨⟨store_preserves_valid _ _ _ _ initial stored, store_retains_shape _ _ _ _ stored,
        ?_, (store_keeps_counters _ _ _ _ stored).1, (store_keeps_counters _ _ _ _ stored).2,
        heap_after_store_other _ true false slot.value.type _ _ _ stored⟩,
      read_after_store_value runtimeSafety state after lifetime cell slot value active initial found typed stored, ?_⟩
    · apply header_frame_of_store runtimeSafety state after lifetime cell value ((Owner.expressionsOffset runtimeSafety) + (slot.offset runtimeSafety))
        initial found typed (by simpa only [valueType] using stored)
      all_goals
        rw [slot.leaves value _ valueType]
        simp only [List.mem_singleton, forall_eq]
        cases slot <;> cases runtimeSafety <;> decide
    · intro queried admitted different
      exact read_frame_value runtimeSafety state after lifetime cell value slot queried valueType admitted different initial found typed stored

theorem write_verified (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (slot : Slot)
    (active : slot.Active runtimeSafety) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (writable : cell.writable = true) :
    ∃ after, write runtimeSafety state ⟨lifetime, 0⟩ slot = .ok after ∧ Written runtimeSafety state after lifetime slot := by
  obtain ⟨after, ran, post⟩ := write_value_verified runtimeSafety state lifetime cell slot slot.value rfl
    (by cases slot <;> decide) active initial found typed writable
  exact ⟨after, (write_default runtimeSafety state ⟨lifetime, 0⟩ slot).trans ran, post.toFrame, post.value, post.others⟩

def run (runtimeSafety : Bool) (state : State) (owner : Address) : Except Fault State := do
  let metadata ← write runtimeSafety state owner .metadata
  let counted ← initializeSize runtimeSafety metadata owner
  let available ← write runtimeSafety counted owner .available
  if runtimeSafety then write runtimeSafety available owner .lock else .ok available

theorem run_of_writes (runtimeSafety : Bool) (state metadata counted available after : State) (owner : Address)
    (first : write runtimeSafety state owner .metadata = .ok metadata)
    (second : initializeSize runtimeSafety metadata owner = .ok counted)
    (third : write runtimeSafety counted owner .available = .ok available)
    (last : (if runtimeSafety then write runtimeSafety available owner .lock else .ok available) = .ok after) :
    run runtimeSafety state owner = .ok after := by
  simpa only [run, first, second, third, bind, Except.bind] using last

structure Initialized (runtimeSafety : Bool) (before after : State) (lifetime : Nat) : Prop extends
    Frame runtimeSafety before after lifetime where
  fields : ∀ slot, slot.Active runtimeSafety → read runtimeSafety after ⟨lifetime, 0⟩ slot = .ok slot.value

/-- The same native default assignment establishes all active fields. The
initial contents, successful stores, final fields and frames are not premises. -/
theorem initialize_verified (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) (writable : cell.writable = true) :
    ∃ after, run runtimeSafety state ⟨lifetime, 0⟩ = .ok after ∧ Initialized runtimeSafety state after lifetime := by
  obtain ⟨metadata, metaRun, metadataWrite⟩ := write_verified runtimeSafety state lifetime cell .metadata (by simp [Slot.Active])
    initial found typed writable
  obtain ⟨metaCell, metaFound, metaShape⟩ := metadataWrite.shape lifetime cell found
  obtain ⟨counted, countRun, count⟩ := write_verified runtimeSafety metadata lifetime metaCell .size (by simp [Slot.Active])
    metadataWrite.valid metaFound (metaShape.2.1.trans typed) (metaShape.2.2.1.trans writable)
  rw [size_write] at countRun
  obtain ⟨countCell, countFound, countShape⟩ := count.shape lifetime metaCell metaFound
  obtain ⟨available, availableRun, avail⟩ := write_verified runtimeSafety counted lifetime countCell .available (by simp [Slot.Active])
    count.valid countFound (countShape.2.1.trans (metaShape.2.1.trans typed))
    (countShape.2.2.1.trans (metaShape.2.2.1.trans writable))
  have frame := (metadataWrite.toFrame.trans count.toFrame).trans avail.toFrame
  have fields : ∀ slot, slot ≠ .lock → read runtimeSafety available ⟨lifetime, 0⟩ slot = .ok slot.value := by
    intro slot nonlock
    have active : slot.Active runtimeSafety := by intro locked; exact False.elim (nonlock locked)
    cases slot with
    | metadata => exact (avail.others _ active (by decide)).trans ((count.others _ active (by decide)).trans metadataWrite.value)
    | size => exact (avail.others _ active (by decide)).trans count.value
    | available => exact avail.value
    | lock => exact False.elim (nonlock rfl)
  cases runtimeSafety with
  | false =>
    refine ⟨available, ?_, frame, ?_⟩
    · exact run_of_writes false state metadata counted available available ⟨lifetime, 0⟩ metaRun countRun availableRun rfl
    · intro slot active
      apply fields slot
      intro locked
      have impossible := active locked
      contradiction
  | true =>
    obtain ⟨availableCell, availableFound, availableShape⟩ := frame.shape lifetime cell found
    obtain ⟨after, lockRun, locked⟩ := write_verified true available lifetime availableCell .lock (by simp [Slot.Active])
      frame.valid availableFound (availableShape.2.1.trans typed) (availableShape.2.2.1.trans writable)
    refine ⟨after, ?_, frame.trans locked.toFrame, ?_⟩
    · exact run_of_writes true state metadata counted available after ⟨lifetime, 0⟩ metaRun countRun availableRun lockRun
    · intro slot active
      by_cases last : slot = .lock
      · subst slot; exact locked.value
      · exact (locked.others slot active last).trans (fields slot last)

/-- This is the checked projection of an initialized empty native map, not a
replacement for nonempty bucket enumeration. Unknown or inconsistent contents
remain explicit rejections. The observation does not dereference a pointee. -/
def observeEmpty (runtimeSafety : Bool) (state : State) (owner : Address) : Except Fault Unit := do
  let metadata ← read runtimeSafety state owner .metadata
  if metadata ≠ Slot.metadata.value then .error .unsupported else do
  let size ← read runtimeSafety state owner .size
  if size ≠ Slot.size.value then .error .unsupported else do
  let available ← read runtimeSafety state owner .available
  if available ≠ Slot.available.value then .error .unsupported else do
  if runtimeSafety then
    let lock ← read runtimeSafety state owner .lock
    if lock ≠ Slot.lock.value then .error .unsupported else .ok ()
  else .ok ()

theorem rejects_metadata (runtimeSafety : Bool) (state : State) (owner : Address) (value : Value)
    (loaded : read runtimeSafety state owner .metadata = .ok value) (different : value ≠ Slot.metadata.value) :
    observeEmpty runtimeSafety state owner = .error .unsupported := by
  simp only [observeEmpty, loaded, bind, Except.bind, if_pos different]

theorem rejects_size (runtimeSafety : Bool) (state : State) (owner : Address) (value : Value)
    (metadata : read runtimeSafety state owner .metadata = .ok Slot.metadata.value)
    (loaded : read runtimeSafety state owner .size = .ok value) (different : value ≠ Slot.size.value) :
    observeEmpty runtimeSafety state owner = .error .unsupported := by
  simp only [observeEmpty, metadata, loaded, bind, Except.bind, ne_eq, not_true_eq_false, ↓reduceIte, if_pos different]

theorem rejects_available (runtimeSafety : Bool) (state : State) (owner : Address) (value : Value)
    (metadata : read runtimeSafety state owner .metadata = .ok Slot.metadata.value)
    (size : read runtimeSafety state owner .size = .ok Slot.size.value)
    (loaded : read runtimeSafety state owner .available = .ok value) (different : value ≠ Slot.available.value) :
    observeEmpty runtimeSafety state owner = .error .unsupported := by
  simp only [observeEmpty, metadata, size, loaded, bind, Except.bind, ne_eq, not_true_eq_false, ↓reduceIte, if_pos different]

theorem rejects_lock (state : State) (owner : Address) (value : Value)
    (metadata : read true state owner .metadata = .ok Slot.metadata.value)
    (size : read true state owner .size = .ok Slot.size.value)
    (available : read true state owner .available = .ok Slot.available.value)
    (loaded : read true state owner .lock = .ok value) (different : value ≠ Slot.lock.value) :
    observeEmpty true state owner = .error .unsupported := by
  simp only [observeEmpty, metadata, size, available, loaded, bind, Except.bind, ne_eq, not_true_eq_false, ↓reduceIte, if_pos different]

theorem missing_lock (state : State) (owner : Address) (fault : Fault)
    (metadata : read true state owner .metadata = .ok Slot.metadata.value)
    (size : read true state owner .size = .ok Slot.size.value)
    (available : read true state owner .available = .ok Slot.available.value)
    (loaded : read true state owner .lock = .error fault) :
    observeEmpty true state owner = .error fault := by
  simp only [observeEmpty, metadata, size, available, loaded, bind, Except.bind, ne_eq, not_true_eq_false, ↓reduceIte]

theorem Initialized.observed (initialized : Initialized runtimeSafety before after lifetime) :
    observeEmpty runtimeSafety after ⟨lifetime, 0⟩ = .ok () := by
  simp only [observeEmpty, initialized.fields .metadata (by simp [Slot.Active]),
    initialized.fields .size (by simp [Slot.Active]), initialized.fields .available (by simp [Slot.Active]),
    bind, Except.bind, ne_eq, not_true_eq_false, ↓reduceIte]
  split
  · rename_i safety
    rw [initialized.fields .lock (by intro _; exact safety)]
    rfl
  · rfl

end Compiler.Extraction.ExpressionMap.Initialization
