/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayFields
import Compiler.ZigAir.MemoryRecordWrites
import Compiler.ZigAir.MemoryWordArray

namespace Compiler.Extraction.RepresentativeArray
open Compiler.ZigAir.Memory
open Compiler.Algebraic

/-- Project the existing captured field table; no independent layout or second
descriptor representation is introduced by initialization. -/
def expressionSlots : List (Nat × Ty) := match Expression.allocationType with
  | .aggregate _ _ fields => fields.map (fun field => (field.1, field.2.type))
  | _ => []

private theorem slot_geometry (offset : Nat) (type : Ty) (member : (offset, type) ∈ expressionSlots) :
    ∃ layout, type.layout = some layout ∧ 0 < layout.bytes ∧ offset + layout.bytes ≤ 32 ∧
      offset % layout.alignment = 0 ∧ 8 % layout.alignment = 0 := by
  simp only [expressionSlots, Expression.allocationType, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, Field.type, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨_, rfl, by decide⟩

private theorem slot_view (capacity index offset : Nat) (value : Value)
    (inside : index < capacity) (member : (offset, value.type) ∈ expressionSlots) (valid : value.valid = true) :
    acceptsView (.array capacity Expression.allocationType) (index * 32 + offset) value.type = true ∧
    (∀ entry ∈ value.leaves 0,
      leafType (.array capacity Expression.allocationType) (index * 32 + offset + entry.1) = some entry.2.type) := by
  have quotient (localOffset : Nat) (bounded : localOffset < 32) : (index * 32 + localOffset) / 32 = index := by omega
  have remainder (localOffset : Nat) (bounded : localOffset < 32) : (index * 32 + localOffset) % 32 = localOffset := by omega
  simp only [expressionSlots, Expression.allocationType, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, Field.type, Prod.mk.injEq] at member
  rcases member with ⟨rfl, typed⟩ | ⟨rfl, typed⟩ | ⟨rfl, typed⟩ | ⟨rfl, typed⟩
  all_goals cases value with
    | optionalScalar _ _ | optionalObject _ _ _ => cases typed
    | scalar value =>
      simp only [Value.type] at typed
      all_goals try contradiction
      all_goals cases value <;> simp_all [acceptsView, leafType, Expression.allocationType, Ty.aggregateValid, checkFields, Field.layouts, Field.layout, Field.contains,
        Field.type, Ty.layout, Ty.leafLayout, Value.leaves, Value.type, Compiler.ZigAir.Scalar.Value.type,
        Value.valid]
    | pointer type address =>
      simp only [Value.type] at typed
      all_goals try contradiction
      all_goals subst type
      all_goals simp_all [acceptsView, leafType, Expression.allocationType, Ty.aggregateValid, checkFields, Field.layouts, Field.layout, Field.contains,
        Field.type, Ty.layout, Ty.leafLayout, Value.leaves, Value.type, Value.valid]
    | slice type address length =>
      simp only [Value.type] at typed
      all_goals try contradiction
      all_goals subst type
      all_goals simp_all [acceptsView, leafType, Expression.allocationType, Ty.aggregateValid, checkFields, Field.layouts, Field.layout, Field.contains,
        Field.type, Ty.layout, Ty.leafLayout, Value.leaves, Value.type, Compiler.ZigAir.Scalar.Value.type,
        Value.valid, usize, Nat.add_assoc]

/-- Every valid field value can initialize its actual slot in a ready array
element. The write access and typed leaves are derived from captured geometry,
not an allocator response, initialized destination or successful-store premise. -/
theorem field_store_total (state : State) (lifetime capacity index : Nat) (cell : Allocation)
    (offset : Nat) (value : Value) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : index < capacity) (member : (offset, value.type) ∈ expressionSlots) (valid : value.valid = true) :
    ∃ after, store state (.pointer (.pointer true false value.type) ⟨lifetime, index * 32 + offset⟩) value = .ok after := by
  obtain ⟨layout, shaped, positive, bounded, aligned, divided⟩ := slot_geometry offset value.type member
  have parent := array_access state lifetime capacity index 32 Expression.allocationType ⟨32, 8⟩ cell
    initial found typed writable Expression.layout_checked (by decide) (by decide) inside (by decide) true
  dsimp only at parent
  have accessed := access_subregion state ⟨lifetime, index * 32⟩ ⟨32, 8⟩ layout offset true cell
    parent positive bounded aligned divided
  have declared := slot_view capacity index offset value inside member valid
  exact store_subobject_total state ⟨lifetime, index * 32 + offset⟩ layout cell value valid shaped accessed
    (typed.symm ▸ declared.1) (typed.symm ▸ declared.2)

/-- Evaluated descriptor values in the existing captured layout order. This
list is an assignment schedule, not a second descriptor or storage layout. -/
def descriptorFields (itemAddress argumentsAddress : Address) (length : Nat) (id sequence : Int) : List (Nat × Value) :=
  [(Expression.itemOffset, .pointer Expression.itemType itemAddress),
   (Expression.argumentsOffset, .slice Expression.argumentsType argumentsAddress length),
   (Expression.idOffset, .scalar (.int false 32 id)),
   (Expression.sequence_numberOffset, .scalar (.int false 32 sequence))]

/-- Each checked store retains earlier stores on rejection. The schedule refines
aggregate assignment for already evaluated values; it does not describe Zig
initializer evaluation or native behavior of an invalid descriptor. -/
def writeFields (state : State) (lifetime index : Nat) (fields : List (Nat × Value)) : Except Fault Unit × State :=
  match fields with
  | [] => (.ok (), state)
  | (offset, value) :: rest =>
    match store state (.pointer (.pointer true false value.type) ⟨lifetime, index * 32 + offset⟩) value with
    | .error fault => (.error fault, state)
    | .ok after => writeFields after lifetime index rest

def initializeFieldsReached (state : State) (lifetime index : Nat) (itemAddress argumentsAddress : Address)
    (length : Nat) (id sequence : Int) : Except Fault Unit × State :=
  writeFields state lifetime index (descriptorFields itemAddress argumentsAddress length id sequence)

/-- Retain the successful-store facade; the reached executor is authoritative
for both success and diagnostic rejection. -/
def initializeFields (state : State) (lifetime index : Nat) (itemAddress argumentsAddress : Address)
    (length : Nat) (id sequence : Int) : Except Fault State :=
  match initializeFieldsReached state lifetime index itemAddress argumentsAddress length id sequence with
  | (.error fault, _) => .error fault
  | (.ok (), after) => .ok after

theorem initializeFields_reached_iff (state after : State) (lifetime index : Nat) (itemAddress argumentsAddress : Address)
    (length : Nat) (id sequence : Int) :
    initializeFields state lifetime index itemAddress argumentsAddress length id sequence = .ok after ↔
      initializeFieldsReached state lifetime index itemAddress argumentsAddress length id sequence = (.ok (), after) := by
  unfold initializeFields
  cases executed : initializeFieldsReached state lifetime index itemAddress argumentsAddress length id sequence with
  | mk result reached => cases result <;> simp

/-- Every prefix preserves validity, allocation geometry and all other
lifetimes, including after a malformed later value rejects. -/
theorem writeFields_storage (fields : List (Nat × Value)) (state : State) (lifetime index : Nat)
    (initial : state.valid = true) :
    (writeFields state lifetime index fields).2.valid = true ∧
      state.heap.RetainsShape (writeFields state lifetime index fields).2.heap ∧
      (writeFields state lifetime index fields).2.nextId = state.nextId ∧
      (writeFields state lifetime index fields).2.nextAddress = state.nextAddress ∧
      (∀ other, other ≠ lifetime → (writeFields state lifetime index fields).2.heap.lookup other = state.heap.lookup other) := by
  induction fields generalizing state with
  | nil => exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl⟩
  | cons field rest ih =>
    rcases field with ⟨offset, value⟩
    simp only [writeFields]
    cases stored : store state (.pointer (.pointer true false value.type) ⟨lifetime, index * 32 + offset⟩) value with
    | error fault => exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl⟩
    | ok after =>
      have tail := ih after (store_preserves_valid _ _ _ _ initial stored)
      have counters := store_keeps_counters _ _ _ _ stored
      exact ⟨tail.1, (store_retains_shape _ _ _ _ stored).trans tail.2.1,
        tail.2.2.1.trans counters.1, tail.2.2.2.1.trans counters.2,
        fun other apart => (tail.2.2.2.2 other apart).trans (heap_after_store_other _ _ _ _ _ _ _ stored other apart)⟩

theorem initializeFields_of_stores (state withItem withArguments withId after : State)
    (lifetime index : Nat) (itemAddress argumentsAddress : Address) (length : Nat) (id sequence : Int)
    (storedItem : store state (.pointer (.pointer true false Expression.itemType)
      ⟨lifetime, index * 32 + Expression.itemOffset⟩) (.pointer Expression.itemType itemAddress) = .ok withItem)
    (storedArguments : store withItem (.pointer (.pointer true false Expression.argumentsType)
      ⟨lifetime, index * 32 + Expression.argumentsOffset⟩) (.slice Expression.argumentsType argumentsAddress length) = .ok withArguments)
    (storedId : store withArguments (.pointer (.pointer true false Expression.idType)
      ⟨lifetime, index * 32 + Expression.idOffset⟩) (.scalar (.int false 32 id)) = .ok withId)
    (storedSequence : store withId (.pointer (.pointer true false Expression.idType)
      ⟨lifetime, index * 32 + Expression.sequence_numberOffset⟩) (.scalar (.int false 32 sequence)) = .ok after) :
    initializeFields state lifetime index itemAddress argumentsAddress length id sequence = .ok after := by
  simp only [Expression.idType] at storedId storedSequence
  simp only [initializeFields, initializeFieldsReached, descriptorFields, writeFields, Value.type,
    Compiler.ZigAir.Scalar.Value.type, storedItem, storedArguments, storedId, storedSequence]

/-- Derive all reached descriptor stores from live writable array geometry and
valid source values. No initialized destination or successful-store premise is
needed, including for the slice's two leaves. -/
theorem initializeFields_stores (state : State) (lifetime capacity index : Nat) (cell : Allocation)
    (itemAddress argumentsAddress : Address) (length : Nat) (id sequence : Int)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : index < capacity) (lengthValid : length < addressLimit)
    (idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains id = true)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true) :
    ∃ withItem withArguments withId after,
      store state (.pointer (.pointer true false Expression.itemType)
        ⟨lifetime, index * 32 + Expression.itemOffset⟩) (.pointer Expression.itemType itemAddress) = .ok withItem ∧
      store withItem (.pointer (.pointer true false Expression.argumentsType)
        ⟨lifetime, index * 32 + Expression.argumentsOffset⟩) (.slice Expression.argumentsType argumentsAddress length) = .ok withArguments ∧
      store withArguments (.pointer (.pointer true false Expression.idType)
        ⟨lifetime, index * 32 + Expression.idOffset⟩) (.scalar (.int false 32 id)) = .ok withId ∧
      store withId (.pointer (.pointer true false Expression.idType)
        ⟨lifetime, index * 32 + Expression.sequence_numberOffset⟩) (.scalar (.int false 32 sequence)) = .ok after := by
  obtain ⟨withItem, storedItem⟩ := field_store_total state lifetime capacity index cell Expression.itemOffset
    (.pointer Expression.itemType itemAddress) initial found typed writable inside (by simp only [Value.type]; decide) rfl
  have validItem := store_preserves_valid _ _ _ _ initial storedItem
  obtain ⟨itemCell, foundItem, shapeItem⟩ := store_retains_shape _ _ _ _ storedItem lifetime cell found
  obtain ⟨withArguments, storedArguments⟩ := field_store_total withItem lifetime capacity index itemCell Expression.argumentsOffset
    (.slice Expression.argumentsType argumentsAddress length) validItem foundItem (shapeItem.2.1.trans typed)
    (shapeItem.2.2.1.trans writable) inside (by simp only [Value.type]; decide)
    (by simpa only [Value.valid, Expression.argumentsType, decide_eq_true_eq] using lengthValid)
  have validArguments := store_preserves_valid _ _ _ _ validItem storedArguments
  obtain ⟨argumentCell, foundArguments, shapeArguments⟩ := store_retains_shape _ _ _ _ storedArguments lifetime itemCell foundItem
  obtain ⟨withId, storedId⟩ := field_store_total withArguments lifetime capacity index argumentCell Expression.idOffset
    (.scalar (.int false 32 id)) validArguments foundArguments (shapeArguments.2.1.trans (shapeItem.2.1.trans typed))
    (shapeArguments.2.2.1.trans (shapeItem.2.2.1.trans writable)) inside
    (by simp only [Value.type, Compiler.ZigAir.Scalar.Value.type]; decide) idValid
  have validId := store_preserves_valid _ _ _ _ validArguments storedId
  obtain ⟨idCell, foundId, shapeId⟩ := store_retains_shape _ _ _ _ storedId lifetime argumentCell foundArguments
  obtain ⟨after, storedSequence⟩ := field_store_total withId lifetime capacity index idCell Expression.sequence_numberOffset
    (.scalar (.int false 32 sequence)) validId foundId (shapeId.2.1.trans (shapeArguments.2.1.trans (shapeItem.2.1.trans typed)))
    (shapeId.2.2.1.trans (shapeArguments.2.2.1.trans (shapeItem.2.2.1.trans writable))) inside
    (by simp only [Value.type, Compiler.ZigAir.Scalar.Value.type]; decide) sequenceValid
  exact ⟨withItem, withArguments, withId, after, storedItem, storedArguments, storedId, storedSequence⟩

/-- The actual four-store refinement executes, establishes readonly complete
readback and preserves the existing heap's allocation geometry. The native
header/backing construction and append are separate compiler obligations. -/
theorem initializeFields_verified (state : State) (lifetime capacity index : Nat) (cell : Allocation)
    (itemAddress argumentsAddress : Address) (length : Nat) (id sequence : Int)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : index < capacity) (lengthValid : length < addressLimit)
    (idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains id = true)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true) :
    ∃ after, initializeFields state lifetime index itemAddress argumentsAddress length id sequence = .ok after ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      Expression.readFields after false ⟨lifetime, index * 32⟩ = .ok [.pointer Expression.itemType itemAddress,
        .slice Expression.argumentsType argumentsAddress length, .scalar (.int false 32 id), .scalar (.int false 32 sequence)] := by
  obtain ⟨withItem, withArguments, withId, after, storedItem, storedArguments, storedId, storedSequence⟩ :=
    initializeFields_stores state lifetime capacity index cell itemAddress argumentsAddress length id sequence
      initial found typed writable inside lengthValid idValid sequenceValid
  refine ⟨after, ?_, ?_, ?_, ?_⟩
  · exact initializeFields_of_stores state withItem withArguments withId after lifetime index itemAddress argumentsAddress
      length id sequence storedItem storedArguments storedId storedSequence
  · exact store_preserves_valid _ _ _ _ (store_preserves_valid _ _ _ _
      (store_preserves_valid _ _ _ _ (store_preserves_valid _ _ _ _ initial storedItem) storedArguments) storedId) storedSequence
  · exact (store_retains_shape _ _ _ _ storedItem).trans ((store_retains_shape _ _ _ _ storedArguments).trans
      ((store_retains_shape _ _ _ _ storedId).trans (store_retains_shape _ _ _ _ storedSequence)))
  · exact fields_after_array_stores state withItem withArguments withId after lifetime capacity index cell
      itemAddress argumentsAddress length id sequence initial found typed writable inside
      storedItem storedArguments storedId storedSequence

/-- Compose descriptor initialization with the source-bound native lookup.
The four successful stores and final reader are derived together. This still
requires the initial live header/backing mapping; it does not prove append,
payload ownership, graph initialization or recursive correspondence. -/
theorem representativeFields_after_initialization (state : State) (header : Address)
    (lifetime capacity length : Nat) (cell : Allocation) (id : NodeId)
    (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (sequence : Int)
    (initial : state.valid = true)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (extent : length ≤ capacity) (inside : id.toNat < length) (apart : header.allocation ≠ lifetime)
    (argumentsValid : argumentsLength < addressLimit)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true) :
    ∃ after, initializeFields state lifetime id.toNat itemAddress argumentsAddress argumentsLength id.toNat sequence = .ok after ∧
      representativeFields after header id = .ok (.ok [.pointer Expression.itemType itemAddress,
        .slice Expression.argumentsType argumentsAddress argumentsLength,
        .scalar (.int false 32 id.toNat), .scalar (.int false 32 sequence)]) := by
  have idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains (id.toNat : Int) = true :=
    WordArray.number_valid id
  obtain ⟨withItem, withArguments, withId, after, storedItem, storedArguments, storedId, storedSequence⟩ :=
    initializeFields_stores state lifetime capacity id.toNat cell itemAddress argumentsAddress argumentsLength id.toNat sequence
      initial found typed writable (by omega) argumentsValid idValid sequenceValid
  refine ⟨after, ?_, ?_⟩
  · exact initializeFields_of_stores state withItem withArguments withId after lifetime id.toNat itemAddress argumentsAddress
      argumentsLength id.toNat sequence storedItem storedArguments storedId storedSequence
  · exact representativeFields_after_stores state withItem withArguments withId after header lifetime capacity length cell id
      itemAddress argumentsAddress argumentsLength sequence initial loaded found typed writable extent inside apart
      storedItem storedArguments storedId storedSequence

end Compiler.Extraction.RepresentativeArray
