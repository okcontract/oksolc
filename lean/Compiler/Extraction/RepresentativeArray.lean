/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayLayout
import Compiler.Extraction.ExpressionFields
import Compiler.Extraction.StorageProgram
import Compiler.ZigAir.MemoryRecordViews
import Compiler.ZigAir.MemoryArrayGeometry

namespace Compiler.Extraction.RepresentativeArray
open Compiler.ZigAir.Memory
open Compiler.Algebraic

theorem layout_checked : allocationType.layout = some ⟨24, 8⟩ := by decide
theorem element_layout_checked : elementType.layout = some ⟨32, 8⟩ := by decide
theorem field_types_checked : fieldType allocationType itemsOffset = some itemsType ∧
    fieldType allocationType capacityOffset = some usize := by decide

/-- The slice pointer is a nested field, distinct from the whole items slice.
Readers and publication share the same checked place and lifetime resolution. -/
def itemsDataPointer (state : State) (header : Address) (writable : Bool) : Except Fault Value := do
  let items ← fieldPointer state (.pointer (.pointer writable false allocationType) header) itemsOffset
  fieldPointer state items 0

def readField (state : State) (header : Address) (offset : Nat) : Except Fault Value := do
  let field ← fieldPointer state (.pointer (.pointer false false allocationType) header) offset
  load state field

theorem readField_eq_of_lookup (before after : State) (header : Address) (offset : Nat)
    (same : after.heap.lookup header.allocation = before.heap.lookup header.allocation) :
    readField after header offset = readField before header offset := by
  simp only [readField, fieldPointer_eq_of_lookup before after false false allocationType header offset same]
  cases selected : fieldPointer before (.pointer (.pointer false false allocationType) header) offset with
  | error fault => rfl
  | ok pointer =>
    obtain ⟨child, _, rfl⟩ := fieldPointer_address before false false allocationType header offset pointer selected
    exact load_eq_of_lookup before after false false child ⟨header.allocation, header.offset + offset⟩ same

def readItems (state : State) (header : Address) : Except Fault Value := readField state header itemsOffset

def readItemsData (state : State) (header : Address) : Except Fault Value := do
  let pointer ← itemsDataPointer state header false
  load state pointer

def readHeader (state : State) (header : Address) : Except Fault (Value × Value) := do
  let items ← readItems state header
  let capacity ← readField state header capacityOffset
  .ok (items, capacity)

/-- A successful complete header read contains its actual reached slice read. -/
theorem readHeader_items (state : State) (header : Address) (items capacity : Value)
    (loaded : readHeader state header = .ok (items, capacity)) : readItems state header = .ok items := by
  cases first : readItems state header with
  | error fault => simp only [readHeader, first, bind, Except.bind, reduceCtorEq] at loaded
  | ok value =>
    cases second : readField state header capacityOffset with
    | error fault => simp only [readHeader, first, second, bind, Except.bind, reduceCtorEq] at loaded
    | ok result =>
      simp only [readHeader, first, second, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at loaded
      exact congrArg Except.ok loaded.1

/-- The capacity is the second actual field read of the same header. -/
theorem readHeader_capacity (state : State) (header : Address) (items capacity : Value)
    (loaded : readHeader state header = .ok (items, capacity)) :
    readField state header capacityOffset = .ok capacity := by
  have first := readHeader_items state header items capacity loaded
  unfold readHeader at loaded
  rw [first] at loaded
  cases second : readField state header capacityOffset with
  | error fault => simp only [second, bind, Except.bind] at loaded; contradiction
  | ok value =>
    simp only [second, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at loaded
    rw [loaded.2]

/-- Reuse the admitted production bounds/index program. Memory failures remain
proof-side rejections, distinct from the native InvalidExpressionId outcome.
The nominal element reference is resolved against the same heap's complete
Expression subobject, then the native return's const permission is applied. -/
def representative (state : State) (header : Address) (id : NodeId) : Except Fault (Except Storage.ReadError Value) := do
  let view ← readItems state header
  let .slice _ _ length := view | .error .malformed
  if Storage.representativeProgram.bound.reject id.toNat length then return .error .invalidId else
  let element ← sliceElementPointer state view (Storage.representativeProgram.index.eval id)
  let complete ← recordView state Expression.allocationType element
  let readonly ← pointerCast state (.pointer false false Expression.allocationType) complete
  return .ok readonly

theorem readItems_from_root (state : State) (lifetime : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = allocationType) :
    readItems state ⟨lifetime, 0⟩ = load state (.pointer (.pointer false false itemsType) ⟨lifetime, itemsOffset⟩) := by
  have selected := root_fieldPointer state lifetime cell allocationType itemsType ⟨24, 8⟩ itemsOffset false false
    initial found typed layout_checked (by decide) field_types_checked.1
  simp only [readItems, readField, selected, bind, Except.bind]

/-- Both header members follow their reached stores in any declared subobject.
The later capacity store preserves the slice's pointer and length leaves. The
same checked selectors retain nonzero enclosing offsets; no initialized header
or final graph invariant is assumed. -/
theorem header_after_subobject_stores (state withItems after : State) (header data : Address)
    (length : Nat) (capacity : Int)
    (selectItems : fieldPointer state (.pointer (.pointer false false allocationType) header) itemsOffset =
      .ok (.pointer (.pointer false false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩))
    (selectCapacity : fieldPointer state (.pointer (.pointer false false allocationType) header) capacityOffset =
      .ok (.pointer (.pointer false false usize) ⟨header.allocation, header.offset + capacityOffset⟩))
    (storedItems : store state (.pointer (.pointer true false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩)
      (.slice itemsType data length) = .ok withItems)
    (storedCapacity : store withItems (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + capacityOffset⟩)
      (.scalar (.int false 64 capacity)) = .ok after) :
    readHeader after header = .ok (.slice itemsType data length, .scalar (.int false 64 capacity)) := by
  have selectors (offset : Nat) :
      fieldPointer after (.pointer (.pointer false false allocationType) header) offset =
        fieldPointer state (.pointer (.pointer false false allocationType) header) offset :=
    (fieldPointer_after_store _ _ _ _ false false _ _ offset storedCapacity).trans
      (fieldPointer_after_store _ _ _ _ false false _ _ offset storedItems)
  have frame := load_disjoint_after_store withItems true false usize ⟨header.allocation, header.offset + capacityOffset⟩
    (.scalar (.int false 64 capacity)) after false false itemsType (header.offset + itemsOffset) storedCapacity
    (by simp [Ty.readOffsets, itemsType, Value.leaves, itemsOffset, capacityOffset])
  have itemsRead := frame.trans (load_alias_after_store _ true false _ _ _ _ false false storedItems)
  have capacityRead := load_alias_after_store _ true false _ _ _ _ false false storedCapacity
  simp only [readHeader, readItems, readField, selectors, selectItems, selectCapacity,
    bind, Except.bind, itemsRead, capacityRead]

/-- The root facade derives the same selectors from valid declared storage.
Embedded owners reuse the subobject readback rather than another field reader. -/
theorem header_after_stores (state withItems after : State) (lifetime : Nat) (cell : Allocation)
    (data : Address) (length : Nat) (capacity : Int) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = allocationType)
    (storedItems : store state (.pointer (.pointer true false itemsType) ⟨lifetime, itemsOffset⟩)
      (.slice itemsType data length) = .ok withItems)
    (storedCapacity : store withItems (.pointer (.pointer true false usize) ⟨lifetime, capacityOffset⟩)
      (.scalar (.int false 64 capacity)) = .ok after) :
    readHeader after ⟨lifetime, 0⟩ = .ok (.slice itemsType data length, .scalar (.int false 64 capacity)) :=
  header_after_subobject_stores state withItems after ⟨lifetime, 0⟩ data length capacity
    (root_fieldPointer state lifetime cell allocationType itemsType ⟨24, 8⟩ itemsOffset false false
      initial found typed layout_checked (by decide) field_types_checked.1)
    (root_fieldPointer state lifetime cell allocationType usize ⟨24, 8⟩ capacityOffset false false
      initial found typed layout_checked (by decide) field_types_checked.2) storedItems storedCapacity

/-- Invalid IDs do not inspect, dereference or manufacture backing for the
data pointer. In particular an empty header needs no live sentinel allocation. -/
theorem invalid_from_loaded_header (state : State) (header data : Address) (length : Nat) (id : NodeId)
    (loaded : readItems state header = .ok (.slice itemsType data length)) (outside : length ≤ id.toNat) :
    representative state header id = .ok (.error .invalidId) := by
  simp [representative, loaded, bind, Except.bind, pure, Except.pure,
    Storage.representativeProgram, Storage.Bound.reject, outside]

theorem element_pointer (state : State) (lifetime capacity index : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : index < capacity) :
    elementPointer state (.pointer (.pointer true true elementType) ⟨lifetime, 0⟩) index =
      .ok (.pointer (.pointer true false elementType) ⟨lifetime, index * 32⟩) := by
  have start := array_access state lifetime capacity 0 0 Expression.allocationType ⟨32, 8⟩ cell
    initial found typed writable Expression.layout_checked (by decide) (by decide) (by omega) (by omega) false
  have finish := array_access state lifetime capacity index 0 Expression.allocationType ⟨32, 8⟩ cell
    initial found typed writable Expression.layout_checked (by decide) (by decide) inside (by decide) false
  have element := array_access state lifetime capacity index 32 Expression.allocationType ⟨32, 8⟩ cell
    initial found typed writable Expression.layout_checked (by decide) (by decide) inside (by decide) false
  dsimp only at start finish element
  obtain ⟨_, positive, actual, shaped, _, bounded, limit⟩ := valid_lookup state lifetime cell initial found
  have arrayShape : cell.type.layout = some ⟨capacity * 32, 8⟩ := by
    simp only [typed, Ty.layout, Expression.layout_checked, bind, Option.bind]
  cases Option.some.inj (shaped.symm.trans arrayShape)
  dsimp only at bounded
  have rawBounds : ¬((cell.base : Int) + (0 : Nat) + (index * 32 : Nat) < 0 ∨
      (cell.base : Int) + (0 : Nat) + (index * 32 : Nat) ≥ addressLimit) := by omega
  have lower : ¬(cell.base : Int) + (0 : Nat) + (index * 32 : Nat) < cell.base := by omega
  have offset : ((cell.base : Int) + (0 : Nat) + (index * 32 : Nat)).toNat - cell.base = index * 32 := by omega
  simp only [elementPointer, offsetPointer, element_layout_checked, Nat.reduceEqDiff, ↓reduceIte,
    start, bind, Except.bind, if_neg rawBounds, if_neg lower, offset, finish,
    pointerCast, pointerCompatible, decide_true, Bool.and_false, Bool.true_or, Bool.false_or, Bool.not_true,
    Bool.false_eq_true, element]

theorem element_record_view (state : State) (lifetime capacity index : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : index < capacity) :
    recordView state Expression.allocationType (.pointer (.pointer true false elementType) ⟨lifetime, index * 32⟩) =
      .ok (.pointer (.pointer true false Expression.allocationType) ⟨lifetime, index * 32⟩) := by
  have accessed := array_access state lifetime capacity index 32 Expression.allocationType ⟨32, 8⟩ cell
    initial found typed writable Expression.layout_checked (by decide) (by decide) inside (by decide) false
  dsimp only at accessed
  have declared : acceptsView cell.type (index * 32) Expression.allocationType = true := by
    simp [typed, acceptsView, Expression.layout_checked, inside]
    split <;> rfl
  simp only [recordView, elementType, Expression.allocationType, ne_self_iff_false, or_self, ↓reduceIte]
  change (do let cell ← access state ⟨lifetime, index * 32⟩ ⟨32, 8⟩ false
             if !acceptsView cell.type (index * 32) Expression.allocationType then .error .unsupported
             else .ok (Value.pointer (.pointer true false Expression.allocationType) ⟨lifetime, index * 32⟩)) =
      Except.ok (Value.pointer (.pointer true false Expression.allocationType) ⟨lifetime, index * 32⟩)
  simp only [accessed, bind, Except.bind, declared, Bool.not_true, Bool.false_eq_true, ↓reduceIte]

theorem representative_from_array (state : State) (header : Address) (lifetime capacity length : Nat)
    (cell : Allocation) (id : NodeId) (initial : state.valid = true)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = .array capacity Expression.allocationType)
    (writable : cell.writable = true) (extent : length ≤ capacity) (inside : id.toNat < length) :
    representative state header id =
      .ok (.ok (.pointer (.pointer false false Expression.allocationType) ⟨lifetime, id.toNat * 32⟩)) := by
  have pointed := element_pointer state lifetime capacity id.toNat cell initial found typed writable (by omega)
  have resolved := element_record_view state lifetime capacity id.toNat cell initial found typed writable (by omega)
  have accessed := array_access state lifetime capacity id.toNat 32 Expression.allocationType ⟨32, 8⟩ cell
    initial found typed writable Expression.layout_checked (by decide) (by decide) (by omega) (by decide) false
  dsimp only at accessed
  obtain ⟨_, basePositive, actual, actualShape, _, bounded, limit⟩ :=
    valid_lookup state lifetime cell initial found
  have arrayShape : cell.type.layout = some ⟨capacity * 32, 8⟩ := by
    simp only [typed, Ty.layout, Expression.layout_checked, bind, Option.bind]
  cases Option.some.inj (actualShape.symm.trans arrayShape)
  dsimp only at bounded
  have width : ¬length ≥ addressLimit := by omega
  simp [representative, loaded, bind, Except.bind, pure, Except.pure,
    Storage.representativeProgram, Storage.Bound.reject, Storage.Index.eval,
    sliceElementPointer, itemsType, width, pointed, resolved,
    pointerCast, pointerCompatible, Expression.layout_checked, accessed, inside, Nat.not_le.mpr inside]

end Compiler.Extraction.RepresentativeArray
