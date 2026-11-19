/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArray
import Compiler.ZigAir.MemoryAllocationShape

namespace Compiler.Extraction.RepresentativeArray
open Compiler.ZigAir.Memory
open Compiler.Algebraic

/-- Observe all descriptor fields through the actual readonly representative
pointer. This is the native probe's observation projection, not another graph
or query interpreter. Pointer rejection and native invalid-ID remain distinct. -/
def representativeFields (state : State) (header : Address) (id : NodeId) :
    Except Fault (Except Storage.ReadError (List Value)) := do
  let result ← representative state header id
  match result with
  | .error fault => return .error fault
  | .ok (.pointer type address) =>
    if type ≠ .pointer false false Expression.allocationType then .error .malformed else
    return .ok (← Expression.readFields state false address)
  | .ok _ => .error .malformed

/-- The array's declared extent and complete element type derive every field
selector at the actual nonzero byte offset, before any payload is initialized. -/
theorem element_fieldPointer (state : State) (lifetime capacity index : Nat) (cell : Allocation)
    (offset : Nat) (field : Ty) (readWritable : Bool) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : index < capacity) (selected : fieldType Expression.allocationType offset = some field) :
    fieldPointer state (.pointer (.pointer readWritable false Expression.allocationType) ⟨lifetime, index * 32⟩) offset =
      .ok (.pointer (.pointer readWritable false field) ⟨lifetime, index * 32 + offset⟩) := by
  have accessed := array_access state lifetime capacity index 32 Expression.allocationType ⟨32, 8⟩ cell
    initial found typed writable Expression.layout_checked (by decide) (by decide) inside (by decide) false
  dsimp only at accessed
  have declared : acceptsView cell.type (index * 32) Expression.allocationType = true := by
    simp [typed, acceptsView, Expression.layout_checked, inside]
    split <;> rfl
  simp only [fieldPointer, Expression.layout_checked, accessed, bind, Except.bind, declared,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, selected]

/-- Readonly readback of every stored field is derived for the same live array
element. The complete final descriptor, selectors and initialized leaves are
conclusions; only the four actual reached stores are supplied. -/
theorem fields_after_array_stores (state withItem withArguments withId after : State)
    (lifetime capacity index : Nat) (cell : Allocation) (itemAddress argumentsAddress : Address)
    (length : Nat) (id sequence : Int) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : index < capacity)
    (storedItem : store state (.pointer (.pointer true false Expression.itemType)
      ⟨lifetime, index * 32 + Expression.itemOffset⟩) (.pointer Expression.itemType itemAddress) = .ok withItem)
    (storedArguments : store withItem (.pointer (.pointer true false Expression.argumentsType)
      ⟨lifetime, index * 32 + Expression.argumentsOffset⟩)
      (.slice Expression.argumentsType argumentsAddress length) = .ok withArguments)
    (storedId : store withArguments (.pointer (.pointer true false Expression.idType)
      ⟨lifetime, index * 32 + Expression.idOffset⟩) (.scalar (.int false 32 id)) = .ok withId)
    (storedSequence : store withId (.pointer (.pointer true false Expression.idType)
      ⟨lifetime, index * 32 + Expression.sequence_numberOffset⟩) (.scalar (.int false 32 sequence)) = .ok after) :
    Expression.readFields after false ⟨lifetime, index * 32⟩ = .ok [.pointer Expression.itemType itemAddress,
      .slice Expression.argumentsType argumentsAddress length, .scalar (.int false 32 id), .scalar (.int false 32 sequence)] := by
  apply Expression.fields_after_subobject_stores state withItem withArguments withId after
    ⟨lifetime, index * 32⟩ false itemAddress argumentsAddress length id sequence
    (fun offset field selected => element_fieldPointer state lifetime capacity index cell offset field false
      initial found typed writable inside selected) storedItem storedArguments storedId storedSequence

/-- Descriptor writes preserve the separate header's exact read, including a
rejection. This does not retain an element pointer across container relocation. -/
theorem readField_after_other_store (state after : State) (writeType : Ty) (writeAddress header : Address)
    (offset : Nat)
    (value : Value) (stored : store state (.pointer (.pointer true false writeType) writeAddress) value = .ok after)
    (apart : header.allocation ≠ writeAddress.allocation) : readField after header offset = readField state header offset := by
  have selector := fieldPointer_after_store state after _ value false false allocationType header offset stored
  unfold readField
  rw [selector]
  cases selected : fieldPointer state (.pointer (.pointer false false allocationType) header) offset with
  | error fault => rfl
  | ok pointer =>
    obtain ⟨field, _, same⟩ := fieldPointer_address state false false allocationType header offset pointer selected
    subst pointer
    exact load_other_after_store state true false writeType writeAddress value after false false field
      ⟨header.allocation, header.offset + offset⟩ stored apart

theorem readItems_after_other_store (state after : State) (writeType : Ty) (writeAddress header : Address)
    (value : Value) (stored : store state (.pointer (.pointer true false writeType) writeAddress) value = .ok after)
    (apart : header.allocation ≠ writeAddress.allocation) : readItems after header = readItems state header :=
  readField_after_other_store state after writeType writeAddress header itemsOffset value stored apart

/-- Compose source bounds/indexing and readonly field observation after actual
element stores. Neither final graph validity, initialized descriptor values nor
a successful final native reader is a premise. Header/backing construction,
append/growth and item/map correspondence remain separate compiler work. -/
theorem representativeFields_after_stores (state withItem withArguments withId after : State)
    (header : Address) (lifetime capacity length : Nat) (cell : Allocation) (id : NodeId)
    (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (sequence : Int)
    (initial : state.valid = true)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (extent : length ≤ capacity) (inside : id.toNat < length) (apart : header.allocation ≠ lifetime)
    (storedItem : store state (.pointer (.pointer true false Expression.itemType)
      ⟨lifetime, id.toNat * 32 + Expression.itemOffset⟩) (.pointer Expression.itemType itemAddress) = .ok withItem)
    (storedArguments : store withItem (.pointer (.pointer true false Expression.argumentsType)
      ⟨lifetime, id.toNat * 32 + Expression.argumentsOffset⟩)
      (.slice Expression.argumentsType argumentsAddress argumentsLength) = .ok withArguments)
    (storedId : store withArguments (.pointer (.pointer true false Expression.idType)
      ⟨lifetime, id.toNat * 32 + Expression.idOffset⟩) (.scalar (.int false 32 id.toNat)) = .ok withId)
    (storedSequence : store withId (.pointer (.pointer true false Expression.idType)
      ⟨lifetime, id.toNat * 32 + Expression.sequence_numberOffset⟩) (.scalar (.int false 32 sequence)) = .ok after) :
    representativeFields after header id = .ok (.ok [.pointer Expression.itemType itemAddress,
      .slice Expression.argumentsType argumentsAddress argumentsLength,
      .scalar (.int false 32 id.toNat), .scalar (.int false 32 sequence)]) := by
  have preserved := (store_retains_shape _ _ _ _ storedItem).trans
    ((store_retains_shape _ _ _ _ storedArguments).trans
      ((store_retains_shape _ _ _ _ storedId).trans (store_retains_shape _ _ _ _ storedSequence)))
  obtain ⟨updated, lookup, shape⟩ := preserved lifetime cell found
  have valid := store_preserves_valid _ _ _ _
    (store_preserves_valid _ _ _ _ (store_preserves_valid _ _ _ _
      (store_preserves_valid _ _ _ _ initial storedItem) storedArguments) storedId) storedSequence
  have itemsRead := (readItems_after_other_store _ _ _ _ header _ storedSequence apart).trans
    ((readItems_after_other_store _ _ _ _ header _ storedId apart).trans
      ((readItems_after_other_store _ _ _ _ header _ storedArguments apart).trans
        (readItems_after_other_store _ _ _ _ header _ storedItem apart)))
  have pointer := representative_from_array after header lifetime capacity length updated id valid
    (itemsRead.trans loaded) lookup (shape.2.1.trans typed) (shape.2.2.1.trans writable) extent inside
  have fields := fields_after_array_stores state withItem withArguments withId after lifetime capacity id.toNat cell
    itemAddress argumentsAddress argumentsLength id.toNat sequence initial found typed writable (by omega)
    storedItem storedArguments storedId storedSequence
  simp only [representativeFields, pointer, bind, Except.bind, ne_self_iff_false, ↓reduceIte, fields, pure, Except.pure]

end Compiler.Extraction.RepresentativeArray
