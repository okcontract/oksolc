/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeAppendProgram
import Compiler.Extraction.RepresentativeArrayWrites
import Compiler.ZigAir.MemorySliceUpdates

namespace Compiler.Extraction.RepresentativeArray.Append
open Compiler.ZigAir.Memory
open Compiler.Algebraic

def lengthOffset : Nat := itemsOffset + 8

theorem length_type_checked : fieldType allocationType lengthOffset = some usize := by decide

def writeLength (state : State) (header : Address) (length : Nat) : Except Fault State := do
  let field ← fieldPointer state (.pointer (.pointer true false allocationType) header) lengthOffset
  store state field (.scalar (.int false 64 length))

def selectNewElement (state : State) (header : Address) (newLength : Nat) : Except Fault Address := do
  let view ← readItems state header
  let element ← sliceElementPointer state view (selectedIndex newLength)
  let complete ← recordView state Expression.allocationType element
  let .pointer target address := complete | .error .malformed
  if target ≠ .pointer true false Expression.allocationType ∨ address.offset % 32 ≠ 0 then .error .unsupported else
  .ok address

/-- Scope rejection of a growing append is distinct from a native OOM. The
actual admitted spare-capacity path reads the header, increments only its length,
selects the new element through the updated slice and assigns evaluated fields.
Checked nominal conversion adds no native branch. No backing is manufactured. -/
def appendWithoutGrowth (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) : Except Fault State := do
  let loaded ← readHeader state header
  let (.slice type _ length, .scalar (.int false 64 capacity)) := loaded | .error .malformed
  if type ≠ itemsType then .error .unsupported else
  let newLength := nextLength length
  if !hasCapacity capacity.toNat newLength then .error .unsupported else
  let ready ← writeLength state header newLength
  let address ← selectNewElement ready header newLength
  initializeFields ready address.allocation (address.offset / 32) itemAddress argumentsAddress argumentsLength id sequence

theorem length_store_total (state : State) (header : Nat) (cell : Allocation) (length : Nat)
    (initial : state.valid = true) (found : state.heap.lookup header = some cell)
    (typed : cell.type = allocationType) (writable : cell.writable = true) (bounded : length < addressLimit) :
    ∃ after, writeLength state ⟨header, 0⟩ length = .ok after ∧
      store state (.pointer (.pointer true false usize) ⟨header, lengthOffset⟩) (.scalar (.int false 64 length)) = .ok after := by
  have selected := root_fieldPointer state header cell allocationType usize ⟨24, 8⟩ lengthOffset true false
    initial found typed layout_checked (by decide) length_type_checked
  obtain ⟨parentLayout, parent, parentShape, readable, _⟩ := fieldPointer_parent state true false allocationType ⟨header, 0⟩
    lengthOffset (.pointer (.pointer true false usize) ⟨header, lengthOffset⟩) selected
  have sameLayout : parentLayout = ⟨24, 8⟩ := Option.some.inj (parentShape.symm.trans layout_checked)
  subst parentLayout
  have sameParent : parent = cell := Option.some.inj (((access_success_region state ⟨header, 0⟩ ⟨24, 8⟩ false parent readable).1).symm.trans found)
  subst parent
  have writeParent := access_read_write state ⟨header, 0⟩ ⟨24, 8⟩ cell readable writable
  have accessed := access_subregion state ⟨header, 0⟩ ⟨24, 8⟩ ⟨8, 8⟩ lengthOffset true cell
    writeParent (by decide) (by decide) (by decide) (by decide)
  have valueValid := Value.usize_valid length bounded
  obtain ⟨after, stored⟩ := store_subobject_total state ⟨header, lengthOffset⟩ ⟨8, 8⟩ cell (.scalar (.int false 64 length)) valueValid rfl accessed
    (by rw [typed]; simp only [Value.type, Compiler.ZigAir.Scalar.Value.type]; decide)
    (by intro entry member; simp only [Value.leaves, List.mem_cons, List.not_mem_nil, or_false] at member
        subst entry; rw [typed]; simp only [Value.type, Compiler.ZigAir.Scalar.Value.type, Nat.add_zero]; decide)
  change store state (.pointer (.pointer true false usize) ⟨header, lengthOffset⟩)
    (.scalar (.int false 64 length)) = .ok after at stored
  exact ⟨after, by simp only [writeLength, selected, bind, Except.bind, stored], stored⟩

/-- The same length-store readback applies to both standalone and embedded
headers. The selector is derived by each containing-layout proof. -/
theorem readItems_after_length_store_at (state after : State) (header data : Address) (before length : Nat)
    (selector : fieldPointer state (.pointer (.pointer false false allocationType) header) itemsOffset =
      .ok (.pointer (.pointer false false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩))
    (loaded : readItems state header = .ok (.slice itemsType data before))
    (stored : store state (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + lengthOffset⟩)
      (.scalar (.int false 64 length)) = .ok after) :
    readItems after header = .ok (.slice itemsType data length) := by
  have retained := fieldPointer_after_store state after _ (.scalar (.int false 64 length)) false false allocationType header itemsOffset stored
  have raw : load state (.pointer (.pointer false false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩) = .ok (.slice itemsType data before) := by
    simpa only [readItems, readField, selector, bind, Except.bind] using loaded
  have readback := load_slice_after_length_store state after ⟨header.allocation, header.offset + itemsOffset⟩ data
    false false true elementType before length raw (by simpa only [lengthOffset, Nat.add_assoc] using stored)
  simpa only [readItems, readField, retained, selector, bind, Except.bind] using readback

theorem readItems_after_length_store (state after : State) (header : Nat) (cell : Allocation)
    (data : Address) (before length : Nat) (initial : state.valid = true)
    (found : state.heap.lookup header = some cell) (typed : cell.type = allocationType)
    (loaded : readItems state ⟨header, 0⟩ = .ok (.slice itemsType data before))
    (stored : store state (.pointer (.pointer true false usize) ⟨header, lengthOffset⟩) (.scalar (.int false 64 length)) = .ok after) :
    readItems after ⟨header, 0⟩ = .ok (.slice itemsType data length) :=
  readItems_after_length_store_at state after ⟨header, 0⟩ data before length
    (root_fieldPointer state header cell allocationType itemsType ⟨24, 8⟩ itemsOffset false false
      initial found typed layout_checked (by decide) field_types_checked.1) loaded stored

theorem readCapacity_after_length_store_at (state after : State) (header : Address) (length : Nat)
    (selector : fieldPointer state (.pointer (.pointer false false allocationType) header) capacityOffset =
      .ok (.pointer (.pointer false false usize) ⟨header.allocation, header.offset + capacityOffset⟩))
    (stored : store state (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + lengthOffset⟩)
      (.scalar (.int false 64 length)) = .ok after) :
    readField after header capacityOffset = readField state header capacityOffset := by
  have retained := fieldPointer_after_store state after _ (.scalar (.int false 64 length)) false false allocationType header capacityOffset stored
  have frame := load_disjoint_after_store state true false usize ⟨header.allocation, header.offset + lengthOffset⟩ (.scalar (.int false 64 length)) after
    false false usize (header.offset + capacityOffset) stored (by simp [Ty.readOffsets, usize, Value.leaves, capacityOffset, lengthOffset, itemsOffset])
  simpa only [readField, retained, selector, bind, Except.bind] using frame

theorem readCapacity_after_length_store (state after : State) (header : Nat) (cell : Allocation)
    (length : Nat) (initial : state.valid = true) (found : state.heap.lookup header = some cell)
    (typed : cell.type = allocationType)
    (stored : store state (.pointer (.pointer true false usize) ⟨header, lengthOffset⟩) (.scalar (.int false 64 length)) = .ok after) :
    readField after ⟨header, 0⟩ capacityOffset = readField state ⟨header, 0⟩ capacityOffset :=
  readCapacity_after_length_store_at state after ⟨header, 0⟩ length
    (root_fieldPointer state header cell allocationType usize ⟨24, 8⟩ capacityOffset false false
      initial found typed layout_checked (by decide) field_types_checked.2) stored

/-- The actual declared backing establishes usize safety for addOne's length
increment. No independent arithmetic-overflow or successful-allocation premise
is introduced for a ready array with spare capacity. -/
theorem nextLength_bounded (state : State) (lifetime capacity length : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (spare : length < capacity) :
    nextLength length < addressLimit := by
  obtain ⟨_, positive, layout, shaped, _, bounded, limit⟩ := valid_lookup state lifetime cell initial found
  have arrayShape : cell.type.layout = some ⟨capacity * 32, 8⟩ := by
    simp only [typed, Ty.layout, Expression.layout_checked, bind, Option.bind]
  cases Option.some.inj (shaped.symm.trans arrayShape)
  dsimp only at bounded
  simp only [nextLength]
  omega

/-- Shared native selector for a newly appended row and subsequent last-row
cleanup. Initial live array geometry derives pointer arithmetic and the complete
Expression view; the index remains usize and is never truncated to a NodeId. -/
theorem selectNewElement_from_array (state : State) (header : Address) (lifetime capacity length : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = .array capacity Expression.allocationType) (writable : cell.writable = true)
    (inside : length < capacity)
    (loaded : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ (nextLength length))) :
    selectNewElement state header (nextLength length) = .ok ⟨lifetime, length * 32⟩ := by
  have bounded := nextLength_bounded state lifetime capacity length cell initial found typed inside
  have element := element_pointer state lifetime capacity length cell initial found typed writable inside
  have pointed : sliceElementPointer state (.slice itemsType ⟨lifetime, 0⟩ (nextLength length)) (selectedIndex (nextLength length)) =
      .ok (.pointer (.pointer true false elementType) ⟨lifetime, length * 32⟩) := by
    have width : ¬length + 1 ≥ addressLimit := by simp only [nextLength] at bounded; omega
    simp only [sliceElementPointer, itemsType, selectedIndex, nextLength, Nat.add_sub_cancel,
      if_neg width, if_pos (by omega : length < length + 1), element]
  have resolved := element_record_view state lifetime capacity length cell initial found typed writable inside
  simp only [selectNewElement, loaded, bind, Except.bind, pointed, resolved, ne_self_iff_false,
    Nat.mul_mod_left, or_self, ↓reduceIte]

theorem readHeader_from_parts (state : State) (header : Address) (items capacity : Value)
    (itemsRead : readItems state header = .ok items) (capacityRead : readField state header capacityOffset = .ok capacity) :
    readHeader state header = .ok (items, capacity) := by
  simp only [readHeader, itemsRead, capacityRead, bind, Except.bind]

theorem readHeader_parts (state : State) (header : Address) (items capacity : Value)
    (loaded : readHeader state header = .ok (items, capacity)) :
    readItems state header = .ok items ∧ readField state header capacityOffset = .ok capacity := by
  cases first : readItems state header with
  | error fault => simp [readHeader, first, bind, Except.bind] at loaded
  | ok actualItems =>
    cases second : readField state header capacityOffset with
    | error fault => simp [readHeader, first, second, bind, Except.bind] at loaded
    | ok actualCapacity =>
      simp only [readHeader, first, second, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at loaded
      exact ⟨congrArg Except.ok loaded.1, congrArg Except.ok loaded.2⟩

/-- Applied source equations keep the composition at the same reached states.
This helper supplies no capacity, pointer, store or initialization guarantee. -/
theorem append_of_steps (state ready after : State) (header : Address) (lifetime capacity length : Nat)
    (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (loaded : readHeader state header = .ok (.slice itemsType ⟨lifetime, 0⟩ length, .scalar (.int false 64 capacity)))
    (enough : hasCapacity capacity (nextLength length) = true)
    (written : writeLength state header (nextLength length) = .ok ready)
    (selected : selectNewElement ready header (nextLength length) = .ok ⟨lifetime, length * 32⟩)
    (initialized : initializeFields ready lifetime length itemAddress argumentsAddress argumentsLength id sequence = .ok after) :
    appendWithoutGrowth state header itemAddress argumentsAddress argumentsLength id sequence = .ok after := by
  simp only [appendWithoutGrowth, loaded, bind, Except.bind, ne_self_iff_false, ↓reduceIte,
    Int.toNat_natCast, enough, Bool.not_true, Bool.false_eq_true, written, selected,
    Nat.mul_div_cancel _ (by decide : 0 < 32), initialized]

/-- Shared proof for the continuation of the same reached length store. Public
standalone and captured-owner endpoints derive the store and selectors from
initial geometry; they share all element selection, initialization and frames. -/
theorem append_at_framed (state ready : State) (header : Address) (lifetime capacity length : Nat)
    (backing : Allocation) (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (initial : state.valid = true)
    (backingFound : state.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (itemsRead : readItems state header = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (capacityRead : readField state header capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : length < capacity) (argumentsValid : argumentsLength < addressLimit)
    (idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains id = true)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true)
    (apart : header.allocation ≠ lifetime)
    (selectedItems : fieldPointer state (.pointer (.pointer false false allocationType) header) itemsOffset =
      .ok (.pointer (.pointer false false itemsType) ⟨header.allocation, header.offset + itemsOffset⟩))
    (selectedCapacity : fieldPointer state (.pointer (.pointer false false allocationType) header) capacityOffset =
      .ok (.pointer (.pointer false false usize) ⟨header.allocation, header.offset + capacityOffset⟩))
    (written : writeLength state header (nextLength length) = .ok ready)
    (storedLength : store state (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + lengthOffset⟩)
      (.scalar (.int false 64 (nextLength length))) = .ok ready) :
    ∃ after, appendWithoutGrowth state header itemAddress argumentsAddress argumentsLength id sequence = .ok after ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after header = .ok (.slice itemsType ⟨lifetime, 0⟩ (nextLength length), .scalar (.int false 64 capacity)) ∧
      Expression.readFields after false ⟨lifetime, length * 32⟩ = .ok [.pointer Expression.itemType itemAddress,
        .slice Expression.argumentsType argumentsAddress argumentsLength, .scalar (.int false 32 id), .scalar (.int false 32 sequence)] ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ other, other ≠ header.allocation → other ≠ lifetime → after.heap.lookup other = state.heap.lookup other) ∧
      after.heap.lookup header.allocation = ready.heap.lookup header.allocation := by
  have validReady := store_preserves_valid _ _ _ _ initial storedLength
  have shapeReady := store_retains_shape _ _ _ _ storedLength
  obtain ⟨readyBacking, readyFound, readyShape⟩ := shapeReady lifetime backing backingFound
  have readyTyped := readyShape.2.1.trans backingTyped
  have readyWritable := readyShape.2.2.1.trans backingWritable
  have reloaded := readItems_after_length_store_at state ready header ⟨lifetime, 0⟩ length (nextLength length)
    selectedItems itemsRead storedLength
  have capacityReady := (readCapacity_after_length_store_at state ready header (nextLength length)
    selectedCapacity storedLength).trans capacityRead
  have selected := selectNewElement_from_array ready header lifetime capacity length readyBacking
    validReady readyFound readyTyped readyWritable spare reloaded
  obtain ⟨withItem, withArguments, withId, after, storedItem, storedArguments, storedId, storedSequence⟩ :=
    initializeFields_stores ready lifetime capacity length readyBacking itemAddress argumentsAddress argumentsLength id sequence
      validReady readyFound readyTyped readyWritable spare argumentsValid idValid sequenceValid
  have initialized := initializeFields_of_stores ready withItem withArguments withId after lifetime length itemAddress argumentsAddress
    argumentsLength id sequence storedItem storedArguments storedId storedSequence
  have itemsFrame := (readItems_after_other_store _ _ _ _ header _ storedSequence apart).trans
    ((readItems_after_other_store _ _ _ _ header _ storedId apart).trans
      ((readItems_after_other_store _ _ _ _ header _ storedArguments apart).trans
        (readItems_after_other_store _ _ _ _ header _ storedItem apart)))
  have capacityFrame := (readField_after_other_store _ _ _ _ header capacityOffset _ storedSequence apart).trans
    ((readField_after_other_store _ _ _ _ header capacityOffset _ storedId apart).trans
      ((readField_after_other_store _ _ _ _ header capacityOffset _ storedArguments apart).trans
        (readField_after_other_store _ _ _ _ header capacityOffset _ storedItem apart)))
  refine ⟨after, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact append_of_steps state ready after header lifetime capacity length itemAddress argumentsAddress argumentsLength id sequence
      (readHeader_from_parts state header _ _ itemsRead capacityRead)
      (by simp [hasCapacity, nextLength]; omega) written selected initialized
  · exact store_preserves_valid _ _ _ _ (store_preserves_valid _ _ _ _
      (store_preserves_valid _ _ _ _ (store_preserves_valid _ _ _ _ validReady storedItem) storedArguments) storedId) storedSequence
  · exact shapeReady.trans ((store_retains_shape _ _ _ _ storedItem).trans ((store_retains_shape _ _ _ _ storedArguments).trans
      ((store_retains_shape _ _ _ _ storedId).trans (store_retains_shape _ _ _ _ storedSequence))))
  · exact readHeader_from_parts after header _ _ (itemsFrame.trans reloaded) (capacityFrame.trans capacityReady)
  · exact fields_after_array_stores ready withItem withArguments withId after lifetime capacity length readyBacking
      itemAddress argumentsAddress argumentsLength id sequence validReady readyFound readyTyped readyWritable spare
      storedItem storedArguments storedId storedSequence
  · exact (store_keeps_counters _ _ _ _ storedSequence).1.trans ((store_keeps_counters _ _ _ _ storedId).1.trans
      ((store_keeps_counters _ _ _ _ storedArguments).1.trans ((store_keeps_counters _ _ _ _ storedItem).1.trans
        (store_keeps_counters _ _ _ _ storedLength).1)))
  · exact (store_keeps_counters _ _ _ _ storedSequence).2.trans ((store_keeps_counters _ _ _ _ storedId).2.trans
      ((store_keeps_counters _ _ _ _ storedArguments).2.trans ((store_keeps_counters _ _ _ _ storedItem).2.trans
        (store_keeps_counters _ _ _ _ storedLength).2)))
  · intro other outsideHeader outsideBacking
    exact (heap_after_store_other _ _ _ _ _ _ _ storedSequence other outsideBacking).trans
      ((heap_after_store_other _ _ _ _ _ _ _ storedId other outsideBacking).trans
        ((heap_after_store_other _ _ _ _ _ _ _ storedArguments other outsideBacking).trans
          ((heap_after_store_other _ _ _ _ _ _ _ storedItem other outsideBacking).trans
            (heap_after_store_other _ _ _ _ _ _ _ storedLength other outsideHeader))))

  · exact (heap_after_store_other _ _ _ _ _ _ _ storedSequence header.allocation apart).trans
      ((heap_after_store_other _ _ _ _ _ _ _ storedId header.allocation apart).trans
        ((heap_after_store_other _ _ _ _ _ _ _ storedArguments header.allocation apart).trans
          (heap_after_store_other _ _ _ _ _ _ _ storedItem header.allocation apart)))

/-- An admitted finite append with spare capacity executes in the same heap,
updates only the header length, initializes the new slot and derives complete
readonly fields. The initial header/backing mapping and valid evaluated values
are compiler preconditions; native growth, payload ownership and publication
are not conclusions or assumptions hidden in this scope. -/
theorem appendWithoutGrowth_framed (state : State) (header lifetime capacity length : Nat)
    (headerCell backing : Allocation) (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (initial : state.valid = true)
    (headerFound : state.heap.lookup header = some headerCell) (headerTyped : headerCell.type = allocationType)
    (headerWritable : headerCell.writable = true)
    (backingFound : state.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (itemsRead : readItems state ⟨header, 0⟩ = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (capacityRead : readField state ⟨header, 0⟩ capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : length < capacity) (argumentsValid : argumentsLength < addressLimit)
    (idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains id = true)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true) :
    ∃ after, appendWithoutGrowth state ⟨header, 0⟩ itemAddress argumentsAddress argumentsLength id sequence = .ok after ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after ⟨header, 0⟩ = .ok (.slice itemsType ⟨lifetime, 0⟩ (nextLength length), .scalar (.int false 64 capacity)) ∧
      Expression.readFields after false ⟨lifetime, length * 32⟩ = .ok [.pointer Expression.itemType itemAddress,
        .slice Expression.argumentsType argumentsAddress argumentsLength, .scalar (.int false 32 id), .scalar (.int false 32 sequence)] ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ other, other ≠ header → other ≠ lifetime → after.heap.lookup other = state.heap.lookup other) := by
  have apart : header ≠ lifetime := by
    apply state.heap.lookup_ne_of_type_ne header lifetime headerCell backing headerFound backingFound
    rw [headerTyped, backingTyped]
    intro impossible
    cases impossible
  have bounded := nextLength_bounded state lifetime capacity length backing initial backingFound backingTyped spare
  obtain ⟨ready, written, storedLength⟩ := length_store_total state header headerCell (nextLength length)
    initial headerFound headerTyped headerWritable bounded
  obtain ⟨after, ran, valid, shape, header, fields, nextId, nextAddress, frame, _⟩ :=
    append_at_framed state ready ⟨header, 0⟩ lifetime capacity length backing itemAddress argumentsAddress
    argumentsLength id sequence initial backingFound backingTyped backingWritable itemsRead capacityRead spare
    argumentsValid idValid sequenceValid apart
    (root_fieldPointer state header headerCell allocationType itemsType ⟨24, 8⟩ itemsOffset false false
      initial headerFound headerTyped layout_checked (by decide) field_types_checked.1)
    (root_fieldPointer state header headerCell allocationType usize ⟨24, 8⟩ capacityOffset false false
      initial headerFound headerTyped layout_checked (by decide) field_types_checked.2) written storedLength

  exact ⟨after, ran, valid, shape, header, fields, nextId, nextAddress, frame⟩

/-- Preserve the original append interface through the stronger same-execution
frame proof. Successful stores and final correctness remain conclusions. -/
theorem appendWithoutGrowth_verified (state : State) (header lifetime capacity length : Nat)
    (headerCell backing : Allocation) (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (initial : state.valid = true)
    (headerFound : state.heap.lookup header = some headerCell) (headerTyped : headerCell.type = allocationType)
    (headerWritable : headerCell.writable = true)
    (backingFound : state.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (itemsRead : readItems state ⟨header, 0⟩ = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (capacityRead : readField state ⟨header, 0⟩ capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : length < capacity) (argumentsValid : argumentsLength < addressLimit)
    (idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains id = true)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true) :
    ∃ after, appendWithoutGrowth state ⟨header, 0⟩ itemAddress argumentsAddress argumentsLength id sequence = .ok after ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after ⟨header, 0⟩ = .ok (.slice itemsType ⟨lifetime, 0⟩ (nextLength length), .scalar (.int false 64 capacity)) ∧
      Expression.readFields after false ⟨lifetime, length * 32⟩ = .ok [.pointer Expression.itemType itemAddress,
        .slice Expression.argumentsType argumentsAddress argumentsLength, .scalar (.int false 32 id), .scalar (.int false 32 sequence)] := by
  obtain ⟨after, executed, valid, shape, loaded, fields, _⟩ := appendWithoutGrowth_framed state header lifetime capacity length
    headerCell backing itemAddress argumentsAddress argumentsLength id sequence initial headerFound headerTyped headerWritable
    backingFound backingTyped backingWritable itemsRead capacityRead spare argumentsValid idValid sequenceValid
  exact ⟨after, executed, valid, shape, loaded, fields⟩

/-- Lookup of the appended ID uses the source bounds/index program and the
actual updated header. Successful final selection, descriptor initialization and
field observations are conclusions. Initial native mapping remains required. -/
theorem representativeFields_after_append (state : State) (header lifetime capacity : Nat)
    (headerCell backing : Allocation) (id : NodeId) (sequence : BitVec 32)
    (itemAddress argumentsAddress : Address) (argumentsLength : Nat)
    (initial : state.valid = true)
    (headerFound : state.heap.lookup header = some headerCell) (headerTyped : headerCell.type = allocationType)
    (headerWritable : headerCell.writable = true)
    (backingFound : state.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (itemsRead : readItems state ⟨header, 0⟩ = .ok (.slice itemsType ⟨lifetime, 0⟩ id.toNat))
    (capacityRead : readField state ⟨header, 0⟩ capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : id.toNat < capacity) (argumentsValid : argumentsLength < addressLimit) :
    ∃ after, appendWithoutGrowth state ⟨header, 0⟩ itemAddress argumentsAddress argumentsLength id.toNat sequence.toNat = .ok after ∧
      representativeFields after ⟨header, 0⟩ id = .ok (.ok [.pointer Expression.itemType itemAddress,
        .slice Expression.argumentsType argumentsAddress argumentsLength,
        .scalar (.int false 32 id.toNat), .scalar (.int false 32 sequence.toNat)]) := by
  obtain ⟨after, executed, valid, shape, headerRead, fields⟩ := appendWithoutGrowth_verified state header lifetime capacity id.toNat
    headerCell backing itemAddress argumentsAddress argumentsLength id.toNat sequence.toNat initial headerFound headerTyped headerWritable
    backingFound backingTyped backingWritable itemsRead capacityRead spare argumentsValid (WordArray.number_valid id) (WordArray.number_valid sequence)
  obtain ⟨updated, lookup, retained⟩ := shape lifetime backing backingFound
  have pointer := representative_from_array after ⟨header, 0⟩ lifetime capacity (nextLength id.toNat) updated id valid
    (readHeader_parts after ⟨header, 0⟩ _ _ headerRead).1 lookup (retained.2.1.trans backingTyped)
    (retained.2.2.1.trans backingWritable) (by simp only [nextLength]; omega) (by simp [nextLength])
  refine ⟨after, executed, ?_⟩
  simp only [representativeFields, pointer, bind, Except.bind, ne_self_iff_false, ↓reduceIte, fields, pure, Except.pure]

end Compiler.Extraction.RepresentativeArray.Append
