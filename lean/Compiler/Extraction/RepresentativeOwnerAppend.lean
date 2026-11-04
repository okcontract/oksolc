/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayAppend
import Compiler.Extraction.RepresentativeOwnerFields
import Compiler.Extraction.RepresentativeOwnerLock
import Compiler.ZigAir.MemoryWordArrayWrites

namespace Compiler.Extraction.RepresentativeArray.Owner
open Compiler.ZigAir.Memory
open Compiler.Algebraic

/-- Select the production owner's embedded representative list before entering
the admitted spare-capacity append. Descriptor inputs have already been evaluated;
this checked execution does not implement growing append or initializer order. -/
def appendWithoutGrowth (runtimeSafety : Bool) (state : State) (owner itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) : Except Fault State := do
  let selected ← fieldPointer state (.pointer (.pointer true false (viewType runtimeSafety)) owner) representativesOffset
  let .pointer _ header := selected | .error .malformed
  Append.appendWithoutGrowth state header itemAddress argumentsAddress argumentsLength id sequence

/-- Derive the length leaf's selector and write from the complete captured owner.
The owning allocation, header offset and lifetime are retained throughout. -/
theorem length_store_total (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation) (length : Nat)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = viewType runtimeSafety) (writable : cell.writable = true) (bounded : length < addressLimit) :
    ∃ after, Append.writeLength state (headerAddress ⟨lifetime, 0⟩) length = .ok after ∧
      store state (.pointer (.pointer true false usize) ⟨lifetime, representativesOffset + Append.lengthOffset⟩)
        (.scalar (.int false 64 length)) = .ok after := by
  have parent := root_access state lifetime cell (layout runtimeSafety) false initial found
    (typed ▸ view_layout_checked runtimeSafety) (by cases runtimeSafety <;> decide) (by simp)
  have header := header_region_access runtimeSafety state ⟨lifetime, 0⟩ cell false parent
  have declared : acceptsView cell.type (headerAddress ⟨lifetime, 0⟩).offset RepresentativeArray.allocationType = true := by
    simpa only [typed, headerAddress, Nat.zero_add] using header_view_checked runtimeSafety
  have selected := fieldPointer_of_access state (headerAddress ⟨lifetime, 0⟩) cell RepresentativeArray.allocationType usize
    representativesLayout Append.lengthOffset true false header_layout_checked header declared Append.length_type_checked
  have writeHeader := access_read_write state (headerAddress ⟨lifetime, 0⟩) representativesLayout cell header writable
  have accessed := access_subregion state (headerAddress ⟨lifetime, 0⟩) representativesLayout ⟨8, 8⟩ Append.lengthOffset
    true cell writeHeader (by decide) (by decide) (by decide) (by decide)
  obtain ⟨after, stored⟩ := store_subobject_total state ⟨lifetime, representativesOffset + Append.lengthOffset⟩ ⟨8, 8⟩ cell
    (.scalar (.int false 64 length)) (Value.usize_valid length bounded) rfl accessed
    (by rw [typed]; simp only [Value.type, Compiler.ZigAir.Scalar.Value.type]; cases runtimeSafety <;> decide)
    (by intro entry member
        simp only [Value.leaves, List.mem_cons, List.not_mem_nil, or_false] at member
        subst entry
        simpa only [Nat.add_zero, Value.type, Compiler.ZigAir.Scalar.Value.type, typed, Append.lengthOffset]
          using (header_leaf_types_checked runtimeSafety).2.1)
  change store state (.pointer (.pointer true false usize) ⟨lifetime, representativesOffset + Append.lengthOffset⟩)
    (.scalar (.int false 64 length)) = .ok after at stored
  have location : headerAddress ⟨lifetime, 0⟩ = ⟨lifetime, representativesOffset⟩ := rfl
  rw [location] at selected ⊢
  refine ⟨after, ?_, stored⟩
  simp only [Append.writeLength, selected, bind, Except.bind, stored]

/-- The actual captured owner supplies the header location and writable length
leaf. Backing geometry and evaluated fields derive the remaining stores through
the same proof used by standalone append. Final fields and frames are conclusions. -/
theorem appendWithoutGrowth_framed (runtimeSafety : Bool) (state : State) (owner lifetime capacity length : Nat)
    (ownerCell backing : Allocation) (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (initial : state.valid = true)
    (ownerFound : state.heap.lookup owner = some ownerCell) (ownerTyped : ownerCell.type = viewType runtimeSafety)
    (ownerWritable : ownerCell.writable = true)
    (backingFound : state.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (itemsRead : readItems state (headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (capacityRead : readField state (headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : length < capacity) (argumentsValid : argumentsLength < addressLimit)
    (idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains id = true)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true) :
    ∃ after, appendWithoutGrowth runtimeSafety state ⟨owner, 0⟩ itemAddress argumentsAddress argumentsLength id sequence = .ok after ∧
      after.valid = true ∧ state.heap.RetainsShape after.heap ∧
      readHeader after (headerAddress ⟨owner, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ (Append.nextLength length), .scalar (.int false 64 capacity)) ∧
      Expression.readFields after false ⟨lifetime, length * 32⟩ = .ok [.pointer Expression.itemType itemAddress,
        .slice Expression.argumentsType argumentsAddress argumentsLength, .scalar (.int false 32 id), .scalar (.int false 32 sequence)] ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ other, other ≠ owner → other ≠ lifetime → after.heap.lookup other = state.heap.lookup other) ∧
      NativeLock.checkHeader after (headerAddress ⟨owner, 0⟩) =
        NativeLock.checkHeader state (headerAddress ⟨owner, 0⟩) := by
  have location : headerAddress ⟨owner, 0⟩ = ⟨owner, representativesOffset⟩ := rfl
  rw [location] at itemsRead capacityRead ⊢
  have apart : owner ≠ lifetime := state.heap.lookup_ne_of_type_ne owner lifetime ownerCell backing ownerFound backingFound
    (by simp [ownerTyped, backingTyped, viewType])
  have bounded := Append.nextLength_bounded state lifetime capacity length backing initial backingFound backingTyped spare
  obtain ⟨ready, written, stored⟩ := length_store_total runtimeSafety state owner ownerCell (Append.nextLength length)
    initial ownerFound ownerTyped ownerWritable bounded
  rw [location] at written
  have selectors := root_header_fields runtimeSafety state owner ownerCell false initial ownerFound ownerTyped
  rw [location] at selectors
  obtain ⟨after, executed, validAfter, shapeAfter, header, fields, nextId, nextAddress, frame, ownerFrame⟩ := Append.append_at_framed state ready ⟨owner, representativesOffset⟩ lifetime capacity length
    backing itemAddress argumentsAddress argumentsLength id sequence initial backingFound backingTyped backingWritable
    itemsRead capacityRead spare argumentsValid idValid sequenceValid apart selectors.1 selectors.2 written stored
  have selected := root_header_pointer runtimeSafety state owner ownerCell true initial ownerFound ownerTyped
  rw [location] at selected
  obtain ⟨readyOwner, readyFound, readyShape⟩ := (store_retains_shape _ _ _ _ stored) owner ownerCell ownerFound
  have lock := NativeLock.checkHeader_eq_of_lookup runtimeSafety ready after owner readyOwner validAfter
    readyFound (readyShape.2.1.trans ownerTyped) ownerFrame
  refine ⟨after, ?_, validAfter, shapeAfter, header, fields, nextId, nextAddress, frame, ?_⟩
  · simpa only [appendWithoutGrowth, selected, bind, Except.bind] using executed
  · exact lock.trans (NativeLock.checkHeader_after_length_store runtimeSafety state ready owner
      (Append.nextLength length) ownerCell initial ownerFound ownerTyped stored)

/-- A represented parent word allocation is independent of both the owner and
descriptor array by their declared types. Its complete allocation and every
typed read survive this same append; stack/readonly metadata are included. -/
theorem append_parent_borrow (runtimeSafety : Bool) (state : State) (owner lifetime capacity length : Nat)
    (ownerCell backing : Allocation) (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (parentView : WordArray.View) (values : List NodeId) (extent : Nat) (parentCell : Allocation)
    (initial : state.valid = true)
    (ownerFound : state.heap.lookup owner = some ownerCell) (ownerTyped : ownerCell.type = viewType runtimeSafety)
    (ownerWritable : ownerCell.writable = true)
    (backingFound : state.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (itemsRead : readItems state (headerAddress ⟨owner, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ length))
    (capacityRead : readField state (headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (spare : length < capacity) (argumentsValid : argumentsLength < addressLimit)
    (idValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains id = true)
    (sequenceValid : (Compiler.ZigAir.Scalar.Ty.int false 32).contains sequence = true)
    (parentFound : state.heap.lookup parentView.allocation = some parentCell) (parentTyped : parentCell.type = .array extent WordArray.word)
    (represented : WordArray.Represents state parentView values) :
    ∃ after, appendWithoutGrowth runtimeSafety state ⟨owner, 0⟩ itemAddress argumentsAddress argumentsLength id sequence = .ok after ∧
      after.valid = true ∧ after.heap.lookup parentView.allocation = some parentCell ∧ WordArray.Represents after parentView values ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      (∀ writable many type offset, load after (.pointer (.pointer writable many type) ⟨parentView.allocation, offset⟩) =
        load state (.pointer (.pointer writable many type) ⟨parentView.allocation, offset⟩)) := by
  have outsideOwner := state.heap.lookup_ne_of_type_ne parentView.allocation owner parentCell ownerCell parentFound ownerFound
    (by simp [parentTyped, ownerTyped, viewType, WordArray.word])
  have outsideBacking := state.heap.lookup_ne_of_type_ne parentView.allocation lifetime parentCell backing parentFound backingFound
    (by simp [parentTyped, backingTyped, Expression.allocationType, WordArray.word])
  obtain ⟨after, executed, valid, _, _, _, nextId, nextAddress, frame, _⟩ := appendWithoutGrowth_framed runtimeSafety state
    owner lifetime capacity length ownerCell backing itemAddress argumentsAddress argumentsLength id sequence initial
    ownerFound ownerTyped ownerWritable backingFound backingTyped backingWritable itemsRead capacityRead spare argumentsValid idValid sequenceValid
  have same := frame parentView.allocation outsideOwner outsideBacking
  refine ⟨after, executed, valid, same.trans parentFound, ?_, nextId, nextAddress, ?_⟩
  · exact ⟨represented.1, fun index inside =>
      (load_eq_of_lookup state after true false WordArray.word (parentView.address index) same).trans (represented.2 index inside)⟩
  · intro writable many type offset
    exact load_eq_of_lookup state after writable many type ⟨parentView.allocation, offset⟩ same

end Compiler.Extraction.RepresentativeArray.Owner
