/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeGrowingAppend

namespace Compiler.Extraction.RepresentativeArray.Append.Execution
open Compiler.ZigAir.Memory

theorem selected_descriptor_parent (state : State) (header address : Address) (newLength : Nat)
    (selected : selectNewElement state header newLength = .ok address) :
    ∃ layout cell, access state address layout false = .ok cell ∧ acceptsView cell.type address.offset Expression.allocationType = true := by
  cases loaded : readItems state header with
  | error fault => simp [selectNewElement, loaded, bind, Except.bind] at selected
  | ok view =>
    cases pointed : sliceElementPointer state view (selectedIndex newLength) with
    | error fault => simp [selectNewElement, loaded, pointed, bind, Except.bind] at selected
    | ok element =>
      cases resolved : recordView state Expression.allocationType element with
      | error fault => simp [selectNewElement, loaded, pointed, resolved, bind, Except.bind] at selected
      | ok complete =>
        cases complete with
        | pointer target actual =>
          simp only [selectNewElement, loaded, pointed, resolved, bind, Except.bind] at selected
          split at selected
          · contradiction
          · rename_i permitted
            have typed : target = .pointer true false Expression.allocationType := (not_or.mp permitted).1 |> Decidable.of_not_not
            subst target
            have same := Except.ok.inj selected
            subst address
            obtain ⟨layout, cell, _, accessed, declared⟩ := recordView_result_parent state Expression.allocationType element true false actual resolved
            exact ⟨layout, cell, accessed, declared⟩
        | _ => simp [selectNewElement, loaded, pointed, resolved, bind, Except.bind] at selected

theorem word_array_has_no_descriptor (extent offset : Nat) :
    acceptsView (.array extent WordArray.word) offset Expression.allocationType = false := by
  simp [acceptsView, WordArray.word, Expression.allocationType]

/-- A selected complete descriptor cannot inhabit an allocation whose complete
declaration contains no descriptor subobject.
Separation is derived from the same selector, not supplied as a write premise. -/
theorem finish_allocation_frame (state : State) (header : Address) (newLength : Nat) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (lifetime : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell) (noDescriptor : ∀ offset, acceptsView cell.type offset Expression.allocationType = false) :
    (finish state header newLength itemAddress argumentsAddress argumentsLength id sequence).2.heap.lookup lifetime = some cell := by
  unfold finish
  cases selected : selectNewElement state header newLength with
  | error fault => exact found
  | ok address =>
    have separate : lifetime ≠ address.allocation := by
      intro same
      obtain ⟨layout, owner, accessed, declared⟩ := selected_descriptor_parent state header address newLength selected
      have ownerFound := (access_success_region state address layout false owner accessed).1
      rw [← same, found] at ownerFound
      cases Option.some.inj ownerFound
      rw [noDescriptor] at declared
      contradiction
    have frame := (writeFields_storage (descriptorFields itemAddress argumentsAddress argumentsLength id sequence)
      state address.allocation (address.offset / 32) initial).2.2.2.2 lifetime separate
    exact frame.trans found

/-- Rejected slot selection or partial descriptor assignment still preserves
an independently declared allocation. Only the header needs a distinct
lifetime; descriptor separation follows the checked declaration. -/
theorem assumeCapacity_allocation_frame (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (lifetime : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell) (noDescriptor : ∀ offset, acceptsView cell.type offset Expression.allocationType = false)
    (separate : lifetime ≠ header.allocation) :
    (assumeCapacity state header itemAddress argumentsAddress argumentsLength id sequence).2.heap.lookup lifetime = some cell := by
  unfold assumeCapacity
  split
  · exact found
  · rename_i length lengthRead
    split
    · exact found
    · dsimp only
      split
      · exact found
      · split
        · exact found
        · rename_i ready written
          have stored := length_write_is_store state ready header _ written
          have readyFound := (heap_after_store_other _ _ _ _ _ _ _ stored lifetime separate).trans found
          exact finish_allocation_frame ready header (nextLength length.toNat) itemAddress argumentsAddress argumentsLength id sequence
            lifetime cell (store_preserves_valid _ _ _ _ initial stored) readyFound noDescriptor
    · exact found
  · exact found

/-- Appending into a checked live slot cannot revive a released lifetime. -/
theorem finish_missing (state : State) (header : Address) (newLength : Nat) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (lifetime : Nat) (initial : state.valid = true)
    (missing : state.heap.lookup lifetime = none) :
    (finish state header newLength itemAddress argumentsAddress argumentsLength id sequence).2.heap.lookup lifetime = none := by
  unfold finish
  cases selected : selectNewElement state header newLength with
  | error fault => exact missing
  | ok address =>
    obtain ⟨layout, owner, accessed, _⟩ := selected_descriptor_parent state header address newLength selected
    have found := (access_success_region state address layout false owner accessed).1
    have apart : lifetime ≠ address.allocation := by intro same; rw [← same, missing] at found; contradiction
    exact ((writeFields_storage (descriptorFields itemAddress argumentsAddress argumentsLength id sequence)
      state address.allocation (address.offset / 32) initial).2.2.2.2 lifetime apart).trans missing

theorem assumeCapacity_missing (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (lifetime : Nat) (initial : state.valid = true)
    (missing : state.heap.lookup lifetime = none) :
    (assumeCapacity state header itemAddress argumentsAddress argumentsLength id sequence).2.heap.lookup lifetime = none := by
  unfold assumeCapacity
  split
  · exact missing
  · rename_i length lengthRead
    split
    · exact missing
    · dsimp only
      split
      · exact missing
      · split
        · exact missing
        · rename_i ready written
          have stored := length_write_is_store state ready header _ written
          exact finish_missing ready header (nextLength length.toNat) itemAddress argumentsAddress argumentsLength id sequence lifetime
            (store_preserves_valid _ _ _ _ initial stored) (store_keeps_missing _ _ _ _ lifetime stored missing)
    · exact missing
  · exact missing

/-- Allocation OOM, checked growth rejection and later append rejection keep
all live independent descriptor-free storage, with the reached allocator effects intact. -/
theorem run_allocation_frame (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (allocate : RegionAllocation.Allocator σ) (effects : σ)
    (lifetime : Nat) (cell : Allocation) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (noDescriptor : ∀ offset, acceptsView cell.type offset Expression.allocationType = false)
    (separate : lifetime ≠ header.allocation) :
    (run state header itemAddress argumentsAddress argumentsLength id sequence allocate effects).1.2.heap.lookup lifetime = some cell := by
  have older := (valid_lookup state lifetime cell initial found).1
  unfold run runWithCapacity
  split
  · exact found
  · rename_i length lengthRead
    dsimp only
    split
    · exact found
    · have capacityFacts := Capacity.ensure_storage state header (nextLength length.toNat) allocate effects initial
      have readyFound := (capacityFacts.2 lifetime separate (by omega)).trans found
      generalize resolved : Capacity.ensure state header (nextLength length.toNat) allocate effects = outcome at *
      rcases outcome with ⟨⟨result, ready⟩, reached⟩
      cases result with
      | error fault => exact readyFound
      | ok value =>
        cases value with
        | none => exact readyFound
        | some value =>
          cases value
          have framed := assumeCapacity_allocation_frame ready header itemAddress argumentsAddress argumentsLength id sequence
            lifetime cell capacityFacts.1 readyFound noDescriptor separate
          generalize assigned : assumeCapacity ready header itemAddress argumentsAddress argumentsLength id sequence = outcome at *
          rcases outcome with ⟨result, after⟩
          cases result <;> exact framed
  · exact found

/-- Word storage is one instance of the common complete-allocation frame. -/
theorem finish_word_frame (state : State) (header : Address) (newLength : Nat) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (lifetime extent : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell) (typed : cell.type = .array extent WordArray.word) :
    (finish state header newLength itemAddress argumentsAddress argumentsLength id sequence).2.heap.lookup lifetime = some cell :=
  finish_allocation_frame state header newLength itemAddress argumentsAddress argumentsLength id sequence lifetime cell initial found
    (fun offset => typed.symm ▸ word_array_has_no_descriptor extent offset)

theorem assumeCapacity_word_frame (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (lifetime extent : Nat) (cell : Allocation)
    (initial : state.valid = true) (found : state.heap.lookup lifetime = some cell) (typed : cell.type = .array extent WordArray.word)
    (separate : lifetime ≠ header.allocation) :
    (assumeCapacity state header itemAddress argumentsAddress argumentsLength id sequence).2.heap.lookup lifetime = some cell :=
  assumeCapacity_allocation_frame state header itemAddress argumentsAddress argumentsLength id sequence lifetime cell initial found
    (fun offset => typed.symm ▸ word_array_has_no_descriptor extent offset) separate

theorem run_word_frame (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (allocate : RegionAllocation.Allocator σ) (effects : σ)
    (lifetime extent : Nat) (cell : Allocation) (initial : state.valid = true)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = .array extent WordArray.word)
    (separate : lifetime ≠ header.allocation) :
    (run state header itemAddress argumentsAddress argumentsLength id sequence allocate effects).1.2.heap.lookup lifetime = some cell :=
  run_allocation_frame state header itemAddress argumentsAddress argumentsLength id sequence allocate effects lifetime cell initial found
    (fun offset => typed.symm ▸ word_array_has_no_descriptor extent offset) separate

/-- Every complete owner-append outcome preserves the same parent allocation,
all its bytes as modeled leaves, metadata and offset-view observations. -/
theorem owner_parent_borrow (runtimeSafety : Bool) (state : State) (owner : Nat) (ownerCell : Allocation)
    (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (allocate : RegionAllocation.Allocator σ) (effects : σ)
    (parent : WordArray.View) (values : List (BitVec 32)) (extent : Nat) (parentCell : Allocation)
    (initial : state.valid = true) (ownerFound : state.heap.lookup owner = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (parentFound : state.heap.lookup parent.allocation = some parentCell) (parentTyped : parentCell.type = .array extent WordArray.word)
    (represented : WordArray.Represents state parent values) :
    let after := (ownerRun runtimeSafety state ⟨owner, 0⟩ itemAddress argumentsAddress argumentsLength id sequence allocate effects).1.2
    after.valid = true ∧ after.heap.lookup parent.allocation = some parentCell ∧ WordArray.Represents after parent values ∧
      (∀ writable many type offset, load after (.pointer (.pointer writable many type) ⟨parent.allocation, offset⟩) =
        load state (.pointer (.pointer writable many type) ⟨parent.allocation, offset⟩)) := by
  have separate := state.heap.lookup_ne_of_type_ne parent.allocation owner parentCell ownerCell parentFound ownerFound
    (by simp [parentTyped, ownerTyped, Owner.viewType, WordArray.word])
  have selected := Owner.root_header_pointer runtimeSafety state owner ownerCell true initial ownerFound ownerTyped
  simp only [ownerRun, ownerWithCapacity, selected]
  have framed := run_word_frame state (Owner.headerAddress ⟨owner, 0⟩) itemAddress argumentsAddress argumentsLength id sequence
    allocate effects parent.allocation extent parentCell initial parentFound parentTyped separate
  have same := framed.trans parentFound.symm
  refine ⟨run_valid state _ itemAddress argumentsAddress argumentsLength id sequence allocate effects initial, framed, ?_, ?_⟩
  · exact ⟨represented.1, fun index inside => (load_eq_of_lookup state _ true false WordArray.word (parent.address index) same).trans (represented.2 index inside)⟩
  · intro writable many type offset
    exact load_eq_of_lookup state _ writable many type ⟨parent.allocation, offset⟩ same

end Compiler.Extraction.RepresentativeArray.Append.Execution
