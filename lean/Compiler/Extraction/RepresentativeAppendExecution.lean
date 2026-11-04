/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayCapacity
import Compiler.Extraction.RepresentativeOwnerAppend

namespace Compiler.Extraction.RepresentativeArray.Append.Execution
open Compiler.ZigAir.Memory

/-- The shared element selection and descriptor assignment retain every reached
field store. Descriptor inputs are evaluated before entering this operation. -/
def finish (state : State) (header : Address) (newLength : Nat) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) : Except Fault Unit × State :=
  match selectNewElement state header newLength with
  | .error fault => (.error fault, state)
  | .ok address => initializeFieldsReached state address.allocation (address.offset / 32)
      itemAddress argumentsAddress argumentsLength id sequence

/-- Follow addOneAssumeCapacity's length/capacity check before its length store.
Unlike the legacy successful-append facade, this path does not pre-read the
slice pointer. A later pointer/descriptor rejection retains that length store. -/
def assumeCapacity (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) : Except Fault Unit × State :=
  match readField state header lengthOffset with
  | .error fault => (.error fault, state)
  | .ok (.scalar (.int false 64 length)) =>
    match readField state header capacityOffset with
    | .error fault => (.error fault, state)
    | .ok (.scalar (.int false 64 capacity)) =>
      let newLength := nextLength length.toNat
      if !hasCapacity capacity.toNat newLength then (.error .unsupported, state) else
      match writeLength state header newLength with
      | .error fault => (.error fault, state)
      | .ok ready => finish ready header newLength itemAddress argumentsAddress argumentsLength id sequence
    | .ok _ => (.error .malformed, state)
  | .ok _ => (.error .malformed, state)

/-- Shared addOne control: evaluate length, call the selected capacity
executor, then run the same length/descriptor stores. The fault injection only
embeds checked memory failures; OOM and every reached state remain distinct. -/
def runWithCapacity (reject : Fault → ε)
    (ensure : State → Address → Nat → σ → (Except ε (Option Unit) × State) × σ) (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (effects : σ) :
    (Except ε (Option Unit) × State) × σ :=
  match readField state header lengthOffset with
  | .error fault => ((.error (reject fault), state), effects)
  | .ok (.scalar (.int false 64 length)) =>
    let newLength := nextLength length.toNat
    if newLength ≥ addressLimit then ((.error (reject .malformed), state), effects) else
    let ((capacity, ready), reached) := ensure state header newLength effects
    match capacity with
    | .error fault => ((.error fault, ready), reached)
    | .ok none => ((.ok none, ready), reached)
    | .ok (some ()) =>
      let (assigned, after) := assumeCapacity ready header itemAddress argumentsAddress argumentsLength id sequence
      match assigned with
      | .error fault => ((.error (reject fault), after), reached)
      | .ok () => ((.ok (some ()), after), reached)
  | .ok _ => ((.error (reject .malformed), state), effects)

/-- Legacy first/spare scope, instantiated at the same capacity call boundary. -/
def run (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (allocate : RegionAllocation.Allocator σ) (effects : σ) :
    (Except Fault (Option Unit) × State) × σ :=
  runWithCapacity (fun fault => fault) (fun state header minimum effects => Capacity.ensure state header minimum allocate effects)
    state header itemAddress argumentsAddress argumentsLength id sequence effects

/-- Resolve the captured owner's actual embedded header before entering the
shared append control. Capacity execution receives that evaluated address. -/
def ownerWithCapacity (reject : Fault → ε)
    (ensure : State → Address → Nat → σ → (Except ε (Option Unit) × State) × σ)
    (runtimeSafety : Bool) (state : State) (owner itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (effects : σ) : (Except ε (Option Unit) × State) × σ :=
  match fieldPointer state (.pointer (.pointer true false (Owner.viewType runtimeSafety)) owner) Owner.representativesOffset with
  | .error fault => ((.error (reject fault), state), effects)
  | .ok (.pointer _ header) => runWithCapacity reject ensure state header itemAddress argumentsAddress argumentsLength id sequence effects
  | .ok _ => ((.error (reject .malformed), state), effects)

/-- The existing native facade uses the same owner selection and control. -/
def ownerRun (runtimeSafety : Bool) (state : State) (owner itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (allocate : RegionAllocation.Allocator σ) (effects : σ) :
    (Except Fault (Option Unit) × State) × σ :=
  ownerWithCapacity (fun fault => fault) (fun state header minimum effects => Capacity.ensure state header minimum allocate effects)
    runtimeSafety state owner itemAddress argumentsAddress argumentsLength id sequence effects

theorem finish_success_iff (state after : State) (header : Address) (newLength : Nat) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) :
    (do let address ← selectNewElement state header newLength
        initializeFields state address.allocation (address.offset / 32) itemAddress argumentsAddress argumentsLength id sequence) = .ok after ↔
      finish state header newLength itemAddress argumentsAddress argumentsLength id sequence = (.ok (), after) := by
  cases selected : selectNewElement state header newLength with
  | error fault => simp [finish, selected, bind, Except.bind]
  | ok address =>
    simpa only [finish, selected, bind, Except.bind] using
      initializeFields_reached_iff state after address.allocation (address.offset / 32) itemAddress argumentsAddress argumentsLength id sequence

/-- The legacy successful-append proof and the reached execution share every
store and element selector. A complete loaded header supplies the legacy
precheck; the separate length read follows the new executor's source order. -/
theorem assumeCapacity_of_spare (state after : State) (header data : Address) (length capacity : Nat)
    (itemAddress argumentsAddress : Address) (argumentsLength : Nat) (id sequence : Int)
    (loaded : readHeader state header = .ok (.slice itemsType data length, .scalar (.int false 64 capacity)))
    (lengthRead : readField state header lengthOffset = .ok (.scalar (.int false 64 length)))
    (executed : appendWithoutGrowth state header itemAddress argumentsAddress argumentsLength id sequence = .ok after) :
    assumeCapacity state header itemAddress argumentsAddress argumentsLength id sequence = (.ok (), after) := by
  have capacityRead := (readHeader_parts state header _ _ loaded).2
  simp only [appendWithoutGrowth, loaded, bind, Except.bind, ne_self_iff_false, ↓reduceIte, Int.toNat_natCast] at executed
  simp only [assumeCapacity, lengthRead, capacityRead, Int.toNat_natCast]
  split at executed
  · contradiction
  · rename_i enough
    rw [if_neg enough]
    cases written : writeLength state header (nextLength length) with
    | error fault => simp [written] at executed
    | ok ready =>
      simp only [written] at executed
      exact (finish_success_iff ready after header (nextLength length) itemAddress argumentsAddress argumentsLength id sequence).mp executed

theorem finish_storage (state : State) (header : Address) (newLength : Nat) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (initial : state.valid = true) :
    (finish state header newLength itemAddress argumentsAddress argumentsLength id sequence).2.valid = true ∧
      state.heap.RetainsShape (finish state header newLength itemAddress argumentsAddress argumentsLength id sequence).2.heap ∧
      (finish state header newLength itemAddress argumentsAddress argumentsLength id sequence).2.nextId = state.nextId ∧
      (finish state header newLength itemAddress argumentsAddress argumentsLength id sequence).2.nextAddress = state.nextAddress := by
  unfold finish
  split
  · exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl⟩
  · rename_i address selected
    have result := writeFields_storage (descriptorFields itemAddress argumentsAddress argumentsLength id sequence)
      state address.allocation (address.offset / 32) initial
    exact ⟨result.1, result.2.1, result.2.2.1, result.2.2.2.1⟩

theorem length_write_is_store (state ready : State) (header : Address) (length : Nat)
    (written : writeLength state header length = .ok ready) :
    store state (.pointer (.pointer true false usize) ⟨header.allocation, header.offset + lengthOffset⟩)
      (.scalar (.int false 64 length)) = .ok ready := by
  unfold writeLength at written
  cases selected : fieldPointer state (.pointer (.pointer true false allocationType) header) lengthOffset with
  | error fault => rw [selected] at written <;> cases written
  | ok pointer =>
    rw [selected] at written
    simp only [bind, Except.bind] at written
    obtain ⟨type, declared, rfl⟩ := fieldPointer_address state true false allocationType header lengthOffset pointer selected
    have same := Option.some.inj (declared.symm.trans length_type_checked)
    subst type
    exact written

theorem assumeCapacity_storage (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (initial : state.valid = true) :
    (assumeCapacity state header itemAddress argumentsAddress argumentsLength id sequence).2.valid = true ∧
      state.heap.RetainsShape (assumeCapacity state header itemAddress argumentsAddress argumentsLength id sequence).2.heap ∧
      (assumeCapacity state header itemAddress argumentsAddress argumentsLength id sequence).2.nextId = state.nextId ∧
      (assumeCapacity state header itemAddress argumentsAddress argumentsLength id sequence).2.nextAddress = state.nextAddress := by
  unfold assumeCapacity
  split
  · exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl⟩
  · rename_i length lengthRead
    split
    · exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl⟩
    · dsimp only
      split
      · exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl⟩
      · split
        · exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl⟩
        · rename_i ready written
          have stored := length_write_is_store state ready header _ written
          have tail := finish_storage ready header (nextLength length.toNat) itemAddress argumentsAddress argumentsLength id sequence
            (store_preserves_valid _ _ _ _ initial stored)
          have counters := store_keeps_counters _ _ _ _ stored
          exact ⟨tail.1, (store_retains_shape _ _ _ _ stored).trans tail.2.1,
            tail.2.2.1.trans counters.1, tail.2.2.2.trans counters.2⟩
    · exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl⟩
  · exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl⟩

theorem run_valid (state : State) (header : Address) (itemAddress argumentsAddress : Address)
    (argumentsLength : Nat) (id sequence : Int) (allocate : RegionAllocation.Allocator σ) (effects : σ)
    (initial : state.valid = true) :
    (run state header itemAddress argumentsAddress argumentsLength id sequence allocate effects).1.2.valid = true := by
  unfold run runWithCapacity
  split
  · exact initial
  · rename_i length lengthRead
    dsimp only
    split
    · exact initial
    · have capacityValid := (Capacity.ensure_storage state header (nextLength length.toNat) allocate effects initial).1
      generalize resolved : Capacity.ensure state header (nextLength length.toNat) allocate effects = outcome at *
      rcases outcome with ⟨⟨result, ready⟩, reached⟩
      cases result with
      | error fault => exact capacityValid
      | ok value =>
        cases value with
        | none => exact capacityValid
        | some value =>
          cases value
          have appended := (assumeCapacity_storage ready header itemAddress argumentsAddress argumentsLength id sequence capacityValid).1
          generalize assigned : assumeCapacity ready header itemAddress argumentsAddress argumentsLength id sequence = outcome at *
          rcases outcome with ⟨result, after⟩
          cases result <;> exact appended
  · exact initial

end Compiler.Extraction.RepresentativeArray.Append.Execution
