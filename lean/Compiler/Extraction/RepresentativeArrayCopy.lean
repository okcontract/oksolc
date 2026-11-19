/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayWrites
import Compiler.ZigAir.MemoryReadTyping

namespace Compiler.Extraction.RepresentativeArray.Copy
open Compiler.ZigAir.Memory

/-- Copy only the captured descriptor fields through checked reads and stores.
The reached destination prefix is retained on every fault. This is the typed
memcpy boundary for initialized descriptors, not a byte-punning operation or a
native memcpy implementation proof. Padding and spare capacity supply no values. -/
def fields (slots : List (Nat × Ty)) (source target : Address) (state : State) : Except Fault Unit × State :=
  match slots with
  | [] => (.ok (), state)
  | (offset, type) :: tail =>
    match Expression.readField state false source offset with
    | .error fault => (.error fault, state)
    | .ok value =>
      match store state (.pointer (.pointer true false type) ⟨target.allocation, target.offset + offset⟩) value with
      | .error fault => (.error fault, state)
      | .ok middle => fields tail source target middle

/-- ArrayList's fallback copies the initialized prefix, not its capacity.
Growth supplies distinct old/new allocation lifetimes; accepting overlapping
storage here would not implement the native memcpy precondition. -/
def copyFrom (source target : Nat) : Nat → Nat → State → Except Fault Unit × State
  | 0, _, state => (.ok (), state)
  | remaining + 1, index, state =>
    let (result, middle) := fields expressionSlots ⟨source, index * 32⟩ ⟨target, index * 32⟩ state
    match result with
    | .error fault => (.error fault, middle)
    | .ok () => copyFrom source target remaining (index + 1) middle

def run (state : State) (source target length : Nat) : Except Fault Unit × State :=
  if length = 0 then (.ok (), state) else
  if source = target then (.error .memoryValidity, state) else copyFrom source target length 0 state

/-- Successful typed field observations supply checked values for the matching
captured destination slot. A logical list of descriptors is not supplied. -/
theorem readField_hasType (state : State) (address : Address) (offset : Nat) (type : Ty) (value : Value)
    (declared : fieldType Expression.allocationType offset = some type)
    (loaded : Expression.readField state false address offset = .ok value) : value.hasType type = true := by
  unfold Expression.readField at loaded
  cases selected : fieldPointer state (.pointer (.pointer false false Expression.allocationType) address) offset with
  | error fault => simp [selected, bind, Except.bind] at loaded
  | ok pointer =>
    obtain ⟨field, shaped, rfl⟩ := fieldPointer_address state false false Expression.allocationType address offset pointer selected
    have same : field = type := Option.some.inj (shaped.symm.trans declared)
    subst field
    apply load_hasType state false false type ⟨address.allocation, address.offset + offset⟩ value
    simpa only [selected, bind, Except.bind] using loaded

theorem slot_declared (offset : Nat) (type : Ty) (member : (offset, type) ∈ expressionSlots) :
    fieldType Expression.allocationType offset = some type := by
  simp only [expressionSlots, Expression.allocationType, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false, Field.type, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- Validity, geometry and allocation history survive even a partial descriptor
copy. The exact old-allocation frame applies to every lifetime but the target. -/
theorem fields_storage (slots : List (Nat × Ty)) (source target : Address) (state : State)
    (initial : state.valid = true) :
    (fields slots source target state).2.valid = true ∧
      state.heap.RetainsShape (fields slots source target state).2.heap ∧
      (fields slots source target state).2.nextId = state.nextId ∧
      (fields slots source target state).2.nextAddress = state.nextAddress ∧
      (∀ id, id ≠ target.allocation → (fields slots source target state).2.heap.lookup id = state.heap.lookup id) := by
  induction slots generalizing state with
  | nil => exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl⟩
  | cons slot tail ih =>
    rcases slot with ⟨offset, type⟩
    simp only [fields]
    cases loaded : Expression.readField state false source offset with
    | error fault => exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl⟩
    | ok value =>
      dsimp only
      cases stored : store state (.pointer (.pointer true false type) ⟨target.allocation, target.offset + offset⟩) value with
      | error fault => exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl⟩
      | ok middle =>
        have rest := ih middle (store_preserves_valid _ _ _ _ initial stored)
        have counters := store_keeps_counters _ _ _ _ stored
        exact ⟨rest.1, (store_retains_shape _ _ _ _ stored).trans rest.2.1,
          rest.2.2.1.trans counters.1, rest.2.2.2.1.trans counters.2,
          fun id apart => (rest.2.2.2.2 id apart).trans (heap_after_store_other _ _ _ _ _ _ _ stored id apart)⟩

theorem copyFrom_storage (source target remaining index : Nat) (state : State) (initial : state.valid = true) :
    (copyFrom source target remaining index state).2.valid = true ∧
      state.heap.RetainsShape (copyFrom source target remaining index state).2.heap ∧
      (copyFrom source target remaining index state).2.nextId = state.nextId ∧
      (copyFrom source target remaining index state).2.nextAddress = state.nextAddress ∧
      (∀ id, id ≠ target → (copyFrom source target remaining index state).2.heap.lookup id = state.heap.lookup id) := by
  induction remaining generalizing index state with
  | zero => exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl⟩
  | succ remaining ih =>
    have first := fields_storage expressionSlots ⟨source, index * 32⟩ ⟨target, index * 32⟩ state initial
    cases executed : fields expressionSlots ⟨source, index * 32⟩ ⟨target, index * 32⟩ state with
    | mk result middle =>
      rw [executed] at first
      simp only [copyFrom, executed]
      cases result with
      | error fault => exact first
      | ok value =>
        have rest := ih (index + 1) middle first.1
        exact ⟨rest.1, first.2.1.trans rest.2.1, rest.2.2.1.trans first.2.2.1,
          rest.2.2.2.1.trans first.2.2.2.1,
          fun id apart => (rest.2.2.2.2 id apart).trans (first.2.2.2.2 id apart)⟩

theorem run_storage (state : State) (source target length : Nat) (initial : state.valid = true) :
    (run state source target length).2.valid = true ∧
      state.heap.RetainsShape (run state source target length).2.heap ∧
      (run state source target length).2.nextId = state.nextId ∧
      (run state source target length).2.nextAddress = state.nextAddress ∧
      (∀ id, id ≠ target → (run state source target length).2.heap.lookup id = state.heap.lookup id) := by
  unfold run
  split
  · exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl⟩
  · split
    · exact ⟨initial, Heap.RetainsShape.refl _, rfl, rfl, fun _ _ => rfl⟩
    · exact copyFrom_storage source target length 0 state initial

end Compiler.Extraction.RepresentativeArray.Copy
