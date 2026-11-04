/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapInitialization
import Compiler.Extraction.RepresentativeArrayAppend

namespace Compiler.Extraction.RepresentativeArray.Owner.NativeLock
open Compiler.ZigAir.Memory

/-- The captured Zig 0.17 ArrayList lock is a separate leaf of the same owner.
No lock storage exists in the admitted ReleaseFast layout. -/
def pointer (state : State) (owner : Address) (writable : Bool) : Except Fault Value := do
  let lock ← fieldPointer state (.pointer (.pointer writable false (viewType true)) owner) representativesLockOffset
  fieldPointer state lock 0

def checkUnlocked (runtimeSafety : Bool) (state : State) (owner : Address) : Except Fault Unit := do
  if !runtimeSafety then return ()
  let selected ← pointer state owner false
  let value ← load state selected
  if value = .scalar (.int false 64 0) then .ok () else .error .unsupported

/-- Recover the mode from the captured owner type rather than accepting a
caller-selected mode that could omit a native safety check. Header-only views
are not complete native owners and cannot pass this boundary. -/
def checkHeader (state : State) (header : Address) : Except Fault Unit := do
  if header.offset ≠ representativesOffset then .error .memoryValidity else do
  let some cell := state.heap.lookup header.allocation | .error .unallocated
  if cell.type = viewType false then .ok () else
  if cell.type = viewType true then checkUnlocked true state ⟨header.allocation, 0⟩
  else .error .unsupported

theorem checkHeader_owner (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (found : state.heap.lookup lifetime = some cell) (typed : cell.type = viewType runtimeSafety) :
    checkHeader state (headerAddress ⟨lifetime, 0⟩) = checkUnlocked runtimeSafety state ⟨lifetime, 0⟩ := by
  cases runtimeSafety <;> simp only [checkHeader, headerAddress, Nat.zero_add, ne_self_iff_false,
    ↓reduceIte, found, typed]
  · rfl
  · rw [if_neg (by decide : viewType true ≠ viewType false)]

def initializeLock (runtimeSafety : Bool) (state : State) (owner : Address) : Except Fault State := do
  if !runtimeSafety then return state
  let selected ← pointer state owner true
  store state selected (.scalar (.int false 64 0))

theorem root_pointer (state : State) (lifetime : Nat) (cell : Allocation) (writable : Bool)
    (valid : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = viewType true) :
    pointer state ⟨lifetime, 0⟩ writable =
      .ok (.pointer (.pointer writable false usize) ⟨lifetime, representativesLockOffset⟩) := by
  have selected := root_fieldPointer state lifetime cell (viewType true) ExpressionMap.lockType
    (layout true) representativesLockOffset writable false valid found typed (view_layout_checked true)
    (by decide) (by rfl)
  have parent := root_access state lifetime cell (layout true) false valid found
    (typed ▸ view_layout_checked true) (by decide) (by simp)
  have accessed := access_subregion state ⟨lifetime, 0⟩ (layout true) ⟨8, 8⟩ representativesLockOffset false cell
    parent (by decide) (by decide) (by decide) (by decide)
  have inner := fieldPointer_of_access state ⟨lifetime, representativesLockOffset⟩ cell ExpressionMap.lockType usize
    ⟨8, 8⟩ 0 writable false rfl accessed (by rw [typed]; rfl) (by rfl)
  simpa only [pointer, selected, bind, Except.bind, Nat.add_zero] using inner

/-- A native lock observation comes from the same declared owner cells. -/
theorem checkHeader_of_cell (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (valid : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = viewType runtimeSafety)
    (unlocked : runtimeSafety = true → cell.cells.lookup representativesLockOffset = some (.scalar (.int false 64 0))) :
    checkHeader state (headerAddress ⟨lifetime, 0⟩) = .ok () := by
  rw [checkHeader_owner runtimeSafety state lifetime cell found typed]
  cases runtimeSafety with
  | false => rfl
  | true =>
    have parent := root_access state lifetime cell (layout true) false valid found
      (typed ▸ view_layout_checked true) (by decide) (by simp)
    have accessed := access_subregion state ⟨lifetime, 0⟩ (layout true) ⟨8, 8⟩ representativesLockOffset false cell
      parent (by decide) (by decide) (by decide) (by decide)
    change access state ⟨lifetime, representativesLockOffset⟩ ⟨8, 8⟩ false = .ok cell at accessed
    have view : acceptsView cell.type representativesLockOffset usize = true := by rw [typed]; decide
    have leaf : leafType cell.type representativesLockOffset = some usize := by rw [typed]; decide
    simp only [usize] at view leaf
    simp only [checkUnlocked, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      root_pointer state lifetime cell false valid found typed, bind, Except.bind, pure, Except.pure,
      load, usize, Ty.layout, Ty.leafLayout, accessed, readCell, Cells.read, view,
      Cells.readLeaf, leaf, ne_self_iff_false, unlocked rfl]
    rfl

theorem pointer_eq_of_lookup (before after : State) (owner : Address) (writable : Bool)
    (same : after.heap.lookup owner.allocation = before.heap.lookup owner.allocation) :
    pointer after owner writable = pointer before owner writable := by
  unfold pointer
  rw [fieldPointer_eq_of_lookup before after writable false (viewType true) owner representativesLockOffset same]
  generalize selected : fieldPointer before (.pointer (.pointer writable false (viewType true)) owner)
    representativesLockOffset = result
  cases result with
  | error reason => rfl
  | ok value =>
    obtain ⟨field, _, rfl⟩ := fieldPointer_address before writable false (viewType true) owner representativesLockOffset value selected
    simpa only [bind, Except.bind] using fieldPointer_eq_of_lookup before after writable false field
      ⟨owner.allocation, owner.offset + representativesLockOffset⟩ 0 same

/-- Private argument/item preparation retains the same owner allocation, so
its lock observation is retained without assuming a new unlocked state. -/
theorem checkHeader_eq_of_lookup (runtimeSafety : Bool) (before after : State) (lifetime : Nat) (cell : Allocation)
    (validAfter : after.valid = true)
    (found : before.heap.lookup lifetime = some cell) (typed : cell.type = viewType runtimeSafety)
    (same : after.heap.lookup lifetime = before.heap.lookup lifetime) :
    checkHeader after (headerAddress ⟨lifetime, 0⟩) = checkHeader before (headerAddress ⟨lifetime, 0⟩) := by
  rw [checkHeader_owner runtimeSafety before lifetime cell found typed,
    checkHeader_owner runtimeSafety after lifetime cell (same.trans found) typed]
  cases runtimeSafety with
  | false => rfl
  | true =>
    have beforePointer := (pointer_eq_of_lookup before after ⟨lifetime, 0⟩ false same).symm.trans
      (root_pointer after lifetime cell false validAfter (same.trans found) typed)
    simp only [checkUnlocked, Bool.not_true, Bool.false_eq_true, ↓reduceIte, beforePointer,
      root_pointer after lifetime cell false validAfter (same.trans found) typed,
      bind, Except.bind, pure, Except.pure]
    rw [load_eq_of_lookup before after false false usize ⟨lifetime, representativesLockOffset⟩ same]

/-- Updating the representative length preserves the owner's separate lock
leaf in the actual reached memory, in both captured layouts. -/
theorem checkHeader_after_length_store (runtimeSafety : Bool) (before after : State) (lifetime length : Nat)
    (cell : Allocation) (valid : before.valid = true) (found : before.heap.lookup lifetime = some cell)
    (typed : cell.type = viewType runtimeSafety)
    (stored : store before (.pointer (.pointer true false usize) ⟨lifetime, representativesOffset + Append.lengthOffset⟩)
      (.scalar (.int false 64 length)) = .ok after) :
    checkHeader after (headerAddress ⟨lifetime, 0⟩) = checkHeader before (headerAddress ⟨lifetime, 0⟩) := by
  have afterValid := store_preserves_valid _ _ _ _ valid stored
  obtain ⟨kept, keptFound, shape⟩ := (store_retains_shape _ _ _ _ stored) lifetime cell found
  have keptTyped := shape.2.1.trans typed
  rw [checkHeader_owner runtimeSafety after lifetime kept keptFound keptTyped,
    checkHeader_owner runtimeSafety before lifetime cell found typed]
  cases runtimeSafety with
  | false => rfl
  | true =>
    have unchanged := load_disjoint_after_store before true false usize
      ⟨lifetime, representativesOffset + Append.lengthOffset⟩ (.scalar (.int false 64 length)) after
      false false usize representativesLockOffset stored (by
        intro position member entry present
        simp only [Ty.readOffsets, usize, List.mem_singleton] at member
        simp only [Value.leaves, List.mem_singleton] at present
        subst position
        subst entry
        change (40 : Nat) ≠ 24
        decide)
    simp only [checkUnlocked, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      root_pointer before lifetime cell false valid found typed,
      root_pointer after lifetime kept false afterValid keptFound keptTyped,
      bind, Except.bind, unchanged]

structure Initialized (runtimeSafety : Bool) (before after : State) (lifetime : Nat) : Prop extends
    ExpressionMap.Initialization.Frame runtimeSafety before after lifetime where
  unlocked : checkUnlocked runtimeSafety after ⟨lifetime, 0⟩ = .ok ()
  map : ∀ slot, slot.Active runtimeSafety →
    ExpressionMap.Initialization.read runtimeSafety after ⟨lifetime, 0⟩ slot =
      ExpressionMap.Initialization.read runtimeSafety before ⟨lifetime, 0⟩ slot

/-- Initialization writes the actual lock leaf. Its value and all other owner
observations follow from this store, without an initialized-lock premise. -/
theorem initialize_verified (runtimeSafety : Bool) (state : State) (lifetime : Nat) (cell : Allocation)
    (valid : state.valid = true) (found : state.heap.lookup lifetime = some cell)
    (typed : cell.type = viewType runtimeSafety) (writable : cell.writable = true) :
    ∃ after, initializeLock runtimeSafety state ⟨lifetime, 0⟩ = .ok after ∧
      Initialized runtimeSafety state after lifetime := by
  cases runtimeSafety with
  | false =>
    exact ⟨state, rfl, ⟨⟨valid, Heap.RetainsShape.refl _, rfl, rfl, rfl, fun _ _ => rfl⟩,
      rfl, fun _ _ => rfl⟩⟩
  | true =>
    have parent := root_access state lifetime cell (layout true) true valid found
      (typed ▸ view_layout_checked true) (by decide) (by intro _; exact writable)
    have accessed := access_subregion state ⟨lifetime, 0⟩ (layout true) ⟨8, 8⟩ representativesLockOffset true cell
      parent (by decide) (by decide) (by decide) (by decide)
    obtain ⟨after, stored⟩ := store_subobject_total state ⟨lifetime, representativesLockOffset⟩ ⟨8, 8⟩ cell
      (.scalar (.int false 64 0)) (by decide) rfl accessed (by rw [typed]; rfl)
      (by intro entry member; simp only [Value.leaves, List.mem_singleton] at member
          subst entry; rw [typed]; rfl)
    have validAfter := store_preserves_valid _ _ _ _ valid stored
    obtain ⟨finalCell, finalFound, shape⟩ := store_retains_shape _ _ _ _ stored lifetime cell found
    have selected := root_pointer state lifetime cell true valid found typed
    have finalPointer := root_pointer after lifetime finalCell false validAfter finalFound (shape.2.1.trans typed)
    refine ⟨after, ?_, ⟨⟨validAfter, store_retains_shape _ _ _ _ stored, ?_,
      (store_keeps_counters _ _ _ _ stored).1, (store_keeps_counters _ _ _ _ stored).2,
      heap_after_store_other _ true false usize _ _ _ stored⟩, ?_, ?_⟩⟩
    · simpa only [initializeLock, Bool.not_true, Bool.false_eq_true, ↓reduceIte, selected, bind, Except.bind] using stored
    · exact ExpressionMap.header_frame_of_store true state after lifetime cell (.scalar (.int false 64 0))
        representativesLockOffset valid found typed stored (by decide) (by decide)
    · simp only [checkUnlocked, Bool.not_true, Bool.false_eq_true, ↓reduceIte, finalPointer, bind, Except.bind, pure, Except.pure]
      rw [load_alias_after_store state true false usize _ _ after false false stored]
      rfl
    · intro slot active
      simp only [ExpressionMap.Initialization.read,
        ExpressionMap.Initialization.root_pointer true after lifetime finalCell false slot active validAfter finalFound (shape.2.1.trans typed),
        ExpressionMap.Initialization.root_pointer true state lifetime cell false slot active valid found typed, bind, Except.bind]
      apply load_disjoint_after_store state true false usize _ _ after false false slot.value.type
        (expressionsOffset true + slot.offset true) stored
      change ∀ position, position ∈ slot.value.type.readOffsets (expressionsOffset true + slot.offset true) →
        ∀ entry, entry ∈ (.scalar (.int false 64 0) : Value).leaves representativesLockOffset → position ≠ entry.1
      cases slot <;> decide


end Compiler.Extraction.RepresentativeArray.Owner.NativeLock
