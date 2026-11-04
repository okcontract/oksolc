/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordArrayWrites

/-! Checked typed-word exchange, the memory contract needed by normalization.
This is not the runtime byte loop of std.mem.swap: its byte-view refinement and
native pointer correspondence remain separate obligations. -/
namespace Compiler.ZigAir.Memory.WordArray

def exchange (state : State) (view : View) (left right : Nat) : Except Fault Unit × State :=
  if left < view.length ∧ right < view.length then
    match load state (view.pointer left) with
    | .error fault => (.error fault, state)
    | .ok a => match load state (view.pointer right) with
      | .error fault => (.error fault, state)
      | .ok b => match store state (view.pointer left) b with
        | .error fault => (.error fault, state)
        | .ok middle => match store middle (view.pointer right) a with
          | .error fault => (.error fault, middle)
          | .ok after => (.ok (), after)
  else (.error .sourceBounds, state)

theorem exchange_of_effects (state middle after : State) (view : View) (left right : Nat) (a b : Value)
    (leftInside : left < view.length) (rightInside : right < view.length)
    (readLeft : load state (view.pointer left) = .ok a)
    (readRight : load state (view.pointer right) = .ok b)
    (firstWrite : store state (view.pointer left) b = .ok middle)
    (secondWrite : store middle (view.pointer right) a = .ok after) :
    exchange state view left right = (.ok (), after) := by
  simp only [exchange, leftInside, rightInside, and_self, ↓reduceIte, readLeft, readRight,
    firstWrite, secondWrite]

theorem exchange_refines (state : State) (view : View) (items : List (BitVec 32)) (left right : Nat)
    (initial : state.valid = true) (cap : Writable state view) (represented : Represents state view items)
    (leftInside : left < items.length) (rightInside : right < items.length) :
    ∃ after, exchange state view left right = (.ok (), after) ∧
      after.valid = true ∧ Writable after view ∧
      Represents after view ((items.set left items[right]).set right items[left]) ∧
      after.nextId = state.nextId ∧ after.nextAddress = state.nextAddress ∧
      ∀ id, id ≠ view.allocation → after.heap.lookup id = state.heap.lookup id := by
  have leftBound : left < view.length := by simpa only [represented.1] using leftInside
  have rightBound : right < view.length := by simpa only [represented.1] using rightInside
  obtain ⟨middle, firstWrite⟩ := write_total state view left items[right] initial cap leftBound
  have middleValid := store_preserves_valid state _ _ middle initial firstWrite
  have middleCap := writable_store state middle view _ _ firstWrite cap
  obtain ⟨after, secondWrite⟩ := write_total middle view right items[left] middleValid middleCap rightBound
  have firstFrame := write_allocation_frame state middle view left items[right] firstWrite
  have secondFrame := write_allocation_frame middle after view right items[left] secondWrite
  refine ⟨after, exchange_of_effects state middle after view left right _ _ leftBound rightBound
      (represented.2 left leftInside) (represented.2 right rightInside) firstWrite secondWrite,
    store_preserves_valid middle _ _ after middleValid secondWrite,
    writable_store middle after view _ _ secondWrite middleCap,
    write_represents middle after view _ right items[left]
      (write_represents state middle view items left items[right] represented firstWrite) secondWrite,
    secondFrame.1.trans firstFrame.1, secondFrame.2.1.trans firstFrame.2.1, ?_⟩
  intro id apart
  exact (secondFrame.2.2 id apart).trans (firstFrame.2.2 id apart)

/-- The precise byte intervals of distinct u32 elements are disjoint. This
proves geometry in the existing heap model, not a native allocation theorem. -/
theorem element_regions (state : State) (view : View) (left right : Nat)
    (initial : state.valid = true) (cap : Writable state view)
    (leftInside : left < view.length) (rightInside : right < view.length) (apart : left ≠ right) :
    ∃ cell, state.heap.lookup view.allocation = some cell ∧
      0 < cell.base + (view.address left).offset ∧
      cell.base + (view.address left).offset + 4 ≤ addressLimit ∧
      0 < cell.base + (view.address right).offset ∧
      cell.base + (view.address right).offset + 4 ≤ addressLimit ∧
      (cell.base + (view.address left).offset + 4 ≤ cell.base + (view.address right).offset ∨
       cell.base + (view.address right).offset + 4 ≤ cell.base + (view.address left).offset) := by
  obtain ⟨extent, cell, found, typed, _, bound⟩ := cap
  obtain ⟨_, positive, layout, shaped, _, bounded, limit⟩ := valid_lookup state view.allocation cell initial found
  rw [typed, array_layout] at shaped
  cases Option.some.inj shaped
  dsimp only at bounded
  refine ⟨cell, found, ?_⟩
  simp only [View.address]
  omega

end Compiler.ZigAir.Memory.WordArray
