/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordExchange

namespace Compiler.ZigAir.Memory.WordArray

def Outside (view : View) (offset : Nat) : Prop :=
  offset < view.first * 4 ∨ (view.first + view.length) * 4 ≤ offset

/-- Observational framing of word storage outside this sub-slice, including
invalid/uninitialized reads. Other allocations and counters remain exact. -/
structure Frame (view : View) (before after : State) : Prop where
  nextId : after.nextId = before.nextId
  nextAddress : after.nextAddress = before.nextAddress
  allocations : ∀ id, id ≠ view.allocation → after.heap.lookup id = before.heap.lookup id
  outside : ∀ offset, Outside view offset →
    load after (.pointer (.pointer true false word) ⟨view.allocation, offset⟩) =
      load before (.pointer (.pointer true false word) ⟨view.allocation, offset⟩)

theorem Frame.refl (view : View) (state : State) : Frame view state state :=
  ⟨rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Frame.trans (first : Frame view before middle) (second : Frame view middle after) :
    Frame view before after :=
  ⟨second.nextId.trans first.nextId, second.nextAddress.trans first.nextAddress,
    fun id apart => (second.allocations id apart).trans (first.allocations id apart),
    fun offset outside => (second.outside offset outside).trans (first.outside offset outside)⟩

theorem frame_store (state after : State) (view : View) (index : Nat) (value : BitVec 32)
    (inside : index < view.length) (stored : store state (view.pointer index) (number value) = .ok after) :
    Frame view state after := by
  have base := write_allocation_frame state after view index value stored
  refine ⟨base.1, base.2.1, base.2.2, ?_⟩
  intro offset outside
  apply write_offset_frame state after view index offset value stored
  simp only [Outside, View.address] at *
  omega

theorem exchange_frame (state after : State) (view : View) (items : List (BitVec 32)) (left right : Nat)
    (initial : state.valid = true) (cap : Writable state view)
    (represented : Represents state view items) (leftInside : left < items.length) (rightInside : right < items.length)
    (ran : exchange state view left right = (.ok (), after)) : Frame view state after := by
  have leftBound : left < view.length := by simpa only [represented.1] using leftInside
  have rightBound : right < view.length := by simpa only [represented.1] using rightInside
  obtain ⟨middle, first⟩ := write_total state view left items[right] initial cap leftBound
  obtain ⟨final, second⟩ := write_total middle view right items[left]
    (store_preserves_valid state _ _ middle initial first)
    (writable_store state middle view _ _ first cap) rightBound
  have executed := exchange_of_effects state middle final view left right _ _ leftBound rightBound
    (represented.2 left leftInside) (represented.2 right rightInside) first second
  have same : final = after := (Prod.mk.inj (executed.symm.trans ran)).2
  subst final
  exact (frame_store state middle view left items[right] leftBound first).trans
    (frame_store middle after view right items[left] rightBound second)

end Compiler.ZigAir.Memory.WordArray
