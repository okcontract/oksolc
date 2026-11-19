/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpScratch

/-! Total scratch effects and exact preservation of the older heap. These
are facts about the checked memory model, not native stack correspondence. -/
namespace Compiler.ZigAir.MemoryExp
open Memory MemoryAir

structure Progress (mark : Nat) (before after : State) : Prop where
  valid : after.valid = true
  stack : after.heap.StackSince mark
  older : after.heap.older mark = before.heap.older mark
  nextId : before.nextId ≤ after.nextId

theorem Progress.refl (mark : Nat) (state : State) (valid : state.valid = true)
    (stack : state.heap.StackSince mark) : Progress mark state state := ⟨valid, stack, rfl, Nat.le_refl _⟩

theorem Progress.trans {mark : Nat} {first middle last : State}
    (left : Progress mark first middle) (right : Progress mark middle last) : Progress mark first last :=
  ⟨right.valid, right.stack, right.older.trans left.older, Nat.le_trans left.nextId right.nextId⟩

theorem store_progress (mark : Nat) (state after : State) (address : Address) (value : Word)
    (valid : state.valid = true) (stack : state.heap.StackSince mark) (fresh : mark ≤ address.allocation)
    (stored : store state (slot address) (number value) = .ok after) : Progress mark state after := by
  obtain ⟨stacks, older⟩ := store_frame state after true false wordType address (number value) mark stored fresh stack
  exact ⟨store_preserves_valid state _ _ after valid stored, stacks, older,
    Nat.le_of_eq (store_keeps_counters state _ _ after stored).1.symm⟩

def Capabilities (state : State) (baseSlot exponentSlot resultSlot : Address) : Prop :=
  Writable state baseSlot ∧ Writable state exponentSlot ∧ Writable state resultSlot
def FreshSlots (mark : Nat) (baseSlot exponentSlot resultSlot : Address) : Prop :=
  mark ≤ baseSlot.allocation ∧ mark ≤ exponentSlot.allocation ∧ mark ≤ resultSlot.allocation

theorem Capabilities.store (state after : State) (baseSlot exponentSlot resultSlot written : Address) (value : Word)
    (caps : Capabilities state baseSlot exponentSlot resultSlot)
    (stored : store state (slot written) (number value) = .ok after) :
    Capabilities after baseSlot exponentSlot resultSlot :=
  ⟨writable_store state after written baseSlot value stored caps.1,
    writable_store state after written exponentSlot value stored caps.2.1,
    writable_store state after written resultSlot value stored caps.2.2⟩

theorem halve_total (mark : Nat) (state : State) (baseSlot exponentSlot resultSlot : Address) (exponent : Word)
    (valid : state.valid = true) (stack : state.heap.StackSince mark)
    (caps : Capabilities state baseSlot exponentSlot resultSlot) (fresh : mark ≤ exponentSlot.allocation) :
    ∃ after, halve state exponentSlot exponent = (.ok (), after) ∧ Progress mark state after ∧
      Capabilities after baseSlot exponentSlot resultSlot := by
  obtain ⟨after, stored⟩ := write_total state exponentSlot (exponent >>> 1) valid caps.2.1
  exact ⟨after, by rw [halve, stored, finishWrite],
    store_progress mark state after exponentSlot _ valid stack fresh stored,
    caps.store state after baseSlot exponentSlot resultSlot exponentSlot _ stored⟩

theorem square_total (mark : Nat) (state : State) (baseSlot exponentSlot resultSlot : Address) (base exponent : Word)
    (valid : state.valid = true) (stack : state.heap.StackSince mark)
    (caps : Capabilities state baseSlot exponentSlot resultSlot) (fresh : FreshSlots mark baseSlot exponentSlot resultSlot) :
    ∃ after, square state baseSlot exponentSlot base exponent = (.ok (), after) ∧ Progress mark state after ∧
      Capabilities after baseSlot exponentSlot resultSlot := by
  obtain ⟨middle, stored⟩ := write_total state baseSlot (base * base) valid caps.1
  have progressed := store_progress mark state middle baseSlot _ valid stack fresh.1 stored
  obtain ⟨after, halved, next, nextCaps⟩ := halve_total mark middle baseSlot exponentSlot resultSlot exponent
    progressed.valid progressed.stack (caps.store state middle baseSlot exponentSlot resultSlot baseSlot _ stored) fresh.2.1
  exact ⟨after, by rw [square, stored, afterSquare, halved], progressed.trans next, nextCaps⟩

theorem step_total (mark : Nat) (state : State) (baseSlot exponentSlot resultSlot : Address) (base exponent result : Word)
    (valid : state.valid = true) (stack : state.heap.StackSince mark)
    (caps : Capabilities state baseSlot exponentSlot resultSlot) (fresh : FreshSlots mark baseSlot exponentSlot resultSlot) :
    ∃ after, step state baseSlot exponentSlot resultSlot base exponent result = (.ok (), after) ∧
      Progress mark state after ∧ Capabilities after baseSlot exponentSlot resultSlot := by
  by_cases odd : exponent &&& 1 ≠ 0
  · obtain ⟨middle, stored⟩ := write_total state resultSlot (result * base) valid caps.2.2
    have progressed := store_progress mark state middle resultSlot _ valid stack fresh.2.2 stored
    obtain ⟨after, squared, next, nextCaps⟩ := square_total mark middle baseSlot exponentSlot resultSlot base exponent
      progressed.valid progressed.stack (caps.store state middle baseSlot exponentSlot resultSlot resultSlot _ stored) fresh
    exact ⟨after, by rw [step, if_pos odd, stored, afterResult, squared], progressed.trans next, nextCaps⟩
  · simpa only [step, if_neg odd] using square_total mark state baseSlot exponentSlot resultSlot base exponent valid stack caps fresh

theorem effects_total (mark : Nat) (state : State) (baseSlot exponentSlot resultSlot : Address) (base exponent result : Word)
    (valid : state.valid = true) (stack : state.heap.StackSince mark)
    (caps : Capabilities state baseSlot exponentSlot resultSlot) (fresh : FreshSlots mark baseSlot exponentSlot resultSlot) :
    ∃ value after, effects baseSlot exponentSlot resultSlot base exponent result state = (.ok value, after) ∧
      Progress mark state after := by
  rw [effects]
  split
  · exact ⟨result, state, rfl, Progress.refl mark state valid stack⟩
  · obtain ⟨middle, stepped, progressed, nextCaps⟩ := step_total mark state baseSlot exponentSlot resultSlot base exponent result valid stack caps fresh
    rw [stepped]
    obtain ⟨value, after, done, next⟩ := effects_total mark middle baseSlot exponentSlot resultSlot
      (base * base) (exponent >>> 1) (nextResult base exponent result) progressed.valid progressed.stack nextCaps fresh
    exact ⟨value, after, done, progressed.trans next⟩
termination_by exponent.toNat
decreasing_by apply halve_decreases; assumption

end Compiler.ZigAir.MemoryExp
