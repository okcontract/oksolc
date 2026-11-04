/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryExpSafety

namespace Compiler.ZigAir.MemoryExp
open Memory MemoryAir

theorem writable_older (state : State) (address : Address) (valid : state.valid = true)
    (cap : Writable state address) : address.allocation < state.nextId := by
  obtain ⟨_, cell, found, _, _⟩ := cap
  exact (valid_lookup state address.allocation cell valid found).1

/-- One checked allocation and initialization either exhausts the address
space or establishes a fresh writable word while preserving prior words. -/
theorem initialize_safe (mark : Nat) (state : State) (value : Word)
    (valid : state.valid = true) (stack : state.heap.StackSince mark) (fresh : mark ≤ state.nextId) :
    allocate state wordType = .error .outOfMemory ∨ ∃ allocated after,
      allocate state wordType = .ok (slot ⟨state.nextId, 0⟩, allocated) ∧
      store allocated (slot ⟨state.nextId, 0⟩) (number value) = .ok after ∧
      Progress mark state after ∧ Writable after ⟨state.nextId, 0⟩ ∧
      (∀ address, Writable state address → Writable after address) := by
  cases allocation : allocate state wordType with
  | error reason =>
    have same := allocate_fault state reason valid allocation
    exact Or.inl (congrArg Except.error same)
  | ok pair =>
    obtain ⟨pointer, allocated⟩ := pair
    obtain ⟨rfl, nextId⟩ := allocate_pointer state wordType pointer allocated allocation
    have allocatedValid := allocate_preserves_valid state wordType _ allocated allocation
    obtain ⟨stacked, framed⟩ := allocate_frame state allocated wordType _ mark allocation fresh stack
    have allocatedProgress : Progress mark state allocated := ⟨allocatedValid, stacked, framed, by omega⟩
    have cap := writable_fresh state allocated _ allocation
    obtain ⟨after, stored⟩ := write_total allocated ⟨state.nextId, 0⟩ value allocatedValid cap
    refine Or.inr ⟨allocated, after, rfl, stored,
      allocatedProgress.trans (store_progress mark allocated after _ value allocatedValid stacked fresh stored),
      writable_store allocated after _ _ value stored cap, ?_⟩
    intro address old
    have apart : address.allocation ≠ state.nextId := Nat.ne_of_lt (writable_older state address valid old)
    exact writable_store allocated after _ address value stored (writable_allocate state allocated _ address allocation old apart)

inductive PreparedSafe (mark : Nat) (before : State) : Preparation → Prop
  | oom (after : State) (progress : Progress mark before after) : PreparedSafe mark before (.fault .outOfMemory after)
  | ready (baseSlot exponentSlot resultSlot : Address) (after : State)
      (progress : Progress mark before after) (caps : Capabilities after baseSlot exponentSlot resultSlot)
      (fresh : FreshSlots mark baseSlot exponentSlot resultSlot) :
      PreparedSafe mark before (.ready baseSlot exponentSlot resultSlot after)

theorem prepare_safe (mark : Nat) (state : State) (base exponent : Word)
    (valid : state.valid = true) (stack : state.heap.StackSince mark) (fresh : mark ≤ state.nextId) :
    PreparedSafe mark state (prepare base exponent state) := by
  rcases initialize_safe mark state base valid stack fresh with oom | ⟨allocated, first, allocatedBase, storedBase, firstProgress, baseCap, _⟩
  · rw [prepare, oom, baseAllocated]
    exact .oom state (Progress.refl mark state valid stack)
  · rw [prepare, allocatedBase, baseAllocated, storedBase, baseStored]
    have freshFirst := Nat.le_trans fresh firstProgress.nextId
    rcases initialize_safe mark first exponent firstProgress.valid firstProgress.stack freshFirst with
      oom | ⟨allocated, second, allocatedExponent, storedExponent, secondProgress, exponentCap, keepSecond⟩
    · rw [oom, exponentAllocated]
      exact .oom first firstProgress
    · rw [allocatedExponent, exponentAllocated, storedExponent, exponentStored]
      have freshSecond := Nat.le_trans freshFirst secondProgress.nextId
      rcases initialize_safe mark second 1 secondProgress.valid secondProgress.stack freshSecond with
        oom | ⟨allocated, third, allocatedResult, storedResult, thirdProgress, resultCap, keepThird⟩
      · rw [oom, resultAllocated]
        exact .oom second (firstProgress.trans secondProgress)
      · rw [allocatedResult, resultAllocated, storedResult, resultStored]
        exact .ready _ _ _ third (firstProgress.trans (secondProgress.trans thirdProgress))
          ⟨keepThird _ (keepSecond _ baseCap), keepThird _ exponentCap, resultCap⟩
          ⟨fresh, freshFirst, freshSecond⟩

end Compiler.ZigAir.MemoryExp
