/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordFrame

/-! Typed u32 copying for the normalization builtin boundary. The source is
readonly; destination contents need not be initialized. Length and overlap
checks precede all accesses. This is an executable memory specification, not a
claim about captured memcpy AIR or its native lowering. -/
namespace Compiler.ZigAir.Memory.WordCopy
open WordArray

def readPointer (source : View) (index : Nat) : Value :=
  .pointer (.pointer false false word) (source.address index)

theorem load_readonly (state : State) (source : View) (index : Nat) :
    load state (readPointer source index) = load state (source.pointer index) := rfl

def disjoint (source target : View) : Bool :=
  decide (source.allocation ≠ target.allocation ∨
    source.first + source.length ≤ target.first ∨ target.first + target.length ≤ source.first)

def copyFrom (source target : View) : Nat → Nat → State → Except Fault Unit × State
  | 0, _, state => (.ok (), state)
  | remaining + 1, index, state =>
    if index < source.length ∧ index < target.length then
      match load state (readPointer source index) with
      | .error fault => (.error fault, state)
      | .ok value => match store state (target.pointer index) value with
        | .error fault => (.error fault, state)
        | .ok middle => copyFrom source target remaining (index + 1) middle
    else (.error .sourceBounds, state)

theorem copyFrom_step (source target : View) (remaining index : Nat) (state middle : State) (value : Value)
    (sourceBound : index < source.length) (targetBound : index < target.length)
    (read : load state (readPointer source index) = .ok value)
    (written : store state (target.pointer index) value = .ok middle) :
    copyFrom source target (remaining + 1) index state = copyFrom source target remaining (index + 1) middle := by
  simp only [copyFrom, sourceBound, targetBound, and_self, ↓reduceIte, read, written]

def copy (state : State) (source target : View) : Except Fault Unit × State :=
  if source.length ≠ target.length then (.error .sourceBounds, state)
  else if !disjoint source target then (.error .memoryValidity, state)
  else copyFrom source target source.length 0 state

/-- Copy preserves the reached allocation counter on success and every partial-copy fault. -/
theorem copyFrom_address (source target : View) (remaining index : Nat) (state : State) :
    (copyFrom source target remaining index state).2.nextAddress = state.nextAddress := by
  induction remaining generalizing index state with
  | zero => rfl
  | succ remaining ih =>
    simp only [copyFrom]
    split
    · cases read : load state (readPointer source index) with
      | error fault => rfl
      | ok value =>
        simp only
        cases written : store state (target.pointer index) value with
        | error fault => rfl
        | ok middle =>
          exact (ih (index + 1) middle).trans (store_keeps_counters _ _ _ _ written).2
    · rfl

theorem copy_address (state : State) (source target : View) :
    (copy state source target).2.nextAddress = state.nextAddress := by
  simp only [copy]
  split
  · rfl
  · split
    · rfl
    · exact copyFrom_address _ _ _ _ _

theorem disjoint_offsets (source target : View) (left right : Nat)
    (separate : disjoint source target = true) (same : source.allocation = target.allocation)
    (hl : left < source.length) (hr : right < target.length) :
    (source.address left).offset ≠ (target.address right).offset := by
  simp only [disjoint, decide_eq_true_eq] at separate
  simp only [View.address]
  omega

/-- A destination write preserves every initialized source word, including
disjoint sub-slices of the same allocation. No source write permission is used. -/
theorem source_after_store (state after : State) (source target : View) (items : List (BitVec 32))
    (index : Nat) (value : BitVec 32) (inside : index < target.length)
    (separate : disjoint source target = true) (represented : Represents state source items)
    (written : store state (target.pointer index) (number value) = .ok after) : Represents after source items := by
  refine ⟨represented.1, ?_⟩
  intro other bound
  have old := represented.2 other bound
  by_cases same : source.allocation = target.allocation
  · have apart := disjoint_offsets source target other index separate same (by simpa only [represented.1] using bound) inside
    have framed := write_offset_frame state after target index (source.address other).offset value written apart
    simpa only [View.pointer, View.address, same] using framed.trans (by simpa only [View.pointer, View.address, same] using old)
  · exact (load_other_after_store state true false word (target.address index) (number value) after
      true false word (source.address other) written same).trans old

def Prefix (state : State) (target : View) (items : List (BitVec 32)) (count : Nat) : Prop :=
  ∀ index (inside : index < items.length), index < count → load state (target.pointer index) = .ok (number items[index])

theorem prefix_after_store (state after : State) (target : View) (items : List (BitVec 32)) (index : Nat)
    (bound : index < items.length) (prior : Prefix state target items index)
    (written : store state (target.pointer index) (number items[index]) = .ok after) :
    Prefix after target items (index + 1) := by
  intro other inside earlier
  by_cases same : other = index
  · subst other
    exact load_after_store state (target.pointer index) (number items[index]) after written
  · rw [write_frame state after target index other items[index] written same]
    exact prior other inside (by omega)

end Compiler.ZigAir.Memory.WordCopy
