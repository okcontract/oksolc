/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.WordByteExchange
import Compiler.ZigAir.MemoryWordBytes

/-! Sequential byte-exchange effects over the existing typed heap. This is the
effect specification for the pinned std.mem.swap(u32) loop, not a decoding of
its generic AIR body or a proof of its native noalias contract. Every fault
retains the effects already executed. -/
namespace Compiler.ZigAir.Memory.ByteExchange
open WordArray

def step (order : WordBytes.Order) (state : State) (view : View) (left right : Nat) (index : Fin 4) :
    Except Fault Unit × State :=
  if left < view.length ∧ right < view.length then
    match WordByteView.read order state (view.pointer left) index.val with
    | .error reason => (.error reason, state)
    | .ok a => match WordByteView.read order state (view.pointer right) index.val with
      | .error reason => (.error reason, state)
      | .ok b => match WordByteView.write order state (view.pointer left) index.val b with
        | .error reason => (.error reason, state)
        | .ok middle => match WordByteView.write order middle (view.pointer right) index.val a with
          | .error reason => (.error reason, middle)
          | .ok after => (.ok (), after)
  else (.error .sourceBounds, state)

def run (order : WordBytes.Order) (view : View) (left right : Nat) :
    List (Fin 4) → State → Except Fault Unit × State
  | [], state => (.ok (), state)
  | index :: rest, state => match step order state view left right index with
    | (.error reason, after) => (.error reason, after)
    | (.ok (), after) => run order view left right rest after

/-- Expose all four ordered effects of a successful step, including the
intermediate heap. Clients can connect instruction sequences without assuming
their intermediate reads and writes as independent premises. -/
theorem step_effects (order : WordBytes.Order) (state after : State) (view : View)
    (left right : Nat) (index : Fin 4) (ran : step order state view left right index = (.ok (), after)) :
    ∃ a b middle,
      WordByteView.read order state (view.pointer left) index.val = .ok a ∧
      WordByteView.read order state (view.pointer right) index.val = .ok b ∧
      WordByteView.write order state (view.pointer left) index.val b = .ok middle ∧
      WordByteView.write order middle (view.pointer right) index.val a = .ok after := by
  unfold step at ran
  split at ran
  · cases first : WordByteView.read order state (view.pointer left) index.val with
    | error reason => simp [first] at ran
    | ok a =>
      cases second : WordByteView.read order state (view.pointer right) index.val with
      | error reason => simp [first, second] at ran
      | ok b =>
        cases third : WordByteView.write order state (view.pointer left) index.val b with
        | error reason => simp [first, second, third] at ran
        | ok middle =>
          cases fourth : WordByteView.write order middle (view.pointer right) index.val a with
          | error reason => simp [first, second, third, fourth] at ran
          | ok final =>
            simp only [first, second, third, fourth, Prod.mk.injEq, true_and] at ran
            subst final
            exact ⟨a, b, middle, rfl, rfl, third, fourth⟩
  · simp at ran

def updated (items : List (BitVec 32)) (left right : Nat) (words : BitVec 32 × BitVec 32) : List (BitVec 32) :=
  (items.set left words.1).set right words.2

theorem updated_self (items : List (BitVec 32)) (left right : Nat)
    (hl : left < items.length) (hr : right < items.length) : updated items left right (items[left], items[right]) = items := by
  simp [updated, List.set_getElem_self hl, List.set_getElem_self hr]

theorem updated_updated (items : List (BitVec 32)) (left right : Nat) (a b : BitVec 32 × BitVec 32)
    (apart : left ≠ right) : updated (updated items left right a) left right b = updated items left right b := by
  simp only [updated]
  rw [List.set_comm a.2 b.1 (Ne.symm apart), List.set_set, List.set_set]

theorem updated_left (items : List (BitVec 32)) (left right : Nat) (words : BitVec 32 × BitVec 32)
    (inside : left < (updated items left right words).length) (apart : left ≠ right) :
    (updated items left right words)[left] = words.1 := by
  simp only [updated, List.getElem_set_ne (Ne.symm apart), List.getElem_set_self]

theorem updated_right (items : List (BitVec 32)) (left right : Nat) (words : BitVec 32 × BitVec 32)
    (inside : right < (updated items left right words).length) :
    (updated items left right words)[right] = words.2 := by
  simp only [updated, List.getElem_set_self]

theorem step_refines (order : WordBytes.Order) (state : State) (view : View) (items : List (BitVec 32))
    (left right : Nat) (index : Fin 4) (initial : state.valid = true) (cap : Writable state view)
    (represented : Represents state view items) (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right) :
    ∃ after, step order state view left right index = (.ok (), after) ∧
      after.valid = true ∧ Writable after view ∧
      Represents after view (updated items left right (WordBytes.exchangeLane order (items[left], items[right]) index)) ∧
      Frame view state after := by
  have lbound : left < view.length := by simpa only [represented.1] using hl
  have rbound : right < view.length := by simpa only [represented.1] using hr
  have readLeft := WordByteView.read_word order state (view.pointer left) index items[left] (represented.2 left hl)
  have readRight := WordByteView.read_word order state (view.pointer right) index items[right] (represented.2 right hr)
  obtain ⟨middle, first, middleValid, middleCap, middleRep, firstFrame⟩ :=
    WordByteView.write_refines order state view items left index (WordBytes.read order items[right] index) initial cap represented hl
  obtain ⟨after, second, afterValid, afterCap, afterRep, secondFrame⟩ :=
    WordByteView.write_refines order middle view _ right index (WordBytes.read order items[left] index)
      middleValid middleCap middleRep (by simpa using hr)
  refine ⟨after, ?_, afterValid, afterCap, ?_, firstFrame.trans secondFrame⟩
  · simp only [step, lbound, rbound, and_self, ↓reduceIte, readLeft, readRight, first, second]
  · simpa only [updated, WordBytes.exchangeLane, List.getElem_set_ne apart] using afterRep

theorem run_refines (order : WordBytes.Order) (view : View) (left right : Nat) (indices : List (Fin 4))
    (state : State) (items : List (BitVec 32)) (initial : state.valid = true) (cap : Writable state view)
    (represented : Represents state view items) (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right) :
    ∃ after, run order view left right indices state = (.ok (), after) ∧
      after.valid = true ∧ Writable after view ∧
      Represents after view (updated items left right (WordBytes.exchangeLanes order (items[left], items[right]) indices)) ∧
      Frame view state after := by
  induction indices generalizing state items with
  | nil =>
    refine ⟨state, rfl, initial, cap, ?_, Frame.refl _ _⟩
    simpa only [WordBytes.exchangeLanes, List.foldl_nil, updated_self items left right hl hr] using represented
  | cons index rest ih =>
    obtain ⟨middle, first, middleValid, middleCap, middleRep, firstFrame⟩ :=
      step_refines order state view items left right index initial cap represented hl hr apart
    obtain ⟨after, tail, afterValid, afterCap, afterRep, tailFrame⟩ :=
      ih middle _ middleValid middleCap middleRep (by simpa [updated] using hl) (by simpa [updated] using hr)
    refine ⟨after, ?_, afterValid, afterCap, ?_, firstFrame.trans tailFrame⟩
    · simp only [run, first, tail]
    · simpa only [updated_left _ _ _ _ _ apart, updated_right,
        updated_updated items left right _ _ apart, WordBytes.exchangeLanes, List.foldl_cons] using afterRep

/-- Four byte exchanges implement the word/list exchange for either byte order,
with no successful-intermediate-effect premise and a full outside-view frame. -/
theorem exchange_refines (order : WordBytes.Order) (state : State) (view : View) (items : List (BitVec 32))
    (left right : Nat) (initial : state.valid = true) (cap : Writable state view)
    (represented : Represents state view items) (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right) :
    ∃ after, run order view left right [0, 1, 2, 3] state = (.ok (), after) ∧
      after.valid = true ∧ Writable after view ∧
      Represents after view ((items.set left items[right]).set right items[left]) ∧ Frame view state after := by
  simpa only [WordBytes.exchange_four, updated] using
    run_refines order view left right [0, 1, 2, 3] state items initial cap represented hl hr apart

/-- Distinct contained words have disjoint byte addresses in this heap model.
This geometry alone does not establish native pointer provenance or noalias. -/
theorem byte_addresses_apart (state : State) (view : View) (left right : Nat)
    (initial : state.valid = true) (cap : Writable state view)
    (hl : left < view.length) (hr : right < view.length) (apart : left ≠ right) :
    ∃ cell, state.heap.lookup view.allocation = some cell ∧
      ∀ i j : Fin 4, cell.base + (view.address left).offset + i.val ≠ cell.base + (view.address right).offset + j.val := by
  obtain ⟨cell, found, _, _, _, _, separated⟩ := element_regions state view left right initial cap hl hr apart
  refine ⟨cell, found, ?_⟩
  intro i j
  have := i.isLt
  have := j.isLt
  omega

end Compiler.ZigAir.Memory.ByteExchange
