/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortMemory
import Compiler.ZigAir.MemoryWordFrame

/-! Memory interpretation of the same extracted loop definitions used by the
value model. Primitive faults, exhausted observations and partial states are
retained. Native byte exchange/copy and allocator refinement remain open. -/
namespace Compiler.Extraction.InsertionSort.Heap
open Compiler.Algebraic Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

inductive Fault where
  | memory (reason : Compiler.ZigAir.Memory.Fault)
  | incomplete | indexWidth
  deriving DecidableEq, Repr

def read (view : View) (state : State) (index : Nat) : Except Fault NodeId :=
  if index < view.length then
    match elementPointer state view.buffer index with
    | .error reason => .error (.memory reason)
    | .ok pointer => match load state pointer with
      | .error reason => .error (.memory reason)
      | .ok (.scalar (.int false 32 value)) => .ok (BitVec.ofInt 32 value)
      | .ok _ => .error (.memory .malformed)
  else .error (.memory .sourceBounds)

def exchange (view : View) (state : State) (left right : Nat) : Except Fault Unit × State :=
  let (result, after) := WordArray.exchange state view left right
  (result.mapError Fault.memory, after)

def operations (view : View) : Operations State Fault :=
  ⟨read view, exchange view, .incomplete⟩

def run (state : State) (view : View) : Except Fault Unit × State :=
  if view.length < addressLimit then runUsing (operations view) view.length state
  else (.error .indexWidth, state)

theorem read_represents (state : State) (view : View) (items : List NodeId) (index : Nat)
    (initial : state.valid = true) (cap : Writable state view) (represented : Represents state view items)
    (inside : index < items.length) : read view state index = .ok items[index] := by
  have bound : index < view.length := by simpa only [represented.1] using inside
  simp [read, bound, element_pointer state view index initial cap bound, represented.2 index inside, number]

theorem exchange_refines (state : State) (view : View) (items : List NodeId) (j : Nat)
    (initial : state.valid = true) (cap : Writable state view) (represented : Represents state view items)
    (inside : j + 1 < items.length) :
    ∃ after, exchange view state (j + 1) j = (.ok (), after) ∧
      after.valid = true ∧ Writable after view ∧
      Represents after view ((items.set (j + 1) items[j]).set j items[j + 1]) ∧ Frame view state after := by
  obtain ⟨after, ran, valid, writable, values, _⟩ :=
    adjacent_memory_exchange state view items j initial cap represented inside
  exact ⟨after, by simp [exchange, ran, Except.mapError], valid, writable, values,
    exchange_frame state after view items (j + 1) j initial cap represented inside (by omega) ran⟩

end Compiler.Extraction.InsertionSort.Heap
