/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InsertionSortHeapProofs
import Compiler.ZigAir.MemoryWordSwapInvocation
import Compiler.ZigAir.MemoryWordCallFrame

/-! The extracted caller's shared loops, with the actual captured swap as the
exchange operation. A call budget is an observation bound: suspension remains
incomplete and keeps its exact partial heap, including private stack storage.
Completed invocations keep allocator effects and perform their normal cleanup.
No source/native call or backend correspondence is claimed here. -/
namespace Compiler.Extraction.InsertionSort.Captured
open Compiler.Algebraic Compiler.ZigAir Compiler.ZigAir.Memory Compiler.ZigAir.MemoryAir
open Compiler.ZigAir.Memory.WordArray

def outcome : Invocation → Except Heap.Fault Unit × State
  | .finished (.error reason) after => (.error (.memory reason), after)
  | .finished (.ok (.scalar .unit)) after => (.ok (), after)
  | .finished (.ok _) after => (.error (.memory .malformed), after)
  | .suspended _ _ _ config => (.error .incomplete, config.state)

def exchange (budget : Nat) (view : View) (state : State) (left right : Nat) : Except Heap.Fault Unit × State :=
  if left < view.length ∧ right < view.length then
    match elementPointer state view.buffer left with
    | .error reason => (.error (.memory reason), state)
    | .ok a => match elementPointer state view.buffer right with
      | .error reason => (.error (.memory reason), state)
      | .ok b => outcome (GeneratedMemory.fn_swap_u32.runFuel budget [a, b] state)
  else (.error (.memory .sourceBounds), state)

def operations (budget : Nat) (view : View) : Operations State Heap.Fault :=
  ⟨Heap.read view, exchange budget view, .incomplete⟩

def run (budget : Nat) (state : State) (view : View) : Except Heap.Fault Unit × State :=
  if view.length < addressLimit then runUsing (operations budget view) view.length state
  else (.error .indexWidth, state)

/-- A finite bound exists, and every larger observation has this exact result.
This is a proof predicate, not a noncomputable implementation of a call. -/
def Settles (action : Nat → α) (result : α) : Prop := ∃ budget, ∀ fuel, budget ≤ fuel → action fuel = result

theorem exchange_of_view (budget : Nat) (view : View) (state : State) (left right : Nat)
    (initial : state.valid = true) (cap : Writable state view)
    (hl : left < view.length) (hr : right < view.length) :
    exchange budget view state left right =
      outcome (GeneratedMemory.fn_swap_u32.runFuel budget (MemoryWordSwap.arguments view left right) state) := by
  simp only [exchange, hl, hr, and_self, ↓reduceIte, element_pointer state view left initial cap hl,
    element_pointer state view right initial cap hr, MemoryWordSwap.arguments]

theorem invocation_settles (program : WordPairProgram) (args : List Value) (state after : State)
    (budget : Nat) (result : Except Memory.Fault Value)
    (done : program.runFuel budget args state = .finished result after) :
    ∀ fuel, budget ≤ fuel → program.runFuel fuel args state = .finished result after := by
  intro fuel enough
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  rw [← WordPairProgram.resume_add, done, Invocation.resume_finished]

/-- A captured adjacent call either swaps the words or reports allocation
exhaustion without changing caller memory. No successful-call or fuel premise
is supplied; successful calls advance the allocation ID exactly once. -/
theorem exchange_refines (view : View) (state : State) (items : List NodeId) (j : Nat)
    (related : Heap.Related view state items) (inside : j + 1 < items.length) :
    ∃ result after, Settles (fun budget => exchange budget view state (j + 1) j) (result, after) ∧
      HeapFrame view state after ∧
      ((result = .error (.memory .outOfMemory) ∧ after = state) ∨
       (result = .ok () ∧ Heap.Related view after ((items.set (j + 1) items[j]).set j items[j + 1]) ∧
        after.nextId = state.nextId + 1)) := by
  obtain ⟨budget, result, after, done, valid, effect⟩ := MemoryWordSwap.swap_refines state view items (j + 1) j
    related.valid related.writable related.values inside (by omega) (by omega)
  have stable := invocation_settles GeneratedMemory.fn_swap_u32 (MemoryWordSwap.arguments view (j + 1) j)
    state after budget result done
  have settled : Settles (fun fuel => exchange fuel view state (j + 1) j) (outcome (.finished result after)) := by
    refine ⟨budget, fun fuel enough => ?_⟩
    change exchange fuel view state (j + 1) j = _
    rw [exchange_of_view fuel view state (j + 1) j related.valid related.writable
      (by simpa only [related.values.1] using inside) (by have := related.values.1; omega), stable fuel enough]
  rcases effect with ⟨failed, same⟩ | ⟨base, direct, rfl, rfl, _, writable, values, frame⟩
  · subst after
    rw [failed] at settled
    exact ⟨_, state, settled, HeapFrame.refl view state, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨_, _, settled, frame.heapFrame.heap_eq rfl, Or.inr ⟨rfl, ⟨valid, writable, values⟩, rfl⟩⟩

end Compiler.Extraction.InsertionSort.Captured
