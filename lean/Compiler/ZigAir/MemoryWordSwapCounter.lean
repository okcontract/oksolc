/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.ZigAir.MemoryWordSwapBody

/-! One concrete invocation-local counter prefix, using the existing heap.
Caller writes commute with this prefix; counter writes retain the complete
caller heap. Allocation and cleanup never rewind the allocator cursors. -/
namespace Compiler.ZigAir.MemoryWordSwap
open Memory MemoryAir
open Memory.WordArray (View Writable Represents Frame)
open MemoryFill (size size_valid size_typed counter)

def counterCell (base index : Nat) : Allocation := ⟨base, usize, [(0, size index)], true, true⟩
def withCounter (base index : Nat) (caller : State) : State :=
  prepend caller.nextId (counterCell base index) (caller.nextId + 1) (base + 8) caller

theorem counter_found (base index : Nat) (caller : State) :
    (withCounter base index caller).heap.lookup caller.nextId = some (counterCell base index) := by
  simp [withCounter, prepend, Heap.lookup_cons]

theorem counter_store (base index next : Nat) (caller : State)
    (initial : caller.valid = true) (live : (withCounter base index caller).valid = true) (bound : next < addressLimit) :
    store (withCounter base index caller) (counter ⟨caller.nextId, 0⟩) (size next) = .ok (withCounter base next caller) := by
  obtain ⟨after, stored⟩ := root_store_total (withCounter base index caller) caller.nextId (counterCell base index)
    (size next) ⟨8, 8⟩ live (counter_found base index caller) rfl rfl (size_valid next bound) rfl (by decide)
  obtain ⟨_, _, _, layout, cell, contents, same, _, shaped, accessed, written, afterShape⟩ :=
    store_success (withCounter base index caller) _ (size next) after stored
  cases same
  have found := (access_success_region (withCounter base index caller) ⟨caller.nextId, 0⟩ layout true cell accessed).1
  have cellEq : cell = counterCell base index := Option.some.inj (found.symm.trans (counter_found base index caller))
  subst cell
  have writeValue : (counterCell base index).cells.write (counterCell base index).type 0 (size next) =
      .ok [(0, size next)] := by
    have basic := Cells.write_single (counterCell base index).cells usize 0 (size next)
      (size_valid next bound) (by rfl) (by
        change (decide (some usize = some usize) && (size next).valid) = true
        rw [size_valid next bound]; rfl) rfl
    simpa [counterCell, Cells.set] using basic
  have contentsEq := Except.ok.inj (written.symm.trans writeValue)
  subst contents
  have absent : ∀ entry ∈ caller.heap, entry.1 ≠ caller.nextId :=
    fun entry present => Nat.ne_of_lt (valid_heap_ids caller initial entry present)
  have afterEq : after = withCounter base next caller := by
    rw [afterShape]
    simp only [withCounter, prepend, Heap.replace_cons, ↓reduceIte,
      Heap.replace_absent caller.heap caller.nextId _ absent, counterCell]
  simpa only [afterEq] using stored

theorem counter_read (base index : Nat) (caller : State)
    (initial : caller.valid = true) (live : (withCounter base index caller).valid = true) (bound : index < addressLimit) :
    load (withCounter base index caller) (counter ⟨caller.nextId, 0⟩) = .ok (size index) :=
  load_after_store _ _ _ _ (counter_store base index index caller initial live bound)

theorem view_older (state : State) (view : View) (initial : state.valid = true) (cap : Writable state view) :
    view.allocation < state.nextId := by
  obtain ⟨_, cell, found, _, _, _⟩ := cap
  exact (valid_lookup state view.allocation cell initial found).1

theorem counter_writable (base index : Nat) (caller : State) (view : View)
    (initial : caller.valid = true) (cap : Writable caller view) : Writable (withCounter base index caller) view := by
  have apart := Nat.ne_of_lt (view_older caller view initial cap)
  obtain ⟨extent, cell, found, typed, writable, bound⟩ := cap
  refine ⟨extent, cell, ?_, typed, writable, bound⟩
  simpa only [withCounter, prepend, Heap.lookup_cons, if_neg apart.symm] using found

theorem counter_represents (base index : Nat) (caller : State) (view : View) (items : List (BitVec 32))
    (initial : caller.valid = true) (cap : Writable caller view) (represented : Represents caller view items) :
    Represents (withCounter base index caller) view items := by
  have apart := Nat.ne_of_lt (view_older caller view initial cap)
  refine ⟨represented.1, ?_⟩
  intro i inside
  rw [withCounter, WordArray.View.pointer, load_prepend _ _ _ _ _ _ _ _ _ apart]
  exact represented.2 i inside

theorem counter_cleanup (base index : Nat) (caller : State) (initial : caller.valid = true) :
    (cleanup caller.nextId (withCounter base index caller)).heap = caller.heap :=
  cleanup_prepend caller (counterCell base index) (caller.nextId + 1) (base + 8) initial rfl

/-- Even failed exchange steps commute with the separate counter allocation;
the same partial caller effects survive on both sides. -/
theorem step_prepend (order : WordBytes.Order) (state : State) (id : Nat) (cell : Allocation)
    (nextId nextAddress : Nat) (view : View) (left right : Nat) (index : Fin 4) (apart : view.allocation ≠ id) :
    ByteExchange.step order (prepend id cell nextId nextAddress state) view left right index =
      ((ByteExchange.step order state view left right index).1,
        prepend id cell nextId nextAddress (ByteExchange.step order state view left right index).2) := by
  simp only [ByteExchange.step, View.pointer]
  split
  · rw [WordByteView.read_prepend _ _ _ _ _ _ _ _ _ _ apart,
      WordByteView.read_prepend _ _ _ _ _ _ _ _ _ _ apart]
    cases first : WordByteView.read order state (.pointer (.pointer true false WordArray.word) (view.address left)) index.val with
    | error reason => rfl
    | ok a =>
      cases second : WordByteView.read order state (.pointer (.pointer true false WordArray.word) (view.address right)) index.val with
      | error reason => rfl
      | ok b =>
        dsimp only
        rw [WordByteView.write_prepend order state id cell nextId nextAddress true false (view.address left) index.val b apart]
        cases third : WordByteView.write order state (.pointer (.pointer true false WordArray.word) (view.address left)) index.val b with
        | error reason => rfl
        | ok middle =>
          simp only [Except.map]
          rw [WordByteView.write_prepend order middle id cell nextId nextAddress true false (view.address right) index.val a apart]
          cases fourth : WordByteView.write order middle (.pointer (.pointer true false WordArray.word) (view.address right)) index.val a <;> rfl
  · rfl

theorem lane_counter_refines (args : List Value) (env : Env) (caller : State) (base : Nat) (view : View)
    (items : List (BitVec 32)) (left right : Nat) (index : Fin 4)
    (initial : caller.valid = true) (live : (withCounter base index.val caller).valid = true)
    (cap : Writable caller view) (represented : Represents caller view items)
    (hl : left < items.length) (hr : right < items.length) (apart : left ≠ right)
    (locals : Locals env view left right ⟨caller.nextId, 0⟩) (h13 : env 13 = some (size index.val)) :
    ∃ after nextEnv, lane.eval semantics args env (withCounter base index.val caller) =
        .jumped 14 (.scalar .unit) nextEnv (withCounter base index.val after) ∧
      Locals nextEnv view left right ⟨after.nextId, 0⟩ ∧ nextEnv 13 = some (size index.val) ∧
      after.valid = true ∧ (withCounter base index.val after).valid = true ∧ Writable after view ∧
      Represents after view (ByteExchange.updated items left right (WordBytes.exchangeLane .little (items[left], items[right]) index)) ∧
      Frame view caller after := by
  obtain ⟨after, direct, valid, writable, rep, frame⟩ :=
    ByteExchange.step_refines .little caller view items left right index initial cap represented hl hr apart
  obtain ⟨actual, nextEnv, evaluated, nextLocals, nextIndex, ran, actualValid, _, _, _⟩ :=
    lane_refines args env (withCounter base index.val caller) view items left right index ⟨caller.nextId, 0⟩
      live (counter_writable base index.val caller view initial cap)
      (counter_represents base index.val caller view items initial cap represented) hl hr apart locals h13
  have prefixed := step_prepend .little caller caller.nextId (counterCell base index.val) (caller.nextId + 1) (base + 8)
    view left right index (Nat.ne_of_lt (view_older caller view initial cap))
  change ByteExchange.step .little (withCounter base index.val caller) view left right index = _ at prefixed
  rw [direct, ran] at prefixed
  have same : actual = withCounter base index.val after := by
    have heap := (Prod.mk.inj prefixed).2
    simpa only [withCounter, frame.nextId] using heap
  subst actual
  exact ⟨after, nextEnv, evaluated, by simpa only [frame.nextId] using nextLocals,
    nextIndex, valid, actualValid, writable, rep, frame⟩

end Compiler.ZigAir.MemoryWordSwap
