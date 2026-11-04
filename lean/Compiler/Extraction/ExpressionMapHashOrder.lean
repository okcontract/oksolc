/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapHashBytes
import Compiler.Extraction.WyhashMemoryRun

namespace Compiler.Extraction.ExpressionMap.HashBytes.Ordered
open Compiler.ZigAir.Memory Compiler.Extraction.Cache
open WyhashLocal

/-- A scalar field or the argument slice. The captured caller determines this
list; each entry executes its existing concrete byte-view program. -/
abbrev Input := Option Field

def image (key : Key) : Input → List (BitVec 8)
  | some field => field.image key
  | none => HashInput.arguments key.arguments

def observe (state : State) (keyId : Nat) : Input → Except Fault (List (BitVec 8)) × State
  | some field => (read state keyId field, state)
  | none => argumentBytes state keyId

/-- Read one view and immediately update the live hasher, before evaluating
the next view. Update internals still use the scoped cell evaluator; this does
not assert that the update AIR body has been translated. -/
def updates (keyId self : Nat) : List Input → State → Except Fault Unit × State
  | [], state => (.ok (), state)
  | input :: rest, state =>
    let (bytes, viewed) := observe state keyId input
    match bytes with
    | .error fault => (.error fault, viewed)
    | .ok bytes =>
      match CellFrame.borrow viewed self objectType (WyhashMemory.updates [bytes]) with
      | .error fault => (.error fault, viewed)
      | .ok (_, updated) => updates keyId self rest updated

def finish (state : State) (self : Nat) : Except Fault (BitVec 64) × State :=
  match state.heap.lookup self with
  | none => (.error .unallocated, state)
  | some cell => WyhashMemory.finish state cell.cells

/-- The initialization cut precedes every view/update pair. Finalization reads
the current live hasher after the last update; no precollected byte list or
precomputed final cells bypass these state transitions. Key-copy admission and
update/finalization AIR refinement remain separate obligations. -/
def run (state : State) (keyId : Nat) (order : List Input) : Except Fault (BitVec 64) × State :=
  let (initialized, middle) := Compiler.ZigAir.WyhashCallerInit.run state 0
  match initialized with
  | .error fault => (.error fault, middle)
  | .ok self =>
    let (updated, after) := updates keyId self order middle
    match updated with
    | .error fault => (.error fault, after)
    | .ok () => finish after self

theorem observe_verified (state : State) (keyId : Nat) (key : Key) (source : WordArray.View)
    (input : Input) (valid : state.valid = true) (binding : HashKey.Binding state keyId key (source.address 0))
    (represented : WordArray.Represents state source key.arguments) (bounded : source.length * 4 < addressLimit) :
    ∃ result after, observe state keyId input = (result, after) ∧ StackFrame state after ∧
      (result = .ok (image key input) ∨ result = .error .outOfMemory) := by
  cases input with
  | none =>
    obtain ⟨result, after, ran, frame, _, outcome⟩ := argumentBytes_verified state keyId key source valid binding represented bounded
    exact ⟨result, after, ran, frame, outcome⟩
  | some field =>
    refine ⟨.ok (field.image key), state, ?_, StackFrame.refl state valid, Or.inl rfl⟩
    rw [observe, read_verified state keyId key (source.address 0) field valid binding (by have := represented.1; omega)]

/-- One induction composes all view calls and updates. The original key and
word storage survive because only the invocation's fresh hasher is mutated.
Successful execution is the same logical update sequence used by the existing
hash theorem. A view's allocation failure retains every earlier update. -/
theorem updates_verified (caller : State) (keyId self : Nat) (key : Key) (source : WordArray.View)
    (binding : HashKey.Binding caller keyId key (source.address 0))
    (represented : WordArray.Represents caller source key.arguments)
    (sourceBound : source.length * 4 < addressLimit) (fresh : caller.nextId ≤ self)
    (order : List Input) (state : State) (cell : Allocation) (total length : Nat)
    (stack : StackFrame caller state) (found : state.heap.lookup self = some cell)
    (typed : cell.type = objectType) (writable : cell.writable = true)
    (invariant : WyhashUpdate.Invariant cell.cells total length)
    (sumBound : total + (order.map (image key)).flatten.length < addressLimit)
    (budgets : ∀ input ∈ order, (image key input).length + 48 < addressLimit) :
    ∃ result after, updates keyId self order state = (result, after) ∧ StackFrame caller after ∧
      (result = .error .outOfMemory ∨ result = .ok () ∧ ∃ finalCell,
        after.heap.lookup self = some finalCell ∧ finalCell.type = objectType ∧ finalCell.writable = true ∧
        WyhashHash.updates (order.map (image key)) cell.cells = .ok finalCell.cells) := by
  induction order generalizing state cell total length with
  | nil => exact ⟨.ok (), state, rfl, stack, Or.inr ⟨rfl, cell, found, typed, writable, rfl⟩⟩
  | cons input rest ih =>
    have size : ((input :: rest).map (image key)).flatten.length =
        (image key input).length + (rest.map (image key)).flatten.length := by simp
    obtain ⟨bytes, viewed, observed, viewFrame, success | failure⟩ := observe_verified state keyId key source input
      stack.valid (binding.extend stack) (represented.extend stack) sourceBound
    · obtain ⟨cells, buffered, updated, nextInvariant⟩ := WyhashUpdate.update_verified
        (ByteSlice.cellsFrom (image key input) 0) cell.cells (ByteSlice.imageView (image key input))
        (fun i => (image key input)[i]?.getD 0) (ByteSlice.array_geometry (image key input).length)
        (ByteSlice.image_represents (image key input)) total length invariant
        (by change total + (image key input).length < addressLimit; rw [size] at sumBound; omega)
        (budgets input (by simp))
      let frame := CellFrame.of_valid viewed self cell ⟨104, 8⟩ viewFrame.valid
        (viewFrame.old_lookup self cell found) (typed ▸ rfl) (by decide) writable
      have borrowed := frame.borrow_eq (WyhashMemory.updates [(image key input)]) () cells
        (by simp only [WyhashMemory.updates, WyhashHash.updates,
          show frame.cell.cells = cell.cells from rfl, updated, bind, Except.bind])
        (typed ▸ nextInvariant.core.valid)
      rw [show frame.cell.type = objectType from typed] at borrowed
      have nextStack := (stack.trans viewFrame).install self frame cells fresh (typed ▸ nextInvariant.core.valid)
      have tailBound : total + (image key input).length + (rest.map (image key)).flatten.length < addressLimit := by
        rw [size] at sumBound; omega
      obtain ⟨result, after, continued, finalStack, failed | ⟨succeeded, finalCell, finalFound, finalType, finalWritable, finalRun⟩⟩ :=
        ih (frame.install cells) { cell with cells } (total + (image key input).length) buffered nextStack
          (frame.lookup cells) typed writable nextInvariant tailBound (fun i inside => budgets i (by simp [inside]))
      · exact ⟨result, after, by simp only [updates, observed, success, borrowed, continued], finalStack, Or.inl failed⟩
      · refine ⟨result, after, by simp only [updates, observed, success, borrowed, continued], finalStack,
          Or.inr ⟨succeeded, finalCell, finalFound, finalType, finalWritable, ?_⟩⟩
        simp only [List.map_cons, WyhashHash.updates, updated, bind, Except.bind]
        exact finalRun
    · exact ⟨.error .outOfMemory, viewed, by simp only [updates, observed, failure], stack.trans viewFrame, Or.inl rfl⟩

theorem run_verified (state : State) (keyId : Nat) (key : Key) (source : WordArray.View) (order : List Input)
    (valid : state.valid = true) (binding : HashKey.Binding state keyId key (source.address 0))
    (represented : WordArray.Represents state source key.arguments) (sourceBound : source.length * 4 < addressLimit)
    (long : 16 < (order.map (image key)).flatten.length)
    (bounded : (order.map (image key)).flatten.length < addressLimit)
    (budgets : ∀ input ∈ order, (image key input).length + 48 < addressLimit) :
    ∃ result after, run state keyId order = (result, after) ∧ StackFrame state after ∧
      (result = .ok (WyhashHash.digest (order.map (image key))) ∨ result = .error .outOfMemory) := by
  obtain ⟨initialized, middle, created, initFrame, failed | ⟨success, cell, found, typed, contents, writable⟩⟩ :=
    Compiler.ZigAir.WyhashCallerInit.run_verified state 0 valid
  · rw [failed] at created
    exact ⟨.error .outOfMemory, middle, by simp only [run, created], initFrame, Or.inr rfl⟩
  · rw [success] at created
    have invariant : WyhashUpdate.Invariant cell.cells 0 0 := contents ▸ WyhashUpdate.init_invariant 0
    obtain ⟨updated, reached, updatesRun, updateFrame, failure | ⟨finished, finalCell, finalFound, finalType, finalWritable, logical⟩⟩ :=
      updates_verified state keyId state.nextId key source binding represented sourceBound (Nat.le_refl _) order
        middle cell 0 0 initFrame found typed writable invariant (by simpa using bounded) budgets
    · exact ⟨.error .outOfMemory, reached, by simp only [run, created, updatesRun, failure], updateFrame, Or.inr rfl⟩
    · have final := WyhashHash.run_digest (order.map (image key)) long bounded
        (by intro bytes member; obtain ⟨input, inside, rfl⟩ := List.mem_map.mp member; exact budgets input inside)
      simp only [WyhashHash.run, WyhashUpdate.init_eq, ← contents, logical, bind, Except.bind] at final
      obtain ⟨result, after, finishedRun, finishFrame, outcome⟩ :=
        WyhashMemory.finish_verified reached finalCell.cells _ updateFrame.valid final
      exact ⟨result, after, by simp only [run, created, updatesRun, finished, finish, finalFound, finishedRun],
        updateFrame.trans finishFrame, outcome⟩

end Compiler.Extraction.ExpressionMap.HashBytes.Ordered
