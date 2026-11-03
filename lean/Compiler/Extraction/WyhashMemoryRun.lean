/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.WyhashMemory
import Compiler.ZigAir.WyhashCallerInit

namespace Compiler.Extraction.WyhashMemory
open Compiler.ZigAir.Memory WyhashLocal

/-- Borrow the caller's initialized hasher. Update execution remains scoped
typed-region evaluation; its AIR instruction refinement is open. -/
def updates (inputs : List (List (BitVec 8))) (cells : Cells) : Except Fault (Unit × Cells) := do
  let cells ← WyhashHash.updates inputs cells
  .ok ((), cells)

def copy (source : Cells) (_ : Cells) : Except Fault (Unit × Cells) := do
  let cells ← shallowCopy source
  .ok ((), cells)

/-- The long-key branch allocates scratch even when length is at least 16.
Only the short buffered case initializes and uses its bytes. -/
def prepare (source : Cells) (length : Nat) (_ : Cells) : Except Fault ((Cells × ByteSlice.View × Nat) × Cells) := do
  let prepared ← WyhashBuffer.prepare source length
  .ok (prepared, if length < 16 then prepared.1 else [])

def finish (state : State) (source : Cells) : Except Fault (BitVec 64) × State :=
  match WyhashBuffer.readLength source with
  | .error fault => (.error fault, state)
  | .ok length =>
    if length > 48 then (.error .sourceBounds, state) else
    let (copied, middle) := CellFrame.create state objectType (copy source)
    match copied with
    | .error fault => (.error fault, middle)
    | .ok (_, copyId) =>
      match nativeOps.read source 5 with
      | .error fault => (.error fault, middle)
      | .ok total =>
        if total.toNat ≤ 16 then (.error .unsupported, middle) else
        let (prepared, after) := CellFrame.create middle WyhashBuffer.scratch.owner (prepare source length)
        match prepared with
        | .error fault => (.error fault, after)
        | .ok ((input, view, start), _) =>
          match after.heap.lookup copyId with
          | none => (.error .unallocated, after)
          | some cell => (WyhashFinalization.finish (ops after copyId cell) input view start cell.cells, after)

def runInitializedRaw (state : State) (self : Nat) (inputs : List (List (BitVec 8))) : Except Fault (BitVec 64) × State :=
  match CellFrame.borrow state self objectType (updates inputs) with
  | .error fault => (.error fault, state)
  | .ok (_, after) =>
    match after.heap.lookup self with
    | none => (.error .unallocated, after)
    | some cell => finish after cell.cells

/-- Execute the captured allocation/call/store order before borrowing the live
hasher. Key admission, updates and finalization still need AIR refinement. -/
def runRaw (state : State) (seed : BitVec 64) (inputs : List (List (BitVec 8))) : Except Fault (BitVec 64) × State :=
  let (initialized, after) := Compiler.ZigAir.WyhashCallerInit.run state seed
  match initialized with
  | .error fault => (.error fault, after)
  | .ok self => runInitializedRaw after self inputs

/-- Retire invocation locals on every outcome, retaining both reached cursors.
Resource rejection never supplies a digest or an allocator-OOM callback. -/
def run (state : State) (seed : BitVec 64) (inputs : List (List (BitVec 8))) : Except Fault (BitVec 64) × State :=
  let (result, after) := runRaw state seed inputs
  (result, cleanup state.nextId after)

theorem copy_valid (source : Cells) (offsets : List Nat) (target after : Cells)
    (valid : target.valid objectType = true) (ran : copyFields source offsets target = .ok after) :
    after.valid objectType = true := by
  induction offsets generalizing target with
  | nil => cases Except.ok.inj ran; exact valid
  | cons offset rest ih =>
    cases transferred : source.transferScalar objectType offset target objectType offset (.int false 64) with
    | error fault => simp only [copyFields, transferred, bind, Except.bind] at ran; cases ran
    | ok middle =>
      exact ih middle (Cells.transferScalar_valid _ _ _ _ _ _ _ _ valid transferred)
        (by simpa only [copyFields, transferred, bind, Except.bind] using ran)

theorem prepare_valid (source : Cells) (length : Nat) (input : Cells) (view : ByteSlice.View) (start : Nat)
    (ran : WyhashBuffer.prepare source length = .ok (input, view, start)) :
    (if length < 16 then input else []).valid WyhashBuffer.scratch.owner = true := by
  by_cases short : length < 16
  · rw [if_pos short]
    unfold WyhashBuffer.prepare at ran
    split at ran
    · contradiction
    · cases first : ByteSlice.copy source (WyhashBuffer.buffer (48 - (16 - length)) (16 - length))
          WyhashBuffer.scratch 0 0 (16 - length) [] with
      | error fault => simp only [first, bind, Except.bind] at ran; cases ran
      | ok middle =>
        cases second : ByteSlice.copy source (WyhashBuffer.buffer 0 length) WyhashBuffer.scratch 0 (16 - length) length middle with
        | error fault => simp only [first, second, bind, Except.bind] at ran; cases ran
        | ok after =>
          simp only [first, second, bind, Except.bind, Except.ok.injEq, Prod.mk.injEq] at ran
          obtain ⟨rfl, _, _⟩ := ran
          exact ByteSlice.copy_valid _ _ _ _ _ _ _ _ (ByteSlice.copy_valid _ _ _ _ _ _ _ _ rfl first) second
  · rw [if_neg short]; rfl

/-- Reuse complete local finalization. Local storage and permissions are
derived from allocation; the concrete heap-backed Ops discharge the callback
connection internally. This remains scoped evaluation, not an AIR trace. -/
theorem finish_verified (state : State) (source : Cells) (value : BitVec 64)
    (valid : state.valid = true) (ran : WyhashBuffer.run source = .ok value) :
    ∃ result after, finish state source = (result, after) ∧ StackFrame state after ∧
      (result = .ok value ∨ result = .error .outOfMemory) := by
  unfold WyhashBuffer.run at ran
  cases lengthRead : WyhashBuffer.readLength source with
  | error fault => simp only [lengthRead, bind, Except.bind] at ran; cases ran
  | ok length =>
    simp only [lengthRead, bind, Except.bind] at ran
    by_cases large : length > 48
    · simp only [if_pos large] at ran; cases ran
    · rw [if_neg large] at ran
      cases copied : shallowCopy source with
      | error fault => simp only [copied] at ran; cases ran
      | ok copiedCells =>
        simp only [copied] at ran
        have copiedValid := copy_valid source [0, 8, 16, 24, 32, 40] [] copiedCells rfl copied
        obtain ⟨copyResult, middle, createdCopy, copyStack, copyOutcome⟩ := StackFrame.create state objectType ⟨104, 8⟩
          (copy source) () copiedCells valid rfl (by decide)
          (by simp only [copy, copied, bind, Except.bind]) copiedValid
        rcases copyOutcome with failed | ⟨success, copyCell, copyFound, copyType, copyCells, copyWritable⟩
        · rw [failed] at createdCopy
          exact ⟨_, _, by simp only [finish, lengthRead, if_neg large, createdCopy], copyStack, Or.inr rfl⟩
        · rw [success] at createdCopy
          cases totalRead : nativeOps.read source 5 with
          | error fault => simp only [totalRead] at ran; cases ran
          | ok total =>
            simp only [totalRead] at ran
            by_cases small : total.toNat ≤ 16
            · simp only [if_pos small] at ran; cases ran
            · rw [if_neg small] at ran
              cases prepared : WyhashBuffer.prepare source length with
              | error fault => simp only [prepared] at ran; cases ran
              | ok triple =>
                obtain ⟨input, view, start⟩ := triple
                simp only [prepared] at ran
                obtain ⟨scratchResult, after, createdScratch, scratchStack, scratchOutcome⟩ :=
                  StackFrame.create middle WyhashBuffer.scratch.owner ⟨16, 1⟩ (prepare source length)
                    (input, view, start) (if length < 16 then input else []) copyStack.valid rfl (by decide)
                    (by simp only [prepare, prepared, bind, Except.bind]) (prepare_valid source length input view start prepared)
                rcases scratchOutcome with failed | ⟨success, scratchCell, scratchFound, scratchType, scratchCells, scratchWritable⟩
                · rw [failed] at createdScratch
                  exact ⟨_, _, by simp only [finish, lengthRead, if_neg large, createdCopy, totalRead, if_neg small, createdScratch],
                    copyStack.trans scratchStack, Or.inr rfl⟩
                · rw [success] at createdScratch
                  have retained := scratchStack.old_lookup state.nextId copyCell copyFound
                  let frame := CellFrame.of_valid after state.nextId copyCell ⟨104, 8⟩ scratchStack.valid retained
                    (copyType ▸ rfl) (by decide) copyWritable
                  have concrete : ops after state.nextId copyCell = nativeOps := ops_eq frame copyType rfl
                  refine ⟨_, _, ?_, copyStack.trans scratchStack, Or.inl rfl⟩
                  simp only [finish, lengthRead, if_neg large, createdCopy, totalRead, if_neg small, createdScratch, retained]
                  rw [concrete, copyCells, ran]

theorem runInitializedRaw_verified {caller state : State} (stack : StackFrame caller state)
    (self : Nat) (cell : Allocation) (found : state.heap.lookup self = some cell)
    (typed : cell.type = objectType) (contents : cell.cells = WyhashUpdate.initialCells (WyhashUpdate.seedState 0))
    (writable : cell.writable = true) (fresh : caller.nextId ≤ self) (inputs : List (List (BitVec 8)))
    (long : 16 < inputs.flatten.length) (bounded : inputs.flatten.length < addressLimit)
    (budgets : ∀ input ∈ inputs, input.length + 48 < addressLimit) :
    ∃ result after, runInitializedRaw state self inputs = (result, after) ∧ StackFrame caller after ∧
      (result = .ok (WyhashHash.digest inputs) ∨ result = .error .outOfMemory) := by
  obtain ⟨cells, length, updated, invariant⟩ := WyhashHash.updates_verified inputs
    (WyhashUpdate.initialCells (WyhashUpdate.seedState 0)) 0 0 (WyhashUpdate.init_invariant 0)
    (by simpa only [Nat.zero_add] using bounded) budgets
  let frame := CellFrame.of_valid state self cell ⟨104, 8⟩ stack.valid found (typed ▸ rfl) (by decide) writable
  have borrowed := frame.borrow_eq (updates inputs) () cells
    (by simp only [updates, show frame.cell.cells = cell.cells from rfl, contents, updated, bind, Except.bind])
    (typed ▸ invariant.core.valid)
  rw [show frame.cell.type = objectType from typed] at borrowed
  have updatedStack := stack.install self frame cells fresh (typed ▸ invariant.core.valid)
  have localRun := WyhashHash.run_digest inputs long bounded budgets
  simp only [WyhashHash.run, WyhashUpdate.init_eq, updated, bind, Except.bind] at localRun
  obtain ⟨result, after, finished, framed, outcome⟩ := finish_verified (frame.install cells) cells _ updatedStack.valid localRun
  exact ⟨_, _, by simp only [runInitializedRaw, borrowed, frame.lookup cells, finished], updatedStack.trans framed, outcome⟩

theorem runRaw_verified (state : State) (inputs : List (List (BitVec 8)))
    (valid : state.valid = true) (long : 16 < inputs.flatten.length) (bounded : inputs.flatten.length < addressLimit)
    (budgets : ∀ input ∈ inputs, input.length + 48 < addressLimit) :
    ∃ result after, runRaw state 0 inputs = (result, after) ∧ StackFrame state after ∧
      (result = .ok (WyhashHash.digest inputs) ∨ result = .error .outOfMemory) := by
  obtain ⟨initialized, middle, ran, initFrame, outcome⟩ := Compiler.ZigAir.WyhashCallerInit.run_verified state 0 valid
  rcases outcome with failure | ⟨success, cell, found, typed, contents, writable⟩
  · rw [failure] at ran
    exact ⟨.error .outOfMemory, middle, by simp only [runRaw, ran], initFrame, Or.inr rfl⟩
  · rw [success] at ran
    obtain ⟨result, after, finished, frame, resultKind⟩ := runInitializedRaw_verified initFrame state.nextId cell found
      typed contents writable (Nat.le_refl _) inputs long bounded budgets
    exact ⟨result, after, by simpa only [runRaw, ran] using finished, frame, resultKind⟩

/-- No chosen digest, successful run, poststate or extra allocation budget is
a premise. The only failure on admitted long inputs is explicit exhaustion. -/
theorem run_verified (state : State) (inputs : List (List (BitVec 8)))
    (valid : state.valid = true) (long : 16 < inputs.flatten.length) (bounded : inputs.flatten.length < addressLimit)
    (budgets : ∀ input ∈ inputs, input.length + 48 < addressLimit) :
    (run state 0 inputs).2.valid = true ∧ (run state 0 inputs).2.heap = state.heap ∧
      ((run state 0 inputs).1 = .ok (WyhashHash.digest inputs) ∨ (run state 0 inputs).1 = .error .outOfMemory) := by
  obtain ⟨result, after, ran, frame, outcome⟩ := runRaw_verified state inputs valid long bounded budgets
  simpa only [run, ran] using And.intro frame.cleanup_valid (And.intro frame.cleanup_heap outcome)

end Compiler.Extraction.WyhashMemory
