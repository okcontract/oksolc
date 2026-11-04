/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionFields

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open AssemblyClone (Value)

/-- Admit the input descriptor and check the reached resource frame and live
success locals. The complete execution proves the output's field correspondence;
its key/value equality is not an output admission check. This does not
insert checks into Zig or assert that all native calls pass them. Native field
assignment and container representation remain compiler obligations. -/
def admitOutput (source : View) (key : Key) (value : Word) (before : World (Publication.Effects σ))
    (input : Value Metadata) (outcome : Option Storage.Outcome) (owner : Storage.State)
    (normalized : ArgumentSlice) (after : State Metadata σ) : Bool :=
  decide (keyCode.run input.item normalized.items key.sequence = some key) &&
  decide ((if input.item.kind == 2 then input.item.data else value) = value) &&
  decide (source.length = 0 ∨ (memory after).memory.heap.lookup source.allocation = before.memory.memory.heap.lookup source.allocation) &&
  (outcome != some .success || (after.item.object.isSome && after.item.clone.value.isSome && (arguments normalized owner after).isSome))

def projected (cells : List Storage.Cell) (before : World (Publication.Effects σ)) (key : Key)
    (candidate : Storage.Cell) (owner : Storage.State) (after : State Metadata σ) : World (Publication.Effects σ) :=
  ⟨{ Interner.InsertionExecution.project cells before.graph.table candidate key owner with
       allocationCursor := before.graph.allocationCursor }, memory after⟩

/-- One execution of the production insertion control tree. Semantic rejection
retains its reached state, including partial allocations and private effects.
Ordinary OOM uses the source's actual defers; no synthetic rollback is added. -/
def body (ops : Operations σ) (allocator : Nat) (source : View) (meaning : Meaning) (input : Value Metadata)
    (key : Key) (normalized : ArgumentSlice) (deterministic : Bool) (cells : List Storage.Cell)
    (before : World (Publication.Effects σ)) : Except Fault NodeId × World (Publication.Effects σ) :=
  let ran := execution ops allocator source meaning input key normalized deterministic cells before
  let value := (key.eval meaning before.graph.read).getD 0
  let candidate := cell input key normalized value ran.1.2 ran.2
  let reached := projected cells before key candidate ran.1.2 ran.2
  match ran.1.1 with
  | .error _ => (.error (.language .safetyFault), reached)
  | .ok outcome =>
    if admitOutput source key value before input outcome ran.1.2 normalized ran.2 then
      ((Interner.insertionOutcome cells outcome).mapError Fault.language, reached)
    else (.error (.language .safetyFault), reached)

def insert (ops : Operations σ) (allocator : Nat) (source : View) (meaning : Meaning)
    (input : Value Metadata) (key : Key) (normalized : ArgumentSlice) (deterministic : Bool) :
    GraphAction (Publication.Effects σ) NodeId := fun before =>
  match before.graph.representatives with
  | none => (.error (.language .safetyFault), before)
  | some cells => body ops allocator source meaning input key normalized deterministic cells before

theorem execution_valid (ops : Operations σ) (allocator : Nat) (source : View) (meaning : Meaning)
    (input : Value Metadata) (key : Key) (normalized : ArgumentSlice) (deterministic : Bool)
    (cells : List Storage.Cell) (before : World (Publication.Effects σ)) (outcome : Option Storage.Outcome)
    (initial : Valid before.memory) (admitted : Admitted ops.arguments)
    (completed : (execution ops allocator source meaning input key normalized deterministic cells before).1.1 = .ok outcome) :
    StateValid (execution ops allocator source meaning input key normalized deterministic cells before).2 := by
  exact Storage.Program.execute_preserves _ _ _ StateValid (callbacks_preserve ops allocator cells.length source input key normalized _ admitted)
    _ _ initial outcome completed

theorem body_memory (ops : Operations σ) (allocator : Nat) (source : View) (values : List NodeId)
    (meaning : Meaning) (input : Value Metadata) (key : Key) (normalized : ArgumentSlice) (deterministic : Bool)
    (cells : List Storage.Cell) (before : World (Publication.Effects σ)) (initial : Good source values before)
    (admitted : Admitted ops.arguments)
    (ordinaryResult : ordinary (body ops allocator source meaning input key normalized deterministic cells before).1 = true) :
    Good source values (body ops allocator source meaning input key normalized deterministic cells before).2 := by
  cases ran : execution ops allocator source meaning input key normalized deterministic cells before with
  | mk control after =>
    rcases control with ⟨result, owner⟩
    cases result with
    | error fault => simp [body, ran, ordinary, Fault.recoverable] at ordinaryResult
    | ok outcome =>
      simp only [body, ran] at ordinaryResult ⊢
      split at ordinaryResult
      · rename_i accepted
        simp only [accepted, ↓reduceIte]
        have safe := execution_valid ops allocator source meaning input key normalized deterministic cells before outcome initial.1 admitted (by rw [ran])
        simp only [ran] at safe
        simp only [admitOutput, Bool.and_eq_true, decide_eq_true_eq] at accepted
        refine ⟨safe, ?_⟩
        rcases accepted.1.2 with empty | frame
        · exact ⟨initial.2.1, fun _ inside => False.elim (by have length := initial.2.1; omega)⟩
        · exact represented_frame source values initial.2 frame
      · simp [ordinary, Fault.recoverable] at ordinaryResult

theorem body_semantics (ops : Operations σ) (allocator : Nat) (source : View) (meaning : Meaning)
    (input : Value Metadata) (key : Key) (normalized : ArgumentSlice) (deterministic : Bool)
    (cells : List Storage.Cell) (before : World (Publication.Effects σ)) (value : Word)
    (represented : before.graph.representatives = some cells)
    (memoryValid : Valid before.memory) (admitted : Admitted ops.arguments)
    (initial : Interner.Invariant meaning before.graph) (evaluated : key.eval meaning before.graph.read = some value) :
    let ran := body ops allocator source meaning input key normalized deterministic cells before
    Semantic.Ensures meaning before.graph ran.1 ran.2.graph (fun id after => after.read id = some value) := by
  dsimp only [Semantic.Ensures]
  intro ordinaryResult
  have observations := initial.representation
  simp only [Interner.Represented, represented] at observations
  have observed : Interner.Invariant meaning (Interner.observedHeap cells before.graph.table) :=
    ⟨by simpa only [observations.1] using initial.cache, rfl, observations.2⟩
  cases ran : execution ops allocator source meaning input key normalized deterministic cells before with
  | mk control after =>
    rcases control with ⟨result, owner⟩
    cases result with
    | error fault => simp [body, ran, ordinary, Fault.recoverable] at ordinaryResult
    | ok outcome =>
      simp only [body, ran, evaluated, Option.getD_some] at ordinaryResult ⊢
      split at ordinaryResult
      · rename_i accepted
        simp only [accepted, ↓reduceIte]
        have checks := accepted
        simp only [admitOutput, Bool.and_eq_true, decide_eq_true_eq] at checks
        have fields := execution_fields ops allocator source meaning input key normalized deterministic cells before outcome
          memoryValid admitted (by rw [ran])
        simp only [ran] at fields
        have bindings := cell_binding input key normalized value owner after fields
        have bound := bindings.2.trans checks.1.1.2
        have safe := Interner.InsertionExecution.verified meaning cells before.graph.table
          (cell input key normalized value owner after) key deterministic _ _ outcome observed (bindings.1.trans checks.1.1.1)
          (by simpa only [observations.1, bound] using evaluated) (by exact congrArg (fun r => r.1.1) ran)
        dsimp only at safe
        simp only [execution] at ran
        rw [ran] at safe
        refine ⟨safe.2.1.with_cursor _, ?_, ?_⟩
        · intro id word found
          exact safe.2.2.1 id word (by simpa only [observations.1] using found)
        · cases returned : Interner.insertionOutcome cells outcome with
          | error error => trivial
          | ok id =>
            simp only [returned] at safe
            simpa only [Except.mapError, projected, bound] using safe.2.2.2
      · simp [ordinary, Fault.recoverable] at ordinaryResult

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
