/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNativePolicy
import Compiler.Extraction.StorageExecutionTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))

/-- Instrument the same source program, actual native callbacks and initial
frame as `execution`. This is the insertion protocol, not a physical host log. -/
def recordExecution (history : List (Trace.Event Fault)) :=
  insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
    (Trace.record (observedCalls ops allocate safety allocator container source address meaning input key normalized cells before growth))
    {} ⟨observedStart before, history⟩

/-- No event segment or allocation policy is a premise: native execution
determines the exact recorded calls and replay consumes precisely that segment.
The result includes semantic faults and all reached native effects. -/
theorem execution_recorded (mismatch : Fault) (history leading trailing : List (Trace.Event Fault)) :
    let actual := execution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth
    let captured := recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth []
    (captured.1, captured.2.effects) = actual ∧
    recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth history =
      (actual.1, ⟨actual.2, history ++ captured.2.events⟩) ∧
    insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
      (Trace.replay (leading ++ captured.2.events ++ trailing) mismatch) {} leading.length =
      (actual.1, leading.length + captured.2.events.length) := by
  rw [execution_observed]
  exact Trace.execute_recorded _ mismatch _ insertProgram {} (observedStart before) history leading trailing

/-- Consume replay in the actual caller body: the replayed ownership state
selects the same reached graph, result and native memory. The typed count read
remains explicit. This does not establish native graph validity, word meaning,
or interleaving with normalization/publication and proper-child events. -/
theorem body_recorded (mismatch : Fault) (leading trailing : List (Trace.Event Fault))
    (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length)) :
    let captured := recordExecution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth []
    let replayed := insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
      (Trace.replay (leading ++ captured.2.events ++ trailing) mismatch) {} leading.length
    body ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth =
      ((match replayed.1.1 with
        | .error _ => .error (.language .safetyFault)
        | .ok outcome => (Interner.insertionOutcome cells outcome).mapError OwnedCall.Fault.language),
        Insertion.projected cells before key
          (cell input key normalized ((key.eval meaning before.graph.read).getD 0) replayed.1.2 captured.2.effects)
          replayed.1.2 captured.2.effects) ∧
    replayed.2 = leading.length + captured.2.events.length := by
  have recorded := execution_recorded ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth mismatch [] leading trailing
  have checked := checkedExecution_read ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth backing header
  dsimp only
  rw [recorded.2.2]
  constructor
  · rw [body, checked, ← recorded.1]
    cases (recordExecution ops allocate safety allocator container source address meaning input key normalized
      deterministic cells before growth []).1
    rfl
  · rfl

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
