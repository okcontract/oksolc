/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNativeBody
import Compiler.Extraction.InternerInsertionNativeProjection
import Compiler.Extraction.InsertionExecutionPolicy

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (cells : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))

/-- The same callback selection and initial locals as `executionWithRoom`,
shared by ghost observations and exact callback recording. The projection proofs check their
binding to that executor by definitional equality. -/
def observedCalls : Storage.Operations (Frame σ) Fault :=
  let value := (key.eval meaning before.graph.read).getD 0
  let projection := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  callbacks ops allocate safety allocator container source address input key normalized cells value projection growth

def observedStart : Frame σ := ⟨⟨⟨⟨before.memory, false⟩, none⟩, none⟩, none⟩

/-- Keep the executor binding explicit so later proofs rewrite one source call,
rather than repeatedly unfolding the entire execution to identify its locals. -/
theorem execution_observed :
    execution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth =
      insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩
        (observedCalls ops allocate safety allocator container source address meaning input key normalized cells before growth) {}
        (observedStart before) := rfl

/-- A ghost policy for one reached invocation, not a heap-only allocation
oracle or a policy for an independently advancing allocation stream. -/
def observedPolicy : Storage.Allocation → Bool :=
  Storage.executionPolicy
    (observedCalls ops allocate safety allocator container source address meaning input key normalized cells before growth)
    deterministic (observedStart before)

/-- Select the candidate from the actual preparation prefix. Earlier failure
makes this selection hypothetical; the candidate theorem uses only real source
success, and failed transactions never install the selected descriptor. -/
def observedCandidate : Storage.Cell :=
  cell input key normalized ((key.eval meaning before.graph.read).getD 0) (executionOwner deterministic .append)
    (executionPreparation
      (observedCalls ops allocate safety allocator container source address meaning input key normalized cells before growth)
      deterministic (observedStart before))

/-- Actual success binds the final candidate to preparation. The existing
append/publication lemmas retain its locals; neither final-cell equality nor a
fixture-specific allocation trace is assumed. -/
theorem execution_candidate
    (completed : (execution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth).1.1 =
      .ok (some .success)) :
    let ran := execution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth
    cell input key normalized ((key.eval meaning before.graph.read).getD 0) ran.1.2 ran.2 =
      observedCandidate ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth := by
  rw [execution_observed] at completed ⊢
  let value := (key.eval meaning before.graph.read).getD 0
  let projection : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project cells before.graph.table
    (cell input key normalized value owner state) key owner
  let calls := observedCalls ops allocate safety allocator container source address meaning input key normalized cells before growth
  let start := observedStart before
  let ready := executionPreparation calls deterministic start
  have observed := insert_execution_success calls deterministic (decide (cells.length < 2 ^ 32 - 1)) start completed
  have preserved : cell input key normalized value
    (insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ calls {} start).1.2
    (insertProgram.execute ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ calls {} start).2 =
      cell input key normalized value (executionOwner deterministic .append) ready := by
    rw [observed.2.2]
    cases deterministic with
    | false =>
      exact append_cell safety allocate allocator container cells input key normalized value
        transferredPreparation transferredOwnership ready growth
    | true =>
      have appended := append_cell safety allocate allocator container cells input key normalized value
        preparationOwnership publishedOwnership ready growth
      have published := publication_cell ops allocate safety allocator container source address input key normalized cells value projection
        growth publicationOwnership publishedOwnership ((calls.attempt .append preparationOwnership ready).2)
      exact published.trans appended
  exact preserved

/-- The native body's ordinary result and whole logical graph follow from its
source execution. The candidate equation binds preparation on actual success. Header,
policy and candidate binding remain local compiler obligations; this theorem
does not assume the final result/graph correspondence or native memory frame. -/
theorem body_model (candidate : Storage.Cell) (succeeds : Storage.Allocation → Bool)
    (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells)
    (policy : succeeds = observedPolicy ops allocate safety allocator container source address meaning input key normalized
      deterministic cells before growth)
    (binding :
      let ran := execution ops allocate safety allocator container source address meaning input key normalized
        deterministic cells before growth
      ran.1.1 = .ok (some .success) →
        observedCandidate ops allocate safety allocator container source address meaning input key normalized
          deterministic cells before growth = candidate)
    (completed : ordinary (body ops allocate safety allocator container source address meaning input key normalized
      deterministic cells before growth).1 = true) :
    let actual := body ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth
    let model := Interner.observedInsert candidate key deterministic succeeds before.graph
    actual.1 = model.1.mapError OwnedCall.Fault.language ∧ actual.2.graph = model.2 := by
  have checked := checkedExecution_read ops allocate safety allocator container source address meaning input key normalized
    deterministic cells before growth backing header
  cases ran : execution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth with
  | mk result after =>
    rcases result with ⟨result, owner⟩
    cases result with
    | error fault =>
      simp only [body, checked, ran, ordinary, OwnedCall.Fault.recoverable, Bool.false_eq_true] at completed
    | ok outcome =>
      have actual : (execution ops allocate safety allocator container source address meaning input key normalized
          deterministic cells before growth).1.1 = .ok outcome := by rw [ran]
      have safe := Storage.insert_execution_safe
        ⟨deterministic, decide (cells.length < 2 ^ 32 - 1), fun _ => false⟩ _ _ outcome actual
      change Storage.InsertionPost _ outcome (execution ops allocate safety allocator container source address meaning input key normalized
        deterministic cells before growth).1.2 at safe
      rw [ran] at safe
      have observed : Interner.observedInsertTransaction cells before.graph.table candidate key deterministic
        (observedPolicy ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth) =
          (Interner.insertionOutcome cells outcome, Interner.InsertionExecution.project cells before.graph.table candidate key
            (execution ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth).1.2) :=
        Interner.InsertionExecution.observed cells before.graph.table candidate key deterministic _ _ outcome actual
      rw [ran] at observed
      have same := Interner.InsertionExecution.project_candidate cells before.graph.table
        (cell input key normalized ((key.eval meaning before.graph.read).getD 0) owner after) candidate key deterministic
        outcome owner safe.1 (fun success => by
          have succeeded : (execution ops allocate safety allocator container source address meaning input key normalized
              deterministic cells before growth).1.1 = .ok (some .success) := by rw [ran, success]
          have selected := execution_candidate ops allocate safety allocator container source address meaning input key normalized
            deterministic cells before growth succeeded
          simpa only [ran] using selected.trans (binding succeeded))
      simp only [body, checked, ran, Insertion.projected, same,
        Interner.observedInsert, rows, policy, observed, and_self]

theorem insert_model (candidate : Storage.Cell) (succeeds : Storage.Allocation → Bool)
    (backing : Compiler.ZigAir.Memory.Address)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType backing cells.length))
    (rows : before.graph.representatives = some cells)
    (policy : succeeds = observedPolicy ops allocate safety allocator container source address meaning input key normalized
      deterministic cells before growth)
    (binding :
      let ran := execution ops allocate safety allocator container source address meaning input key normalized
        deterministic cells before growth
      ran.1.1 = .ok (some .success) →
        observedCandidate ops allocate safety allocator container source address meaning input key normalized
          deterministic cells before growth = candidate)
    (completed : ordinary (insert ops allocate safety allocator container source address meaning input key normalized
      deterministic growth before).1 = true) :
    let actual := insert ops allocate safety allocator container source address meaning input key normalized deterministic growth before
    let model := Interner.observedInsert candidate key deterministic succeeds before.graph
    actual.1 = model.1.mapError OwnedCall.Fault.language ∧ actual.2.graph = model.2 := by
  simp only [insert, rows] at completed ⊢
  exact body_model ops allocate safety allocator container source address meaning input key normalized deterministic cells before growth
    candidate succeeds backing header rows policy binding completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
