/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendCoverage

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The candidate's observable fields are determined by the reached allocation
cursor and source inputs. Empty duplication consumes no allocation identity;
transferred insertion retains the incoming argument address. -/
def allocationCandidate (input : AssemblyClone.NativeFields.ItemValue) (key : Key)
    (normalized : ArgumentSlice) (value : Word) (deterministic : Bool) (nextId : Nat) : Storage.Cell :=
  { item := input.item
    itemAddress := nextId + if deterministic && !normalized.items.isEmpty then 1 else 0
    arguments := normalized.items
    argumentsAddress := if deterministic then nextId else normalized.address
    sequence := key.sequence
    otherValue := value }

/-- The key supplies normalized values. Only transferred insertion observes
the incoming address; deterministic duplication allocates its own slice. -/
theorem allocationCandidate_inputs (input : AssemblyClone.NativeFields.ItemValue) (key : Key)
    (normalized : ArgumentSlice) (value : Word) (deterministic : Bool) (nextId incoming : Nat)
    (aligned : normalized.items = key.arguments)
    (transferred : deterministic = false → normalized.address = incoming) :
    allocationCandidate input key normalized value deterministic nextId =
      allocationCandidate input key ⟨incoming, key.arguments⟩ value deterministic nextId := by
  cases deterministic with
  | false => simp only [allocationCandidate, aligned, transferred rfl, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  | true => simp only [allocationCandidate, aligned, Bool.true_and, ↓reduceIte]

/-- Recover duplication's exact allocation counter from the actual successful
call. The existing total duplication theorem supplies empty/nonempty behavior
and allocator admission; successful copy cannot invent an extra allocation. -/
theorem duplicate_allocation (ops : Operations σ) (allocator : Nat) (normalized operands : ArgumentSlice)
    (before after : Session (Publication.Effects σ)) (remaining : Handle)
    (initial : Valid before) (live : Memory.SliceValid allocator before.heap normalized)
    (admitted : Admitted ops.arguments)
    (executed : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before = (.ok (operands, remaining), after)) :
    operands = ⟨before.memory.nextId, normalized.items⟩ ∧
      after.memory.nextId = before.memory.nextId + if normalized.items.isEmpty then 0 else 1 := by
  have ready := borrowed_ready allocator normalized before initial live
  obtain ⟨result, heap, memory, effects, ran, post⟩ := Duplication.run_total before.heap before.memory allocator
    (view normalized) normalized.items ((Publication.external ops.arguments).allocate .duplicate before) before.effects
    initial.memory initial.related ready.contents (fun _ => initial.injected.fresh initial.memory)
    (fun nonempty base effects response => (Publication.external_admitted ops.arguments admitted)
      .duplicate before normalized.items base effects initial.memory nonempty response)
  simp only [takeOwned, ran] at executed
  cases result with
  | none => cases executed
  | some slice =>
    cases executed
    exact ⟨post.descriptor, post.nextId⟩

/-- Both preparation branches derive the candidate from actual duplicate,
create and clone calls. No final candidate or allocation-identity equation is
supplied by the caller. Installation is handled by the shared native proof. -/
theorem prepared_allocation_candidate (ops : Operations σ) (allocator object : Nat)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (value : Word) (remaining : Handle) (deterministic : Bool)
    (before duplicated allocated middle installed : Session (Publication.Effects σ))
    (initial : Valid before) (live : Memory.SliceValid allocator before.heap normalized)
    (admitted : deterministic = true → Admitted ops.arguments)
    (selected : PreparationInput ops allocator normalized operands remaining deterministic before duplicated)
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    cell input key normalized value (preparationOwnershipAt deterministic)
      (preparedFrameAt deterministic object copied operands installed) =
      allocationCandidate input key normalized value deterministic before.memory.nextId := by
  have item := (AssemblyClone.clone_item (AssemblyClone.Physical.duplicate (observe ops.copy) allocator)
    input copied allocated middle cloned).1
  obtain ⟨base, effects, _, fresh, _⟩ := AssemblyItem.Creation.create_shape (observe ops.create) allocator object
    input.item duplicated allocated created
  have arguments := prepared_arguments ops allocator object normalized operands remaining deterministic before duplicated installed copied selected
  simp only [cell, arguments, Option.getD_some]
  cases deterministic with
  | false =>
    obtain ⟨rfl, rfl⟩ := selected
    simp only [preparedFrameAt, Bool.false_eq_true, ↓reduceIte, Option.getD_some, allocationCandidate,
      Bool.false_and, Nat.add_zero, item, fresh]
  | true =>
    obtain ⟨descriptor, counter⟩ := duplicate_allocation ops allocator normalized operands before duplicated remaining
      initial live (admitted rfl) selected
    rw [counter] at fresh
    rw [descriptor]
    simp only [preparedFrameAt, ↓reduceIte, Option.getD_some, allocationCandidate, Bool.true_and, item, fresh]
    cases normalized.items.isEmpty <;> rfl

variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (deterministic : Bool) (rows : List Storage.Cell) (before : World (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))

/-- Actual successful preparation identifies the candidate selected by the
existing observation. Both ownership modes share native installation and the
same allocation-derived descriptor; no final execution state is assumed. -/
theorem observed_allocation_candidate
    (initial : Valid before.memory) (live : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (admitted : deterministic = true → Admitted ops.arguments)
    (prepared : PreparationSuccessAt ops allocator input normalized deterministic before.memory) :
    observedCandidate ops allocate safety allocator container source address meaning input key normalized
      deterministic rows before growth =
      allocationCandidate input key normalized ((key.eval meaning before.graph.read).getD 0)
        deterministic before.memory.memory.nextId := by
  obtain ⟨operands, remaining, duplicated, object, allocated, copied, middle, selected, created, cloned⟩ := prepared
  let value := (key.eval meaning before.graph.read).getD 0
  let projection : Storage.State → Frame σ → Interner.Heap := fun owner state =>
    Interner.InsertionExecution.project rows before.graph.table (cell input key normalized value owner state) key owner
  let calls := observedCalls ops allocate safety allocator container source address meaning input key normalized rows before growth
  let start := observedStart before
  let dupe : Frame σ := if deterministic then ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩ else start
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, if deterministic then some operands else none⟩
  obtain ⟨installed, duplicateRun, createRun, cloneRun, _⟩ :=
    prepare_selected ops allocate safety deterministic allocator container object source address input copied key normalized operands remaining
      rows value projection growth before.memory duplicated allocated middle initial live represented admitted selected created cloned
  change (deterministic = true → calls.attempt .arguments normalizedOwnership start = (.ok true, dupe)) at duplicateRun
  change calls.attempt .item (executionOwner deterministic .item) dupe = (.ok true, made) at createRun
  change calls.attempt .clone (executionOwner deterministic .clone) made =
    (.ok true, preparedFrameAt deterministic object copied operands installed) at cloneRun
  have duplicatedEq : (if deterministic then (executionAttempt calls deterministic .arguments start).2 else start) = dupe := by
    cases deterministic with
    | false => rfl
    | true => exact congrArg Prod.snd (duplicateRun rfl)
  have ready : executionPreparation calls deterministic start =
      preparedFrameAt deterministic object copied operands installed := by
    simp only [executionPreparation]
    have first : (if deterministic then executionAttempt calls deterministic .arguments start else (true, start)).2 = dupe := by
      cases deterministic <;> exact duplicatedEq
    rw [first]
    simp only [executionAttempt, createRun, cloneRun]
  change cell input key normalized value (executionOwner deterministic .append)
    (executionPreparation calls deterministic start) = _
  rw [ready]
  have owner : executionOwner deterministic .append = preparationOwnershipAt deterministic := by cases deterministic <;> rfl
  rw [owner]
  exact prepared_allocation_candidate ops allocator object input copied key normalized operands value remaining deterministic
    before.memory duplicated allocated middle installed initial live admitted selected created cloned

/-- Successful native insertion derives its candidate directly from entry
inputs and the native allocation cursor. Actual failure coverage excludes
refused preparation; the append/publication proof retains the same descriptor.
This removes a candidate-binding premise without claiming native admission. -/
theorem execution_allocation_candidate
    (initial : Valid before.memory) (live : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (admitted : Admitted ops.arguments)
    (completed : (execution ops allocate safety allocator container source address meaning input key normalized
      deterministic rows before growth).1.1 = .ok (some .success)) :
    let ran := execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth
    cell input key normalized ((key.eval meaning before.graph.read).getD 0) ran.1.2 ran.2 =
      allocationCandidate input key normalized ((key.eval meaning before.graph.read).getD 0)
        deterministic before.memory.memory.nextId := by
  have room : rows.length < 2 ^ 32 - 1 := by
    by_cases fits : rows.length < 2 ^ 32 - 1
    · exact fits
    · have impossible := insert_execution_capacity_outcome deterministic (fun _ => false)
        (observedCalls ops allocate safety allocator container source address meaning input key normalized rows before growth)
        (observedStart before) (some .success) (by simpa only [execution_observed, fits, decide_false] using completed)
      cases impossible
  have prepared : PreparationSuccessAt ops allocator input normalized deterministic before.memory := by
    rcases execution_preparation_coverage ops allocate safety allocator container source address input key normalized rows growth
      meaning deterministic before (some .success) room completed with refused | prepared
    · obtain ⟨after, closed, ran, _⟩ := preparation_oom_execution_at ops allocate growth safety allocator container source address
        meaning input key normalized deterministic rows before initial live represented admitted room refused
      rw [ran] at completed
      cases completed
    · exact prepared
  exact (execution_candidate ops allocate safety allocator container source address meaning input key normalized
    deterministic rows before growth completed).trans
      (observed_allocation_candidate ops allocate safety allocator container source address meaning input key normalized
        deterministic rows before growth initial live represented (fun _ => admitted) prepared)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
