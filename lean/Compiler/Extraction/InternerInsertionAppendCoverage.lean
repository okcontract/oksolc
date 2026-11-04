/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPreparationCoverage
import Compiler.Extraction.RepresentativeAppendCoverage
import Compiler.Extraction.InternerNativeGraphFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Both ownership branches specialize the existing preparation proofs. The
actual primitive calls derive installation and preserve every original native
allocation and registry entry before the backing decision. -/
theorem prepare_selected (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety deterministic : Bool) (allocator container object : Nat) (source : View)
    (address : Compiler.ZigAir.Memory.Address) (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized operands : ArgumentSlice) (remaining : Handle)
    (rows : List Storage.Cell) (value : Word) (projection : Storage.State → Frame σ → Interner.Heap)
    (growth : Option (Growth.Registered.Callbacks σ)) (before duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid before) (live : Memory.SliceValid allocator before.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory address input)
    (admitted : deterministic = true → Admitted ops.arguments)
    (duplicateCall : PreparationInput ops allocator normalized operands remaining deterministic before duplicated)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    let calls := callbacks ops allocate safety allocator container source address input key normalized rows value projection growth
    let start : Frame σ := ⟨⟨⟨⟨before, false⟩, none⟩, none⟩, none⟩
    let dupe : Frame σ := if deterministic then ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩ else start
    let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, if deterministic then some operands else none⟩
    ∃ installed,
      (deterministic = true → calls.attempt .arguments normalizedOwnership start = (.ok true, dupe)) ∧
      calls.attempt .item (executionOwner deterministic .item) dupe = (.ok true, made) ∧
      calls.attempt .clone (executionOwner deterministic .clone) made =
        (.ok true, preparedFrameAt deterministic object copied operands installed) ∧
      AssemblyClone.NativeFields.Installed allocator object copied middle installed ∧
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      (∀ id cell, before.memory.heap.lookup id = some cell →
        installed.memory.heap.lookup id = some cell ∧ installed.heap id = before.heap id) ∧
      installed.effects.keys = before.effects.keys := by
  cases deterministic with
  | true =>
    obtain ⟨installed, duplicateRun, createRun, cloneRun, post, assigned, _, _, _, _, frame, keys, _⟩ :=
      prepare_owned ops allocate safety allocator container object source address input copied key normalized operands rows value
        projection ⟨⟨⟨⟨before, false⟩, none⟩, none⟩, none⟩ duplicated allocated middle remaining initial live represented rfl
        (admitted rfl) duplicateCall createCall cloneCall
    exact ⟨installed, fun _ => duplicateRun normalizedOwnership, createRun (executionOwner true .item), cloneRun (executionOwner true .clone), post, assigned, frame, keys⟩
  | false =>
    obtain ⟨operandsEq, duplicatedEq⟩ := duplicateCall
    subst operands
    subst duplicated
    obtain ⟨installed, createRun, cloneRun, post, assigned, frame, keys, _⟩ :=
      prepare_item ops allocate safety allocator container object source address input copied key normalized rows value projection
        ⟨⟨⟨⟨before, false⟩, none⟩, none⟩, none⟩ allocated middle initial represented rfl createCall cloneCall
    exact ⟨installed, fun impossible => Bool.noConfusion impossible, createRun (executionOwner false .item), cloneRun (executionOwner false .clone), post, assigned, frame, keys⟩

/-- Ordinary source completion after successful preparation reaches an
ordinary native append. Reuse preparation to identify the exact installed
session; do not assume a successful allocation or discard a rejected store. -/
theorem execution_prepared_append (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety deterministic : Bool) (allocator container object : Nat) (source : View)
    (address : Compiler.ZigAir.Memory.Address) (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized operands : ArgumentSlice) (remaining : Handle)
    (rows : List Storage.Cell) (meaning : Meaning) (growth : Option (Growth.Registered.Callbacks σ))
    (before : World (Publication.Effects σ)) (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid before.memory) (live : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (admitted : deterministic = true → Admitted ops.arguments) (room : rows.length < 2 ^ 32 - 1)
    (duplicateCall : PreparationInput ops allocator normalized operands remaining deterministic before.memory duplicated)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (outcome : Option Storage.Outcome)
    (completed : (execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth).1.1 =
      .ok outcome) :
    ∃ installed accepted,
      AssemblyClone.NativeFields.Installed allocator object copied middle installed ∧
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell →
        installed.memory.heap.lookup id = some cell ∧ installed.heap id = before.memory.heap id) ∧
      installed.effects.keys = before.memory.effects.keys ∧
      (append safety allocate allocator container rows input key normalized ((key.eval meaning before.graph.read).getD 0)
        (preparationOwnershipAt deterministic) (preparedFrameAt deterministic object copied operands installed) growth).1 = .ok accepted := by
  let value := (key.eval meaning before.graph.read).getD 0
  let projection : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project rows before.graph.table
    (cell input key normalized value owner state) key owner
  let calls := observedCalls ops allocate safety allocator container source address meaning input key normalized rows before growth
  let start := observedStart before
  let dupe : Frame σ := if deterministic then ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩ else start
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, if deterministic then some operands else none⟩
  obtain ⟨installed, duplicateRun, createRun, cloneRun, post, assigned, frame, keys⟩ :=
    prepare_selected ops allocate safety deterministic allocator container object source address input copied key normalized operands remaining
      rows value projection growth before.memory duplicated allocated middle initial live represented admitted duplicateCall createCall cloneCall
  change (deterministic = true → calls.attempt .arguments normalizedOwnership start = (.ok true, dupe)) at duplicateRun
  change calls.attempt .item (executionOwner deterministic .item) dupe = (.ok true, made) at createRun
  change calls.attempt .clone (executionOwner deterministic .clone) made =
    (.ok true, preparedFrameAt deterministic object copied operands installed) at cloneRun
  have selected : (if deterministic then (calls.attempt .arguments normalizedOwnership start).2 else start) = dupe := by
    cases deterministic with
    | false => rfl
    | true => exact congrArg Prod.snd (duplicateRun rfl)
  have observed := insert_execution_append calls deterministic start outcome (by
    simpa only [execution_observed, room, decide_true] using completed)
  dsimp only at observed
  rw [selected, createRun, cloneRun] at observed
  have ordinary := observed (fun yes => congrArg Prod.fst (duplicateRun yes)) rfl rfl
  have ownerEq : executionOwner deterministic .append = preparationOwnershipAt deterministic := by cases deterministic <;> rfl
  rcases ordinary with failed | ⟨accepted, _⟩
  · exact ⟨installed, false, post, assigned, frame, keys, ownerEq ▸ failed⟩
  · exact ⟨installed, true, post, assigned, frame, keys, ownerEq ▸ accepted⟩

/-- Remove the effect wrapper without strengthening the observed allocator
response. The publication key table is independent of allocator-private state. -/
theorem allocation_observation (allocate : Backing.Registry.Allocate σ) (allocator capacity : Nat)
    (before : Session (Publication.Effects σ)) (accepted : Bool)
    (observed : Backing.AllocationObservation (allocation allocate allocator) capacity before.memory before.effects accepted) :
    Backing.AllocationObservation (allocate allocator) capacity before.memory before.effects.allocator accepted := by
  cases accepted with
  | false =>
    obtain ⟨reached, called⟩ := observed
    exact ⟨(allocate allocator (capacity * 32) 8 before.effects.allocator).2,
      Prod.ext (congrArg (fun result : Option Nat × Publication.Effects σ => result.1) called) rfl⟩
  | true =>
    obtain ⟨base, reached, called, fits⟩ := observed
    exact ⟨base, (allocate allocator (capacity * 32) 8 before.effects.allocator).2,
      Prod.ext (congrArg (fun result : Option Nat × Publication.Effects σ => result.1) called) rfl, fits⟩

/-- The insertion adapter preserves the native append decision. Missing local
values and mapped memory faults cannot be ordinary false results. -/
theorem append_native_completion (safety : Bool) (allocate : Backing.Registry.Allocate σ)
    (allocator container : Nat) (rows : List Storage.Cell) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (value : Word) (owner : Storage.State) (before : Frame σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (accepted : Bool)
    (completed : (append safety allocate allocator container rows input key normalized value owner before growth).1 = .ok accepted) :
    (match growth.map growthCallbacks with
      | none => Append.Registered.run safety (allocation allocate) allocator container rows
          (cell input key normalized value owner before) (memory before)
      | some calls => Append.Registered.runWithGrowth calls safety (allocation allocate) allocator container rows
          (cell input key normalized value owner before) (memory before)).1 = .ok accepted := by
  unfold append at completed
  split at completed
  · cases completed
  · cases growth with
    | none =>
      dsimp only [Option.map]
      cases ran : Append.Registered.run safety (allocation allocate) allocator container rows
          (cell input key normalized value owner before) (memory before) with
      | mk result reached =>
        simp only [ran] at completed
        cases result with
        | error fault => cases completed
        | ok selected => exact congrArg Except.ok (Except.ok.inj completed)
    | some calls =>
      dsimp only [Option.map]
      cases ran : Append.Registered.runWithGrowth (growthCallbacks calls) safety (allocation allocate) allocator container rows
          (cell input key normalized value owner before) (memory before) with
      | mk result reached =>
        simp only [ran] at completed
        cases result with
        | error fault => cases completed
        | ok selected => exact congrArg Except.ok (Except.ok.inj completed)

/-- Apply native backing coverage and erase only the allocator effect wrapper.
The original remap identity and release callback are retained. -/
theorem append_backing_observation (safety : Bool) (allocate : Backing.Registry.Allocate σ)
    (allocator container : Nat) (rows : List Storage.Cell) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (value : Word) (owner : Storage.State) (before : Frame σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (accepted : Bool)
    (ownerCell : Compiler.ZigAir.Memory.Allocation) (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (valid : Valid (memory before))
    (found : (memory before).memory.heap.lookup container = some ownerCell)
    (typed : ownerCell.type = Owner.viewType safety)
    (loaded : readHeader (memory before).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType data rows.length, .scalar (.int false 64 capacity)))
    (bounded : rows.length ≤ capacity)
    (storage : capacity ≠ 0 → Backing.Release.Owned allocator data capacity (memory before))
    (room : rows.length < 2 ^ 32 - 1)
    (completed : (append safety allocate allocator container rows input key normalized value owner before growth).1 = .ok accepted) :
    Append.Registered.BackingObservation growth allocate allocator container rows.length capacity (Publication.forget (memory before)) accepted := by
  have native := append_native_completion safety allocate allocator container rows input key normalized value owner before growth accepted completed
  have observed := Append.Registered.backing_observation (growth.map growthCallbacks) safety (allocation allocate) allocator container rows
    (cell input key normalized value owner before) (memory before) ownerCell data capacity valid found typed loaded bounded storage room accepted (by cases growth <;> exact native)
  rcases observed with spare | ⟨unlocked, first | ⟨nonempty, short, context, returnAddress, release, selected, allocated⟩⟩
  · exact Or.inl spare
  · exact Or.inr ⟨unlocked, Or.inl ⟨first.1, allocation_observation allocate allocator 5 (memory before) accepted first.2⟩⟩
  · cases growth with
    | none => cases selected
    | some calls =>
      have remap := congrArg Growth.Registered.Callbacks.remap (Option.some.inj selected)
      refine Or.inr ⟨unlocked, Or.inr ⟨nonempty, short, context, returnAddress, calls.release, ?_,
        allocation_observation allocate allocator _ (memory before) accepted allocated⟩⟩
      cases calls
      cases remap
      rfl

/-- Successful preparation and an ordinary insertion derive an exhaustive
backing observation at the exact installed session. Original graph geometry
is transported by the existing preparation and graph-frame theorems. -/
theorem execution_backing_coverage (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (safety deterministic : Bool) (allocator container object : Nat) (source : View)
    (address : Compiler.ZigAir.Memory.Address) (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized operands : ArgumentSlice) (remaining : Handle)
    (rows : List Storage.Cell) (meaning : Meaning) (growth : Option (Growth.Registered.Callbacks σ))
    (before : World (Publication.Effects σ)) (duplicated allocated middle : Session (Publication.Effects σ))
    (data : Compiler.ZigAir.Memory.Address) (capacity : Nat)
    (facts : NativeGraph.Facts safety allocator container data capacity before rows)
    (live : Memory.SliceValid allocator before.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents before.memory.memory address input)
    (admitted : deterministic = true → Admitted ops.arguments) (room : rows.length < 2 ^ 32 - 1)
    (duplicateCall : PreparationInput ops allocator normalized operands remaining deterministic before.memory duplicated)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (outcome : Option Storage.Outcome)
    (completed : (execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth).1.1 =
      .ok outcome) :
    ∃ installed accepted,
      Valid installed ∧
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → installed.memory.heap.lookup id = some cell) ∧
      Append.Registered.BackingObservation growth allocate allocator container rows.length capacity (Publication.forget installed) accepted := by
  obtain ⟨installed, accepted, post, assigned, frame, keys, appended⟩ := execution_prepared_append ops allocate safety deterministic allocator container
    object source address input copied key normalized operands remaining rows meaning growth before duplicated allocated middle facts.valid live
    represented admitted room duplicateCall createCall cloneCall outcome completed
  have installedFacts := facts.frame (after := { before with memory := installed }) post.valid facts.projected rfl keys
    (fun id cell found _ => (frame id cell found).1) (fun id block registered => by
      obtain ⟨cell, found, _⟩ := facts.valid.injected id block registered
      exact (frame id cell found).2.trans registered)
  obtain ⟨ownerCell, found, typed, _⟩ := installedFacts.ownerLive
  exact ⟨installed, accepted, post.valid, assigned, (fun id cell found => (frame id cell found).1),
    append_backing_observation safety allocate allocator container rows input key normalized _ (preparationOwnershipAt deterministic)
      (preparedFrameAt deterministic object copied operands installed) growth accepted ownerCell data capacity post.valid found typed
      installedFacts.header facts.bounded (fun nonempty => (installedFacts.storage nonempty).1) room appended⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
