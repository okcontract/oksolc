/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNativePolicy
import Compiler.Extraction.InternerInsertionPreparationOutcome
import Compiler.Extraction.InternerInsertionAppendFailureModes

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

variable (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (rows : List Storage.Cell) (value : Word) (projection : Storage.State → Frame σ → Interner.Heap)
    (growth : Option (Growth.Registered.Callbacks σ))

/-- Invert the actual duplicate callback. An ordinary refusal is precisely
OOM; success retains the returned operands and reached session. -/
theorem duplicate_observation (owner : Storage.State) (before : Frame σ) (accepted : Bool)
    (completed : ((callbacks ops allocate safety allocator container source address input key normalized rows value projection growth).attempt
      .arguments owner before).1 = .ok accepted) :
    (accepted = false ∧ ∃ failed, takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ (memory before) = (.error .outOfMemory, failed)) ∨
    ∃ operands remaining duplicated, accepted = true ∧
      takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
        ⟨view normalized, normalized.items, none⟩ (memory before) = (.ok (operands, remaining), duplicated) ∧
      ((callbacks ops allocate safety allocator container source address input key normalized rows value projection growth).attempt
        .arguments owner before).2 = { withMemory before duplicated with duplicate := some operands } := by
  simp only [callbacks, Insertion.callbacks] at completed ⊢
  split at completed
  · cases completed
  next owns =>
    rw [if_neg owns]
    cases taken : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
        ⟨view normalized, normalized.items, none⟩ (memory before) with
    | mk result reached =>
      rw [taken] at completed
      cases result with
      | error fault =>
        cases fault <;> simp_all only [Except.mapError, Except.ok.injEq, reduceCtorEq]
        exact Or.inl ⟨trivial, reached, rfl⟩
      | ok pair =>
        obtain ⟨operands, remaining⟩ := pair
        simp only [Except.mapError, Except.ok.injEq] at completed
        subst accepted
        exact Or.inr ⟨operands, remaining, reached, rfl, rfl, rfl⟩

/-- Creation's ordinary result records its exact source allocation. Invalid
host responses are semantic rejections and cannot satisfy this observation. -/
theorem create_observation (owner : Storage.State) (before : Frame σ) (accepted : Bool)
    (absent : before.item.object = none)
    (completed : ((callbacks ops allocate safety allocator container source address input key normalized rows value projection growth).attempt
      .item owner before).1 = .ok accepted) :
    (accepted = false ∧ ∃ failed, AssemblyItem.Creation.create (observe ops.create) allocator input.item (memory before) =
      (.error .outOfMemory, failed)) ∨
    ∃ object allocated, accepted = true ∧
      AssemblyItem.Creation.create (observe ops.create) allocator input.item (memory before) = (.ok object, allocated) ∧
      ((callbacks ops allocate safety allocator container source address input key normalized rows value projection growth).attempt
        .item owner before).2 =
          { withMemory before allocated with item := { (withMemory before allocated).item with object := some object } } := by
  simp only [callbacks, items, AssemblyItem.Creation.NativeFields.operations, AssemblyItem.Creation.Insertion.operations,
    absent, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at completed ⊢
  cases created : AssemblyItem.Creation.create (observe ops.create) allocator input.item (memory before) with
  | mk result reached =>
    change AssemblyItem.Creation.create (observe ops.create) allocator input.item before.item.clone.execution.memory = _ at created
    rw [created] at completed ⊢
    cases result with
    | error fault =>
      cases fault <;> simp_all only [Except.mapError, Except.ok.injEq, reduceCtorEq]
      exact Or.inl ⟨trivial, reached, rfl⟩
    | ok object =>
      simp only [Except.mapError, Except.ok.injEq] at completed
      subst accepted
      exact Or.inr ⟨object, reached, rfl, rfl, rfl⟩

private theorem install_result (result : Except Compiler.ZigAir.Memory.Fault (Session σ))
    (before : AssemblyItem.Creation.NativeFields.State σ) (accepted : Bool)
    (completed : (AssemblyItem.Creation.NativeFields.installResult result before).1 = .ok accepted) :
    accepted = true := by
  cases result <;> simp_all only [AssemblyItem.Creation.NativeFields.installResult, Except.ok.injEq, reduceCtorEq]

/-- Native installation cannot change an ordinary clone result. Rejection
remains nonordinary; in particular, an installation fault is not OOM. -/
private theorem finish_result (object : Nat) (result : Except AssemblyItem.Creation.Insertion.Fault Bool)
    (before : AssemblyItem.Creation.NativeFields.State σ) (accepted : Bool)
    (completed : (AssemblyItem.Creation.NativeFields.finish object result before).1 = .ok accepted) :
    result = .ok accepted := by
  cases result with
  | error fault => cases completed
  | ok value =>
    cases value with
    | false => simpa only [AssemblyItem.Creation.NativeFields.finish, Except.ok.injEq] using completed
    | true =>
      cases present : before.clone.value with
      | none => simp only [AssemblyItem.Creation.NativeFields.finish, present, reduceCtorEq] at completed
      | some copied =>
        simp only [AssemblyItem.Creation.NativeFields.finish, present] at completed
        have same := install_result _ _ accepted completed
        rw [same]

/-- Invert the shared native item callback before lifting it into insertion. -/
private theorem clone_item_result (owner : Storage.State) (before : Frame σ) (object : Nat) (accepted : Bool)
    (present : before.item.object = some object)
    (completed : ((items ops allocator address input normalized owner before).attempt .clone owner before.item).1 = .ok accepted) :
    ((itemOperations ops allocator input normalized owner before).attempt .clone owner before.item).1 = .ok accepted := by
  simp only [items, AssemblyItem.Creation.NativeFields.operations, present] at completed
  cases checked : AssemblyClone.NativeFields.checkSource (memory before).memory address input with
  | error fault =>
    change AssemblyClone.NativeFields.checkSource before.item.clone.execution.memory.memory address input = _ at checked
    simp only [checked, reduceCtorEq] at completed
  | ok done =>
    cases done
    change AssemblyClone.NativeFields.checkSource before.item.clone.execution.memory.memory address input = _ at checked
    simp only [checked] at completed
    exact finish_result object _ _ accepted completed

/-- Ordinary clone observations identify the actual source clone result.
Source admission and installation can reject, but neither manufactures OOM. -/
theorem clone_observation (owner : Storage.State) (before : Frame σ) (object : Nat) (accepted : Bool)
    (present : before.item.object = some object)
    (completed : ((callbacks ops allocate safety allocator container source address input key normalized rows value projection growth).attempt
      .clone owner before).1 = .ok accepted) :
    (accepted = false ∧ ∃ failed, AssemblyClone.Physical.run (observe ops.copy) allocator input (memory before) =
      (.error .outOfMemory, failed)) ∨
    ∃ copied middle, accepted = true ∧
      AssemblyClone.Physical.run (observe ops.copy) allocator input (memory before) = (.ok copied, middle) := by
  have native : ((items ops allocator address input normalized owner before).attempt .clone owner before.item).1 = .ok accepted := by
    change (((items ops allocator address input normalized owner before).attempt .clone owner before.item).1.mapError Fault.item) = _ at completed
    cases observed : ((items ops allocator address input normalized owner before).attempt .clone owner before.item).1 with
    | error fault => simp only [observed, Except.mapError, reduceCtorEq] at completed
    | ok result => simpa only [observed, Except.mapError, Except.ok.injEq] using completed
  have base := clone_item_result ops allocator address input normalized owner before object accepted present native
  simp only [itemOperations, AssemblyItem.Creation.Insertion.operations, present,
    AssemblyItem.Creation.Insertion.cloneOperations, AssemblyClone.Physical.Insertion.operations] at base
  cases cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input (memory before) with
  | mk result middle =>
    change AssemblyClone.Physical.run (observe ops.copy) allocator input before.item.clone.execution.memory = _ at cloned
    rw [cloned] at base
    cases result with
    | error fault =>
      cases fault <;> simp_all only [Except.mapError, Except.ok.injEq, reduceCtorEq]
      exact Or.inl ⟨trivial, middle, rfl⟩
    | ok copied =>
      simp only [Except.mapError, Except.ok.injEq] at base
      subst accepted
      exact Or.inr ⟨copied, middle, rfl, rfl⟩

/-- Successful source preparation in either ownership mode. These are the
actual primitive calls, with each later call using its predecessor's session.
Installation, native validity and cleanup frames remain derived facts. -/
def PreparationSuccessAt (ops : Operations σ) (allocator : Nat)
    (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice)
    (deterministic : Bool) (before : Session (Publication.Effects σ)) : Prop :=
  ∃ operands remaining duplicated object allocated copied middle,
    PreparationInput ops allocator normalized operands remaining deterministic before duplicated ∧
    AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated) ∧
    AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)

/-- Exhaust preparation at an actual ordinary insertion. Native faults cannot
satisfy ordinary completion. Both ownership branches return either a genuine
allocation refusal or the exact successful source prefix, without any fixture,
allocator-budget, post-execution frame or successful-result assumption. -/
theorem execution_preparation_coverage (meaning : Meaning) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (outcome : Option Storage.Outcome)
    (room : rows.length < 2 ^ 32 - 1)
    (completed : (execution ops allocate safety allocator container source address meaning input key normalized
      deterministic rows before growth).1.1 = .ok outcome) :
    PreparationOOMAt ops allocator input normalized deterministic before.memory ∨
      PreparationSuccessAt ops allocator input normalized deterministic before.memory := by
  let value := (key.eval meaning before.graph.read).getD 0
  let projection : Storage.State → Frame σ → Interner.Heap := fun owner state => Interner.InsertionExecution.project rows before.graph.table
    (cell input key normalized value owner state) key owner
  let calls := callbacks ops allocate safety allocator container source address input key normalized rows value projection growth
  let start := observedStart before
  let duplicated := if deterministic then (calls.attempt .arguments normalizedOwnership start).2 else start
  have observed := insert_execution_preparation calls deterministic start outcome (by
    simpa only [execution, executionWithRoom, room, decide_true] using completed)
  rcases observed with ⟨deterministicTrue, failed⟩ | ⟨duplicate, rest⟩
  · subst deterministic
    rcases duplicate_observation ops allocate safety allocator container source address input key normalized rows value projection growth
        normalizedOwnership start false failed with ⟨_, failed, called⟩ | ⟨_, _, _, impossible, _⟩
    · exact Or.inl (.duplicate failed called)
    · cases impossible
  · have selection : ∃ operands remaining session,
        PreparationInput ops allocator normalized operands remaining deterministic before.memory session ∧
        duplicated = ⟨⟨⟨⟨session, false⟩, none⟩, none⟩, if deterministic then some operands else none⟩ := by
      cases deterministic with
      | false => exact ⟨normalized, ⟨view normalized, normalized.items, none⟩, before.memory, ⟨rfl, rfl⟩, rfl⟩
      | true =>
        rcases duplicate_observation ops allocate safety allocator container source address input key normalized rows value projection growth
            normalizedOwnership start true (duplicate rfl) with ⟨impossible, _⟩ | ⟨operands, remaining, session, _, called, reached⟩
        · cases impossible
        · exact ⟨operands, remaining, session, called, reached⟩
    obtain ⟨operands, remaining, session, selected, reached⟩ := selection
    have createOOM : ∀ failed, AssemblyItem.Creation.create (observe ops.create) allocator input.item session =
        (.error .outOfMemory, failed) → PreparationOOMAt ops allocator input normalized deterministic before.memory := by
      intro failed called
      cases deterministic with
      | true => exact .create operands remaining session failed selected called
      | false => exact .create failed (selected.2 ▸ called)
    have absent : duplicated.item.object = none := by rw [reached]
    have sessionEq : memory duplicated = session := by rw [reached]; rfl
    rcases rest with failed | ⟨created, rest⟩
    · rcases create_observation ops allocate safety allocator container source address input key normalized rows value projection growth
          (executionOwner deterministic .item) duplicated false absent failed with ⟨_, history, called⟩ | ⟨_, _, impossible, _⟩
      · exact Or.inl (createOOM history (sessionEq ▸ called))
      · cases impossible
    · rcases create_observation ops allocate safety allocator container source address input key normalized rows value projection growth
          (executionOwner deterministic .item) duplicated true absent created with ⟨impossible, _⟩ | ⟨object, allocated, _, called, made⟩
      · cases impossible
      · have createdCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item session = (.ok object, allocated) := sessionEq ▸ called
        have present : (calls.attempt .item (executionOwner deterministic .item) duplicated).2.item.object = some object := by rw [made]
        have allocatedEq : memory (calls.attempt .item (executionOwner deterministic .item) duplicated).2 = allocated := by rw [made]; rfl
        have cloneOOM : ∀ failed, AssemblyClone.Physical.run (observe ops.copy) allocator input allocated =
            (.error .outOfMemory, failed) → PreparationOOMAt ops allocator input normalized deterministic before.memory := by
          intro failed cloned
          cases deterministic with
          | true => exact .clone operands remaining object session allocated failed selected createdCall cloned
          | false => exact .clone object allocated failed (selected.2 ▸ createdCall) cloned
        rcases rest with failed | cloned
        · rcases clone_observation ops allocate safety allocator container source address input key normalized rows value projection growth
              (executionOwner deterministic .clone) _ object false present failed with ⟨_, history, cloned⟩ | ⟨_, _, impossible, _⟩
          · exact Or.inl (cloneOOM history (allocatedEq ▸ cloned))
          · cases impossible
        · rcases clone_observation ops allocate safety allocator container source address input key normalized rows value projection growth
              (executionOwner deterministic .clone) _ object true present cloned with ⟨impossible, _⟩ | ⟨copied, middle, _, cloned⟩
          · cases impossible
          · have clonedCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle) :=
              allocatedEq ▸ cloned
            exact Or.inr ⟨operands, remaining, session, object, allocated, copied, middle, selected, createdCall, clonedCall⟩

/-- Lift source coverage through the actual native count and result adapter.
The row/header relation comes from the reached graph, not a successful result.
Nonordinary native faults remain outside the conditional ordinary claim. -/
theorem insert_preparation_coverage (meaning : Meaning) (deterministic : Bool)
    (before : World (Publication.Effects σ)) (data : Compiler.ZigAir.Memory.Address)
    (projected : before.graph.representatives = some rows)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType data rows.length))
    (room : rows.length < 2 ^ 32 - 1)
    (completed : ordinary (insert ops allocate safety allocator container source address meaning input key normalized
      deterministic growth before).1 = true) :
    PreparationOOMAt ops allocator input normalized deterministic before.memory ∨
      PreparationSuccessAt ops allocator input normalized deterministic before.memory := by
  have checked := checkedExecution_read ops allocate safety allocator container source address meaning input key normalized
    deterministic rows before growth data header
  cases ran : execution ops allocate safety allocator container source address meaning input key normalized
      deterministic rows before growth with
  | mk result reached =>
    obtain ⟨result, owner⟩ := result
    cases result with
    | error fault =>
      simp only [insert, projected, body, checked, ran, ordinary, OwnedCall.Fault.recoverable, Bool.false_eq_true] at completed
    | ok outcome =>
      exact execution_preparation_coverage ops allocate safety allocator container source address input key normalized rows growth
        meaning deterministic before outcome room (by rw [ran])

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
