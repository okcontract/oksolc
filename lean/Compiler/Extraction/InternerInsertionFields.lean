/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionValidity
import Compiler.Extraction.AssemblyCloneProofs
import Compiler.Extraction.NormalizationMemoryFields

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open AssemblyClone (Value)

/-- The insertion local either holds its source item or has been invalidated
by cleanup. This is field correspondence, not physical object-store refinement. -/
def CloneFields (input : Value Metadata) (state : AssemblyClone.Physical.Insertion.State Metadata σ) : Prop :=
  (state.value.getD input).item = input.item

def CreationFields (input : Value Metadata) (state : AssemblyItem.Creation.Insertion.State Metadata σ) : Prop :=
  CloneFields input state.clone

theorem clone_fields (copy : AssemblyClone.Physical.Allocate σ) (bytes : AssemblyItemDeinit.Release σ)
    (objects : AssemblyItem.Release σ) (external : External σ) (allocator : Nat) (input : Value Metadata)
    (target : Storage.State → AssemblyClone.Physical.Insertion.State Metadata σ → ExpressionDeinit.Descriptor)
    (rest : Storage.Operations (AssemblyClone.Physical.Insertion.State Metadata σ) AssemblyClone.Physical.Insertion.Fault)
    (kept : Storage.Preserves rest (CloneFields input)) :
    Storage.Preserves (AssemblyClone.Physical.Insertion.operations copy bytes objects external allocator input target rest)
      (CloneFields input) := by
  constructor
  · intro site owner before result after initial called
    cases site with
    | arguments | item | append | publish => exact kept.attempt _ owner before result after initial called
    | clone =>
      cases ran : AssemblyClone.Physical.run copy allocator input before.execution.memory with
      | mk response reached =>
        cases response with
        | ok copied =>
          have same := (AssemblyClone.clone_item (AssemblyClone.Physical.duplicate copy allocator) input copied _ _ ran).1
          simp only [AssemblyClone.Physical.Insertion.operations, ran, Prod.mk.injEq, Except.ok.injEq] at called
          rw [← called.2]
          exact same
        | error fault =>
          cases fault <;> simp only [AssemblyClone.Physical.Insertion.operations, ran, Prod.mk.injEq,
            Except.ok.injEq, reduceCtorEq, false_and] at called
          all_goals first | contradiction | exact called.2 ▸ initial
  · intro action owner before after initial called
    cases action with
    | normalized | arguments | allocation | pop => exact kept.release _ owner before after initial called
    | value | lastValue =>
      dsimp only [AssemblyClone.Physical.Insertion.operations] at called
      split at called
      · simp at called
      · cases present : before.value with
        | none => simp [present] at called
        | some copied =>
          simp only [present] at called
          have same := congrArg Prod.snd called
          dsimp only at same
          rw [← same]
          simp only [CloneFields]
          split
          · rfl
          · simpa only [CloneFields, present] using initial

theorem creation_fields (allocate : AssemblyItem.Creation.Allocate σ) (copy : AssemblyClone.Physical.Allocate σ)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator : Nat) (input : Value Metadata)
    (arguments : Storage.State → AssemblyClone.Physical.Insertion.State Metadata σ → ArgumentSlice)
    (rest : Storage.Operations (AssemblyItem.Creation.Insertion.State Metadata σ) AssemblyItem.Creation.Insertion.Fault)
    (kept : Storage.Preserves rest (CreationFields input)) :
    Storage.Preserves (AssemblyItem.Creation.Insertion.operations allocate copy bytes objects external allocator input arguments rest)
      (CreationFields input) := by
  have clone (object : Nat) : Storage.Preserves
      (AssemblyItem.Creation.Insertion.cloneOperations copy bytes objects external allocator object input arguments)
      (CloneFields input) := by
    apply clone_fields
    constructor
    · intro _ _ _ _ _ _ impossible; cases impossible
    · intro _ _ _ _ _ impossible; cases impossible
  have release (action : Storage.Release) (owner : Storage.State)
      (before after : AssemblyItem.Creation.Insertion.State Metadata σ) (object : Nat)
      (initial : CreationFields input before) :
      let ran := (AssemblyItem.Creation.Insertion.cloneOperations copy bytes objects external allocator object input arguments).release action owner before.clone
      (ran.1.mapError AssemblyItem.Creation.Insertion.Fault.insertion,
        { clone := ran.2, object := if ran.2.execution.invalidated then none else some object }) = (.ok (), after) →
      CreationFields input after := by
    dsimp only
    intro called
    cases ran : (AssemblyItem.Creation.Insertion.cloneOperations copy bytes objects external allocator object input arguments).release action owner before.clone with
    | mk response reached =>
      cases response with
      | error fault => simp [ran, Except.mapError] at called
      | ok returned =>
        cases returned
        have post := (clone object).release action owner before.clone reached initial ran
        simp only [ran, Except.mapError, Prod.mk.injEq] at called
        exact called.2 ▸ post
  constructor
  · intro site owner before result after initial called
    cases site with
    | arguments | append | publish => exact kept.attempt _ owner before result after initial called
    | item =>
      dsimp only [AssemblyItem.Creation.Insertion.operations] at called
      split at called
      · simp at called
      · cases ran : AssemblyItem.Creation.create allocate allocator input.item before.clone.execution.memory with
        | mk response reached =>
          cases response with
          | ok object =>
            simp only [ran, Prod.mk.injEq, Except.ok.injEq] at called
            exact called.2 ▸ initial
          | error fault =>
            cases fault <;> simp only [ran, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at called
            all_goals first | contradiction | exact called.2 ▸ initial
    | clone =>
      dsimp only [AssemblyItem.Creation.Insertion.operations] at called
      cases present : before.object with
      | none => simp [present] at called
      | some object =>
        simp only [present] at called
        cases ran : (AssemblyItem.Creation.Insertion.cloneOperations copy bytes objects external allocator object input arguments).attempt .clone owner before.clone with
        | mk response reached =>
          cases response with
          | error fault => simp [ran, Except.mapError] at called
          | ok accepted =>
            have post := (clone object).attempt .clone owner before.clone accepted reached initial ran
            simp only [ran, Except.mapError, Prod.mk.injEq, Except.ok.injEq] at called
            exact called.2 ▸ post
  · intro action owner before after initial called
    cases action with
    | normalized | arguments | pop => exact kept.release _ owner before after initial called
    | allocation =>
      dsimp only [AssemblyItem.Creation.Insertion.operations] at called
      cases present : before.object with
      | none => simp [present] at called
      | some object =>
        simp only [present] at called
        have same := congrArg Prod.snd called
        dsimp only at same
        rw [← same]
        exact initial
    | value | lastValue =>
      dsimp only [AssemblyItem.Creation.Insertion.operations] at called
      cases present : before.object with
      | none => simp [present] at called
      | some object =>
        simp only [present] at called
        first
        | exact release .value owner before after object initial called
        | exact release .lastValue owner before after object initial called

/-- The complete insertion's item and operand descriptors come from its input.
Memory validity is carried through the same callbacks to use the checked copy
theorem; the fields are not accepted from the final projected representative. -/
structure Fields (input : Value Metadata) (normalized : ArgumentSlice) (state : State Metadata σ) : Prop where
  valid : StateValid state
  item : CreationFields input state.item
  duplicate : (state.duplicate.getD normalized).items = normalized.items

theorem item_fields (ops : Operations σ) (allocator : Nat) (input : Value Metadata)
    (normalized : ArgumentSlice) (owner : Storage.State) (before : State Metadata σ) :
    Storage.Preserves (itemOperations ops allocator input normalized owner before) (CreationFields input) := by
  apply creation_fields
  constructor
  · intro _ _ _ _ _ _ impossible; cases impossible
  · intro _ _ _ _ _ impossible; cases impossible

/-- Local descriptor correspondence is independent of reached memory validity.
Native storage/assignment callbacks can reuse it without assuming the older
physical callback's memory contract. -/
structure FieldValues (input : Value Metadata) (normalized : ArgumentSlice) (state : State Metadata σ) : Prop where
  item : CreationFields input state.item
  duplicate : (state.duplicate.getD normalized).items = normalized.items

theorem callbacks_field_values (ops : Operations σ) (allocator count : Nat) (source : View) (input : Value Metadata)
    (key : Key) (normalized : ArgumentSlice) (graph : Storage.State → State Metadata σ → Interner.Heap) :
    Storage.Preserves (callbacks ops allocator count source input key normalized graph) (FieldValues input normalized) := by
  have liftedAttempt : ∀ site owner before result after, FieldValues input normalized before →
      (let ran := (itemOperations ops allocator input normalized owner before).attempt site owner before.item
       (ran.1.mapError Rejection.creation, { before with item := ran.2 })) = (.ok result, after) →
      CreationFields input after.item ∧ (after.duplicate.getD normalized).items = normalized.items := by
    intro site owner before result after initial called
    cases ran : (itemOperations ops allocator input normalized owner before).attempt site owner before.item with
    | mk response reached =>
      cases response with
      | error fault => simp [ran, Except.mapError] at called
      | ok accepted =>
        have post := (item_fields ops allocator input normalized owner before).attempt site owner before.item accepted reached initial.item ran
        simp only [ran, Except.mapError, Prod.mk.injEq, Except.ok.injEq] at called
        rw [← called.2]
        exact ⟨post, initial.duplicate⟩
  have liftedRelease : ∀ action owner before after, FieldValues input normalized before →
      (let ran := (itemOperations ops allocator input normalized owner before).release action owner before.item
       (ran.1.mapError Rejection.creation, { before with item := ran.2 })) = (.ok (), after) →
      CreationFields input after.item ∧ (after.duplicate.getD normalized).items = normalized.items := by
    intro action owner before after initial called
    cases ran : (itemOperations ops allocator input normalized owner before).release action owner before.item with
    | mk response reached =>
      cases response with
      | error fault => simp [ran, Except.mapError] at called
      | ok returned =>
        cases returned
        have post := (item_fields ops allocator input normalized owner before).release action owner before.item reached initial.item ran
        simp only [ran, Except.mapError, Prod.mk.injEq] at called
        rw [← called.2]
        exact ⟨post, initial.duplicate⟩
  constructor
  · intro site owner before result after initial called
    suffices fields : CreationFields input after.item ∧ (after.duplicate.getD normalized).items = normalized.items from
      ⟨fields.1, fields.2⟩
    cases site with
    | arguments =>
      dsimp only [callbacks] at called
      split at called
      · simp at called
      · cases ran : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
            ⟨view normalized, normalized.items, none⟩ (memory before) with
        | mk response reached =>
          cases response with
          | ok pair =>
            rcases pair with ⟨slice, handle⟩
            simp only [ran, Prod.mk.injEq, Except.ok.injEq] at called
            rw [← called.2]
            exact ⟨initial.item, takeOwned_borrowed_items normalizationOwnershipCode
                  (Publication.external ops.arguments) allocator _ _ slice handle rfl (congrArg Prod.fst ran)⟩
          | error fault =>
            cases fault <;> simp only [ran, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at called
            all_goals first | contradiction | exact called.2 ▸ ⟨initial.item, initial.duplicate⟩
    | item => exact liftedAttempt .item owner before result after initial called
    | clone => exact liftedAttempt .clone owner before result after initial called
    | append =>
      dsimp only [callbacks] at called
      split at called
      · simp at called
      · have same := congrArg Prod.snd called
        dsimp only at same
        rw [← same]
        exact ⟨initial.item, initial.duplicate⟩
    | publish =>
      dsimp only [callbacks] at called
      cases ran : Publication.publish ops.probe ops.arguments allocator source key normalized (BitVec.ofNat 32 count)
          ⟨graph owner before, memory before⟩ with
      | mk response reached =>
        cases response with
        | ok returned =>
          cases returned
          simp only [ran, Prod.mk.injEq, Except.ok.injEq] at called
          exact called.2 ▸ ⟨initial.item, initial.duplicate⟩
        | error fault =>
          cases fault <;> try { simp [ran] at called }
          rename_i error
          cases error <;> simp only [ran, Prod.mk.injEq, Except.ok.injEq, reduceCtorEq, false_and] at called
          all_goals first | contradiction | exact called.2 ▸ ⟨initial.item, initial.duplicate⟩
  · intro action owner before after initial called
    suffices fields : CreationFields input after.item ∧ (after.duplicate.getD normalized).items = normalized.items from
      ⟨fields.1, fields.2⟩
    cases action with
    | normalized =>
      have same := congrArg Prod.snd called
      dsimp only [callbacks] at same
      rw [← same]
      exact ⟨initial.item, initial.duplicate⟩
    | arguments =>
      dsimp only [callbacks] at called
      cases present : arguments normalized owner before with
      | none => simp [present] at called
      | some slice =>
        simp only [present] at called
        have same := congrArg Prod.snd called
        dsimp only at same
        rw [← same]
        exact ⟨initial.item, initial.duplicate⟩
    | allocation => exact liftedRelease .allocation owner before after initial called
    | value => exact liftedRelease .value owner before after initial called
    | lastValue =>
      dsimp only [callbacks] at called
      cases present : arguments normalized owner before with
      | none => simp [present] at called
      | some slice =>
        simp only [present] at called
        exact liftedRelease .lastValue owner before after initial called
    | pop =>
      have same := congrArg Prod.snd called
      change before = after at same
      exact same ▸ ⟨initial.item, initial.duplicate⟩

theorem callbacks_fields (ops : Operations σ) (allocator count : Nat) (source : View) (input : Value Metadata)
    (key : Key) (normalized : ArgumentSlice) (graph : Storage.State → State Metadata σ → Interner.Heap)
    (admitted : Admitted ops.arguments) :
    Storage.Preserves (callbacks ops allocator count source input key normalized graph) (Fields input normalized) := by
  have valid := callbacks_preserve ops allocator count source input key normalized graph admitted
  have values := callbacks_field_values ops allocator count source input key normalized graph
  constructor
  · intro site owner before result after initial called
    have fields := values.attempt site owner before result after ⟨initial.item, initial.duplicate⟩ called
    exact ⟨valid.attempt site owner before result after initial.valid called, fields.item, fields.duplicate⟩
  · intro action owner before after initial called
    have fields := values.release action owner before after ⟨initial.item, initial.duplicate⟩ called
    exact ⟨valid.release action owner before after initial.valid called, fields.item, fields.duplicate⟩

theorem execution_fields (ops : Operations σ) (allocator : Nat) (source : View) (meaning : Meaning)
    (input : Value Metadata) (key : Key) (normalized : ArgumentSlice) (deterministic : Bool)
    (cells : List Storage.Cell) (before : World (Publication.Effects σ)) (outcome : Option Storage.Outcome)
    (initial : Valid before.memory) (admitted : Admitted ops.arguments)
    (completed : (execution ops allocator source meaning input key normalized deterministic cells before).1.1 = .ok outcome) :
    Fields input normalized (execution ops allocator source meaning input key normalized deterministic cells before).2 :=
  Storage.Program.execute_preserves _ _ _ (Fields input normalized)
    (callbacks_fields ops allocator cells.length source input key normalized _ admitted) _ _ ⟨initial, rfl, rfl⟩ outcome completed

theorem cell_field_values (input : Value Metadata) (key : Key) (normalized : ArgumentSlice) (value : Word)
    (owner : Storage.State) (after : State Metadata σ) (fields : FieldValues input normalized after) :
    (cell input key normalized value owner after).item = input.item ∧
    (cell input key normalized value owner after).arguments = normalized.items ∧
    (cell input key normalized value owner after).sequence = key.sequence := by
  refine ⟨fields.item, ?_, rfl⟩
  simp only [cell, arguments]
  split
  · rfl
  · exact fields.duplicate

theorem cell_fields (input : Value Metadata) (key : Key) (normalized : ArgumentSlice) (value : Word)
    (owner : Storage.State) (after : State Metadata σ) (fields : Fields input normalized after) :
    (cell input key normalized value owner after).item = input.item ∧
    (cell input key normalized value owner after).arguments = normalized.items ∧
    (cell input key normalized value owner after).sequence = key.sequence :=
  cell_field_values input key normalized value owner after ⟨fields.item, fields.duplicate⟩

/-- Key and value binding are consequences of the complete insertion's field
invariant. Only the source descriptor is admitted; no final-cell equality is
supplied as an oracle. Physical assignment/layout refinement is still separate. -/
theorem cell_value_binding (input : Value Metadata) (key : Key) (normalized : ArgumentSlice) (value : Word)
    (owner : Storage.State) (after : State Metadata σ) (fields : FieldValues input normalized after) :
    let candidate := cell input key normalized value owner after
    keyCode.run candidate.item candidate.arguments candidate.sequence =
      keyCode.run input.item normalized.items key.sequence ∧
    candidate.value = (if input.item.kind == 2 then input.item.data else value) := by
  have same := cell_field_values input key normalized value owner after fields
  constructor
  · rw [same.1, same.2.1, same.2.2]
  · simp only [Storage.Cell.value, Storage.Cell.isPush, Storage.Cell.dataValue, same.1]
    rfl

theorem cell_binding (input : Value Metadata) (key : Key) (normalized : ArgumentSlice) (value : Word)
    (owner : Storage.State) (after : State Metadata σ) (fields : Fields input normalized after) :
    let candidate := cell input key normalized value owner after
    keyCode.run candidate.item candidate.arguments candidate.sequence =
      keyCode.run input.item normalized.items key.sequence ∧
    candidate.value = (if input.item.kind == 2 then input.item.data else value) :=
  cell_value_binding input key normalized value owner after ⟨fields.item, fields.duplicate⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
