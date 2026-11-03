/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNativeProjection
import Compiler.Extraction.InternerInsertionFields

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Typed installation changes memory, never the returned clone descriptor.
Rejected installation retains that same descriptor without asserting validity. -/
theorem finish_clone_value (object : Nat) (result : Except AssemblyItem.Creation.Insertion.Fault Bool)
    (before : AssemblyItem.Creation.NativeFields.State σ) :
    (AssemblyItem.Creation.NativeFields.finish object result before).2.clone.value = before.clone.value := by
  cases result with
  | error fault => rfl
  | ok accepted =>
    cases accepted with
    | false => rfl
    | true =>
      cases present : before.clone.value with
      | none => simp only [AssemblyItem.Creation.NativeFields.finish, present]
      | some copied =>
        simp only [AssemblyItem.Creation.NativeFields.finish, present]
        cases installed : AssemblyClone.NativeFields.install copied object before.clone.execution.memory with
        | error fault => exact present
        | ok memory => exact present

/-- Native source admission and typed assignment extend the existing creation
and clone callbacks. Their ordinary outcomes share the existing item-field proof. -/
theorem items_fields (ops : Operations σ) (allocator : Nat) (source : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (normalized : ArgumentSlice) (owner : Storage.State) (start : Frame σ) :
    Storage.Preserves (items ops allocator source input normalized owner start) (CreationFields input) := by
  have kept := item_fields ops allocator input normalized owner start
  have forwarded : ∀ site state before result after, CreationFields input before →
      (let ran := (itemOperations ops allocator input normalized owner start).attempt site state before
       (ran.1.mapError AssemblyItem.Creation.NativeFields.Fault.base, ran.2)) = (.ok result, after) →
      CreationFields input after := by
    intro site state before result after initial called
    cases ran : (itemOperations ops allocator input normalized owner start).attempt site state before with
    | mk response reached =>
      cases response with
      | error fault => simp [ran, Except.mapError] at called
      | ok accepted =>
        simp only [ran, Except.mapError, Prod.mk.injEq, Except.ok.injEq] at called
        exact called.2 ▸ kept.attempt site state before accepted reached initial ran
  constructor
  · intro site state before result after initial called
    cases site with
    | arguments =>
      exact forwarded .arguments state before result after initial (by simpa only [items, AssemblyItem.Creation.NativeFields.operations] using called)
    | item =>
      exact forwarded .item state before result after initial (by simpa only [items, AssemblyItem.Creation.NativeFields.operations] using called)
    | append =>
      exact forwarded .append state before result after initial (by simpa only [items, AssemblyItem.Creation.NativeFields.operations] using called)
    | publish =>
      exact forwarded .publish state before result after initial (by simpa only [items, AssemblyItem.Creation.NativeFields.operations] using called)
    | clone =>
      cases present : before.object with
      | none =>
        exact forwarded .clone state before result after initial (by simpa only [items, AssemblyItem.Creation.NativeFields.operations, present] using called)
      | some object =>
        cases checked : AssemblyClone.NativeFields.checkSource before.clone.execution.memory.memory source input with
        | error fault => simp only [items, AssemblyItem.Creation.NativeFields.operations, present, checked, Prod.mk.injEq, reduceCtorEq, false_and] at called
        | ok done =>
          cases done
          simp only [items, AssemblyItem.Creation.NativeFields.operations, present, checked] at called
          change AssemblyItem.Creation.NativeFields.finish object
            ((itemOperations ops allocator input normalized owner start).attempt .clone state before).1
            ((itemOperations ops allocator input normalized owner start).attempt .clone state before).2 = (.ok result, after) at called
          cases ran : (itemOperations ops allocator input normalized owner start).attempt .clone state before with
          | mk response reached =>
            rw [ran] at called
            cases response with
            | error fault => simp only [AssemblyItem.Creation.NativeFields.finish, Prod.mk.injEq, reduceCtorEq, false_and] at called
            | ok accepted =>
              have post := kept.attempt .clone state before accepted reached initial ran
              have value := finish_clone_value object (.ok accepted) reached
              rw [called] at value
              change (after.clone.value.getD input).item = input.item
              rw [value]
              exact post
  · intro action state before after initial called
    cases ran : (itemOperations ops allocator input normalized owner start).release action state before with
    | mk response reached =>
      change (let ran := (itemOperations ops allocator input normalized owner start).release action state before
        (ran.1.mapError AssemblyItem.Creation.NativeFields.Fault.base, ran.2)) = (.ok (), after) at called
      cases response with
      | error fault => simp [ran, Except.mapError] at called
      | ok done =>
        cases done
        simp only [ran, Except.mapError, Prod.mk.injEq] at called
        exact called.2 ▸ kept.release action state before reached initial ran

/-- The actual native callbacks preserve candidate descriptors on both ordinary
allocation outcomes. Native memory validity is deliberately a separate claim. -/
theorem callbacks_field_values (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (rows : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (growth : Option (Growth.Registered.Callbacks σ)) :
    Storage.Preserves (callbacks ops allocate safety allocator container source address input key normalized rows value graph growth)
      (FieldValues input normalized) := by
  have kept := Insertion.callbacks_field_values ops allocator rows.length source input key normalized graph
  have baseAttempt : ∀ site owner before result after, FieldValues input normalized before →
      (let ran := (Insertion.callbacks ops allocator rows.length source input key normalized graph).attempt site owner before
       (ran.1.mapError Fault.base, ran.2)) = (.ok result, after) → FieldValues input normalized after := by
    intro site owner before result after initial called
    cases ran : (Insertion.callbacks ops allocator rows.length source input key normalized graph).attempt site owner before with
    | mk response reached =>
      cases response with
      | error fault => simp [ran, Except.mapError] at called
      | ok accepted =>
        simp only [ran, Except.mapError, Prod.mk.injEq, Except.ok.injEq] at called
        exact called.2 ▸ kept.attempt site owner before accepted reached initial ran
  have baseRelease : ∀ action owner before after, FieldValues input normalized before →
      (let ran := (Insertion.callbacks ops allocator rows.length source input key normalized graph).release action owner before
       (ran.1.mapError Fault.base, ran.2)) = (.ok (), after) → FieldValues input normalized after := by
    intro action owner before after initial called
    cases ran : (Insertion.callbacks ops allocator rows.length source input key normalized graph).release action owner before with
    | mk response reached =>
      cases response with
      | error fault => simp [ran, Except.mapError] at called
      | ok done =>
        cases done
        simp only [ran, Except.mapError, Prod.mk.injEq] at called
        exact called.2 ▸ kept.release action owner before reached initial ran
  have itemAttempt : ∀ site owner before result after, FieldValues input normalized before →
      (let ran := (items ops allocator address input normalized owner before).attempt site owner before.item
       (ran.1.mapError Fault.item, { before with item := ran.2 })) = (.ok result, after) → FieldValues input normalized after := by
    intro site owner before result after initial called
    cases ran : (items ops allocator address input normalized owner before).attempt site owner before.item with
    | mk response reached =>
      cases response with
      | error fault => simp [ran, Except.mapError] at called
      | ok accepted =>
        have post := (items_fields ops allocator address input normalized owner before).attempt site owner before.item accepted reached initial.item ran
        simp only [ran, Except.mapError, Prod.mk.injEq, Except.ok.injEq] at called
        rw [← called.2]
        exact ⟨post, initial.duplicate⟩
  constructor
  · intro site owner before result after initial called
    cases site with
    | arguments => exact baseAttempt .arguments owner before result after initial called
    | publish => exact baseAttempt .publish owner before result after initial called
    | item => exact itemAttempt .item owner before result after initial called
    | clone => exact itemAttempt .clone owner before result after initial called
    | append =>
      change append safety allocate allocator container rows input key normalized value owner before growth = (.ok result, after) at called
      unfold append at called
      split at called
      · cases called
      · cases growth with
        | none =>
          cases ran : Append.Registered.run safety (allocation allocate) allocator container rows
              (cell input key normalized value owner before) (memory before) with
          | mk response reached =>
            have same := congrArg Prod.snd called
            simp only [ran] at same
            rw [← same]
            exact ⟨initial.item, initial.duplicate⟩
        | some growth =>
          cases ran : Append.Registered.runWithGrowth (growthCallbacks growth) safety (allocation allocate) allocator container rows
              (cell input key normalized value owner before) (memory before) with
          | mk response reached =>
            have same := congrArg Prod.snd called
            simp only [ran] at same
            rw [← same]
            exact ⟨initial.item, initial.duplicate⟩
  · intro action owner before after initial called
    cases action with
    | normalized => exact baseRelease .normalized owner before after initial called
    | arguments => exact baseRelease .arguments owner before after initial called
    | allocation => exact baseRelease .allocation owner before after initial called
    | pop =>
      have same := congrArg Prod.snd called
      change (pop allocator container before).2 = after at same
      unfold pop at same
      cases ran : Pop.Registered.run allocator container (memory before) with
      | mk result reached =>
        simp only [ran] at same
        rw [← same]
        exact ⟨initial.item, initial.duplicate⟩
    | value =>
      change releaseValue ops allocator before = (.ok (), after) at called
      unfold releaseValue at called
      cases present : before.item.object with
      | none => simp [present] at called
      | some object =>
        cases ran : AssemblyItemDeinit.Native.run (release ops.bytes) allocator ⟨object, 0⟩ (memory before) with
        | mk result reached =>
          simp only [present, ran] at called
          cases result with
          | error fault => cases called
          | ok done =>
            cases done
            cases called
            exact ⟨rfl, initial.duplicate⟩
    | lastValue =>
      change releaseLast ops allocator container before = (.ok (), after) at called
      unfold releaseLast at called
      cases selected : Last.select (memory before).memory (Owner.headerAddress ⟨container, 0⟩) with
      | error fault => simp [selected] at called
      | ok descriptor =>
        cases ran : ExpressionDeinit.Native.run (release ops.bytes) (release ops.objects)
            (Publication.external ops.arguments) allocator descriptor (memory before) with
        | mk result reached =>
          simp only [selected, ran] at called
          cases result with
          | error fault => cases called
          | ok done =>
            cases done
            cases called
            exact ⟨rfl, initial.duplicate⟩

theorem execution_field_values (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container : Nat) (source : View) (address : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice) (deterministic : Bool)
    (rows : List Storage.Cell) (before : World (Publication.Effects σ)) (growth : Option (Growth.Registered.Callbacks σ))
    (outcome : Option Storage.Outcome)
    (completed : (execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth).1.1 = .ok outcome) :
    FieldValues input normalized (execution ops allocate safety allocator container source address meaning input key normalized deterministic rows before growth).2 :=
  Storage.Program.execute_preserves _ _ _ (FieldValues input normalized)
    (callbacks_field_values ops allocate safety allocator container source address input key normalized rows _ _ growth)
    _ _ ⟨rfl, rfl⟩ outcome completed

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
