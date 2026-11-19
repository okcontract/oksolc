/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionDeinitNative
import Compiler.Extraction.RepresentativeBackingRelease
import Compiler.Extraction.ExpressionPayload

namespace Compiler.Extraction.ExpressionDeinit.Native
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.ZigAir.Memory (Address)

/-- The existing vector ownership tag separates row storage from all registered
argument arrays. Typed invalidation therefore preserves the same session; no
argument-content frame or final validity is assumed. -/
theorem invalidate_session (allocator lifetime capacity index : Nat) (before : Session σ)
    (initial : Valid before)
    (owned : RepresentativeArray.Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity before)
    (inside : index < capacity) :
    ∃ after, Expression.invalidate before.memory ⟨lifetime, index * 32⟩ = .ok after.memory ∧
      Valid after ∧ after.heap = before.heap ∧ after.effects = before.effects := by
  obtain ⟨_, ⟨cells, registered⟩, cell, found, typed, writable, _⟩ := owned
  obtain ⟨memory, executed, valid, _, _, _, _⟩ := Expression.invalidate_array before.memory lifetime capacity index cell
    initial.memory found typed writable inside
  refine ⟨{ before with memory }, executed, ?_, rfl, rfl⟩
  apply Valid.memory_frame before memory initial valid
    (Compiler.ZigAir.Memory.invalidate_retains_shape _ _ _ _ _ executed)
  intro owner id values stored
  apply (Compiler.ZigAir.Memory.invalidate_frame _ _ _ _ _ executed).2.2 id
  intro same
  subst id
  rw [registered] at stored
  cases stored

/-- Complete native row destruction from initial ownership and field contents.
Registry tags derive separation; earlier frees and item invalidation derive the
later field reads. The witnesses retain exact reached primitive calls and their
postconditions, including the state passed to allocator callbacks. No final
field read, preservation contract or successful cleanup is a premise. -/
theorem run_verified (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator lifetime capacity index object : Nat) (input : AssemblyClone.NativeFields.ItemValue)
    (arguments : Storage.ArgumentSlice) (before : Session σ)
    (initial : Valid before)
    (rowOwned : RepresentativeArray.Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity before)
    (inside : index < capacity) (itemOwned : AssemblyItem.Owned allocator object before)
    (itemRead : Fields.item before.memory ⟨lifetime, index * 32⟩ = .ok ⟨object, 0⟩)
    (argumentRead : Expression.readField before.memory false ⟨lifetime, index * 32⟩ Expression.argumentsOffset =
      .ok (.slice Expression.argumentsType ⟨arguments.address, 0⟩ arguments.items.length))
    (live : Memory.SliceValid allocator before.heap arguments)
    (represented : AssemblyClone.NativeFields.Represents before.memory ⟨object, 0⟩ input)
    (payloadOwned : ∀ slice, AssemblyClone.Physical.payload input = some slice → AssemblyItemDeinit.Owned allocator slice before) :
    ∃ released value objectState argumentState after,
      run bytes objects external allocator ⟨lifetime, index * 32⟩ before = (.ok (), after) ∧
      AssemblyItemDeinit.Post (AssemblyClone.Physical.payload input) before released ∧
      AssemblyItemDeinit.Native.run bytes allocator ⟨object, 0⟩ before = (.ok (), value) ∧
      Compiler.ZigAir.Memory.invalidate released.memory.memory true AssemblyItem.viewType ⟨object, 0⟩ = .ok value.memory.memory ∧
      value.memory.heap = released.memory.heap ∧
      AssemblyItem.destroy objects allocator object value.memory = (.ok (), objectState) ∧
      AssemblyItem.Released object value.memory objectState ∧
      free external allocator arguments objectState = (.ok (), argumentState) ∧
      Memory.Arguments.ReleasePost objectState.heap objectState.memory allocator arguments argumentState.heap argumentState.memory ∧
      Expression.invalidate argumentState.memory ⟨lifetime, index * 32⟩ = .ok after.memory.memory ∧
      after.memory.heap = argumentState.heap ∧ after.memory.effects = argumentState.effects ∧
      after.invalidated = true ∧ Valid after.memory ∧ after.memory.heap lifetime = before.heap lifetime ∧
      RepresentativeArray.Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity after.memory ∧
      (∀ argumentAllocator survivor, Memory.SliceValid argumentAllocator before.heap survivor →
        (arguments.items ≠ [] → survivor.items ≠ [] → survivor.address ≠ arguments.address) →
        Memory.SliceValid argumentAllocator after.memory.heap survivor) := by
  obtain ⟨_, ⟨cells, registered⟩, backing, found, typed, writable, persistent⟩ := rowOwned
  have rowApart : lifetime ≠ object := by
    obtain ⟨item, stored⟩ := itemOwned.1
    intro same
    rw [← same, registered] at stored
    cases stored
  have rowUntouched : ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload input) lifetime := by
    rintro ⟨slice, selected, nonempty, same⟩
    have stored := (payloadOwned slice selected).resolve_left nonempty |>.1
    rw [← same, registered] at stored
    cases stored
  have argumentApart (nonempty : arguments.items ≠ []) : arguments.address ≠ lifetime := by
    have stored := live.resolve_left nonempty
    intro same
    rw [same, registered] at stored
    cases stored
  obtain ⟨released, value, valueCall, _, payloadPost, itemInvalidated, valueValid, stillOwned, valueHeap, _, _⟩ :=
    AssemblyItemDeinit.Native.run_verified bytes allocator object input before initial itemOwned represented payloadOwned
  have valueRow : value.memory.heap lifetime = before.heap lifetime ∧
      value.memory.memory.heap.lookup lifetime = before.memory.heap.lookup lifetime :=
    ⟨(congrFun valueHeap lifetime).trans (payloadPost.frame lifetime rowUntouched).1,
      ((Compiler.ZigAir.Memory.invalidate_frame _ _ _ _ _ itemInvalidated).2.2 lifetime rowApart).trans
        (payloadPost.frame lifetime rowUntouched).2⟩
  have valueArguments : Memory.SliceValid allocator value.memory.heap arguments := by
    rw [valueHeap]
    exact payloadPost.arguments allocator arguments live
  obtain ⟨objectState, objectCall, objectPost, _⟩ :=
    AssemblyItem.destroy_verified objects allocator object value.memory valueValid stillOwned
  have objectRow := objectPost.frame lifetime rowApart
  have objectArguments := objectPost.arguments object value.memory objectState allocator stillOwned allocator arguments valueArguments
  have secondRead : Fields.item value.memory.memory ⟨lifetime, index * 32⟩ = .ok ⟨object, 0⟩ :=
    (Fields.item_frame before.memory value.memory.memory _ valueRow.2).trans itemRead
  have thirdRead : Fields.arguments objectState ⟨lifetime, index * 32⟩ = .ok arguments :=
    Fields.arguments_read objectState _ allocator arguments
      ((Expression.readField_frame before.memory objectState.memory false _ Expression.argumentsOffset
        (objectRow.2.trans valueRow.2)).trans argumentRead) objectArguments
  obtain ⟨argumentState, argumentCall, argumentValid, argumentPost, _⟩ :=
    free_valid external allocator arguments objectState objectPost.valid objectArguments
  have argumentRow : argumentState.heap lifetime = objectState.heap lifetime ∧
      argumentState.memory.heap.lookup lifetime = objectState.memory.heap.lookup lifetime := by
    by_cases empty : arguments.items = []
    · have same := (Prod.mk.inj ((free_empty external allocator arguments objectState empty).symm.trans argumentCall)).2
      rw [← same]
      exact ⟨rfl, rfl⟩
    · exact argumentPost.frame lifetime (Ne.symm (argumentApart empty))
  have registryFrame := argumentRow.1.trans (objectRow.1.trans valueRow.1)
  have backingFrame := argumentRow.2.trans (objectRow.2.trans valueRow.2)
  have remainingOwned : RepresentativeArray.Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity argumentState :=
    ⟨rfl, ⟨cells, registryFrame.trans registered⟩, backing, backingFrame.trans found, typed, writable, persistent⟩
  obtain ⟨final, invalidated, finalValid, finalHeap, finalEffects⟩ :=
    invalidate_session allocator lifetime capacity index argumentState argumentValid remainingOwned inside
  obtain ⟨finalBacking, finalFound, sameShape⟩ :=
    (Compiler.ZigAir.Memory.invalidate_retains_shape _ _ _ _ _ invalidated) lifetime backing (backingFrame.trans found)
  have finalOwned : RepresentativeArray.Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity final :=
    ⟨rfl, ⟨cells, (congrFun finalHeap lifetime).trans (registryFrame.trans registered)⟩,
      finalBacking, finalFound, sameShape.2.1.trans typed, sameShape.2.2.1.trans writable, sameShape.2.2.2.trans persistent⟩
  have first := item_stage bytes objects external allocator ⟨lifetime, index * 32⟩ ⟨object, 0⟩ before itemRead
  have second := allocation_stage bytes objects external allocator object ⟨lifetime, index * 32⟩ value.memory secondRead
  have third := arguments_stage bytes objects external allocator ⟨lifetime, index * 32⟩ arguments objectState thirdRead
  have fourth := invalidation_stage bytes objects external allocator ⟨lifetime, index * 32⟩ argumentState
  rw [valueCall] at first
  rw [objectCall] at second
  rw [argumentCall] at third
  rw [invalidated] at fourth
  have finalSession : { argumentState with memory := final.memory } = final := by
    cases final
    simp only [Session.mk.injEq] at finalHeap finalEffects ⊢
    exact ⟨finalHeap.symm, True.intro, finalEffects.symm⟩
  simp only [finalSession] at fourth
  refine ⟨released, value, objectState, argumentState, ⟨final, true⟩, ?_, payloadPost, valueCall, itemInvalidated,
    valueHeap, objectCall, objectPost, argumentCall, argumentPost, invalidated, finalHeap, finalEffects, rfl,
    finalValid, (congrFun finalHeap lifetime).trans registryFrame, finalOwned, ?_⟩
  · simp only [run, expressionDeinitCode, executeStages, first, second, third, fourth, Except.mapError]
  · intro argumentAllocator survivor survivorLive separate
    have valueLive : Memory.SliceValid argumentAllocator value.memory.heap survivor := by
      rw [valueHeap]
      exact payloadPost.arguments argumentAllocator survivor survivorLive
    have objectLive := objectPost.arguments object value.memory objectState allocator stillOwned
      argumentAllocator survivor valueLive
    rw [finalHeap]
    by_cases empty : arguments.items = []
    · have same := (Prod.mk.inj ((free_empty external allocator arguments objectState empty).symm.trans argumentCall)).2
      rw [← same]
      exact objectLive
    · rcases objectLive with survivorEmpty | survivorStored
      · exact Or.inl survivorEmpty
      · by_cases survivorEmpty : survivor.items = []
        · exact Or.inl survivorEmpty
        · exact Or.inr ((argumentPost.frame survivor.address (separate empty survivorEmpty)).1.trans survivorStored)

end Compiler.Extraction.ExpressionDeinit.Native
