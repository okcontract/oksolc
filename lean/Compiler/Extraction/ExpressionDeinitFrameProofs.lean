/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionDeinitNativeProofs
import Compiler.Extraction.ExpressionInvalidationFrame

namespace Compiler.Extraction.ExpressionDeinit.Native
open Compiler.Extraction.Memory.Arguments.Normalization
open RepresentativeArray

/-- The native destructor's exact footprint. Empty argument sentinels do not
name a released allocation. The row allocation survives, but its selected
subobject loses initialization; earlier rows retain their actual native fields. -/
structure RunFrame (lifetime index object : Nat) (payload : Option AssemblyItemDeinit.Bytes)
    (arguments : Storage.ArgumentSlice) (before after : Session σ) : Prop where
  registry : ∀ id, id ≠ object → ¬AssemblyItemDeinit.Touches payload id →
    (arguments.items ≠ [] → id ≠ arguments.address) → after.heap id = before.heap id
  allocation : ∀ id, id ≠ lifetime → id ≠ object → ¬AssemblyItemDeinit.Touches payload id →
    (arguments.items ≠ [] → id ≠ arguments.address) → after.memory.heap.lookup id = before.memory.heap.lookup id
  rows : ∀ cells : List Storage.Cell, cells.length = index → DescriptorRelation.Prefix before.memory lifetime cells →
    DescriptorRelation.Prefix after.memory lifetime cells
  dead : ∀ id, before.heap id = none ∧ before.memory.heap.lookup id = none →
    after.heap id = none ∧ after.memory.heap.lookup id = none
  released : ∀ id, id = object ∨ AssemblyItemDeinit.Touches payload id ∨
    (arguments.items ≠ [] ∧ id = arguments.address) →
    after.heap id = none ∧ after.memory.heap.lookup id = none

/-- Derive the footprint from the same reached payload free, item invalidation,
object free, argument free and row invalidation as the production destructor.
No final field read, allocation frame or lifetime preservation is a premise. -/
theorem run_framed (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
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
    ∃ after, run bytes objects external allocator ⟨lifetime, index * 32⟩ before = (.ok (), after) ∧
      RunFrame lifetime index object (AssemblyClone.Physical.payload input) arguments before after.memory := by
  obtain ⟨released, value, objectState, argumentState, after, ran, payloadPost, _, itemInvalidated, valueHeap,
      _, objectPost, argumentCall, argumentPost, rowInvalidated, finalHeap, _, _, _, _, _, _⟩ :=
    run_verified bytes objects external allocator lifetime capacity index object input arguments before initial rowOwned inside
      itemOwned itemRead argumentRead live represented payloadOwned
  have itemFrame := Compiler.ZigAir.Memory.invalidate_frame _ _ _ _ _ itemInvalidated
  have rowFrame := Compiler.ZigAir.Memory.invalidate_frame _ _ _ _ _ rowInvalidated
  have freedFrame (id : Nat) (objectApart : id ≠ object)
      (untouched : ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload input) id)
      (argumentsApart : arguments.items ≠ [] → id ≠ arguments.address) :
      argumentState.heap id = before.heap id ∧ argumentState.memory.heap.lookup id = before.memory.heap.lookup id := by
    have argumentFrame : argumentState.heap id = objectState.heap id ∧
        argumentState.memory.heap.lookup id = objectState.memory.heap.lookup id := by
      by_cases empty : arguments.items = []
      · have same := (Prod.mk.inj ((free_empty external allocator arguments objectState empty).symm.trans argumentCall)).2
        rw [← same]; exact ⟨rfl, rfl⟩
      · exact argumentPost.frame id (argumentsApart empty)
    exact ⟨argumentFrame.1.trans ((objectPost.frame id objectApart).1.trans
        ((congrFun valueHeap id).trans (payloadPost.frame id untouched).1)),
      argumentFrame.2.trans ((objectPost.frame id objectApart).2.trans
        ((itemFrame.2.2 id objectApart).trans (payloadPost.frame id untouched).2))⟩
  have registry (id : Nat) (objectApart : id ≠ object)
      (untouched : ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload input) id)
      (argumentsApart : arguments.items ≠ [] → id ≠ arguments.address) : after.memory.heap id = before.heap id :=
    (congrFun finalHeap id).trans (freedFrame id objectApart untouched argumentsApart).1
  have allocation (id : Nat) (rowApart : id ≠ lifetime) (objectApart : id ≠ object)
      (untouched : ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload input) id)
      (argumentsApart : arguments.items ≠ [] → id ≠ arguments.address) :
      after.memory.memory.heap.lookup id = before.memory.heap.lookup id :=
    (rowFrame.2.2 id rowApart).trans (freedFrame id objectApart untouched argumentsApart).2
  refine ⟨after, ran, registry, allocation, ?_, ?_, ?_⟩
  · intro cells length rows
    obtain ⟨_, ⟨old, registered⟩, _, _, _, _, _⟩ := rowOwned
    have objectApart : lifetime ≠ object := by
      obtain ⟨item, stored⟩ := itemOwned.1
      intro same; rw [← same, registered] at stored; cases stored
    have untouched : ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload input) lifetime := by
      rintro ⟨slice, selected, nonempty, same⟩
      have stored := (payloadOwned slice selected).resolve_left nonempty |>.1
      rw [← same, registered] at stored; cases stored
    have argumentsApart (nonempty : arguments.items ≠ []) : lifetime ≠ arguments.address := by
      have stored := live.resolve_left nonempty
      intro same; rw [← same, registered] at stored; cases stored
    have kept := DescriptorRelation.frame before.memory argumentState.memory lifetime cells rows
      (freedFrame lifetime objectApart untouched argumentsApart).2
    apply Expression.prefix_before_invalidate argumentState.memory after.memory.memory lifetime cells
    · simpa only [length] using rowInvalidated
    · exact kept
  · intro id dead
    have rowApart : id ≠ lifetime := by
      obtain ⟨_, _, cell, found, _⟩ := rowOwned
      intro same; rw [same, found] at dead; cases dead.2
    have objectApart : id ≠ object := by
      obtain ⟨_, cell, found, _⟩ := itemOwned
      intro same; rw [same, found] at dead; cases dead.2
    have untouched : ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload input) id := by
      rintro ⟨slice, selected, nonempty, same⟩
      have stored := (payloadOwned slice selected).resolve_left nonempty |>.1
      rw [same, stored] at dead; cases dead.1
    have argumentsApart (nonempty : arguments.items ≠ []) : id ≠ arguments.address := by
      intro same
      have stored := live.resolve_left nonempty
      rw [same, stored] at dead; cases dead.1
    exact ⟨(registry id objectApart untouched argumentsApart).trans dead.1,
      (allocation id rowApart objectApart untouched argumentsApart).trans dead.2⟩
  · intro id selected
    have objectDead (target : id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload input) id) :
        objectState.heap id = none ∧ objectState.memory.heap.lookup id = none := by
      rcases target with rfl | touched
      · exact objectPost.dead
      · have dead := payloadPost.dead id touched
        have apart : id ≠ object := by
          obtain ⟨slice, chosen, nonempty, same⟩ := touched
          have payload := (payloadOwned slice chosen).resolve_left nonempty |>.1
          obtain ⟨item, stored⟩ := itemOwned.1
          intro equal
          rw [← same, equal, stored] at payload
          cases payload
        exact objectPost.keeps_dead object value.memory objectState id
          ⟨(congrFun valueHeap id).trans dead.1, (itemFrame.2.2 id apart).trans dead.2⟩
    have argumentDead : argumentState.heap id = none ∧ argumentState.memory.heap.lookup id = none := by
      rcases selected with item | payload | ⟨nonempty, rfl⟩
      · exact Payload.free_keeps_dead external allocator arguments objectState argumentState id argumentCall argumentPost
          (objectDead (Or.inl item))
      · exact Payload.free_keeps_dead external allocator arguments objectState argumentState id argumentCall argumentPost
          (objectDead (Or.inr payload))
      · exact argumentPost.dead nonempty
    have rowApart : id ≠ lifetime := by
      obtain ⟨_, ⟨cells, stored⟩, _⟩ := rowOwned
      intro same
      rcases selected with item | ⟨slice, chosen, nonempty, payload⟩ | ⟨nonempty, arguments⟩
      · obtain ⟨value, found⟩ := itemOwned.1
        rw [← item, same, stored] at found
        cases found
      · have found := (payloadOwned slice chosen).resolve_left nonempty |>.1
        rw [← payload, same, stored] at found
        cases found
      · have found := live.resolve_left nonempty
        rw [← arguments, same, stored] at found
        cases found
    exact ⟨(congrFun finalHeap id).trans argumentDead.1, (rowFrame.2.2 id rowApart).trans argumentDead.2⟩

end Compiler.Extraction.ExpressionDeinit.Native
