/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionDeinitNativeProofs
import Compiler.Extraction.RepresentativeOwnerLayout

namespace Compiler.Extraction.ExpressionDeinit.Native
open Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.ZigAir.Memory (Address)
open RepresentativeArray

/-- The captured owner is separate from the destroyed item, byte payload,
argument array and selected row by their native types. Derive its complete
allocation frame from the same destructor's reached primitive witnesses. The
owner may be stack or persistent and need not have a registry entry. -/
theorem run_owner_verified (runtimeSafety : Bool)
    (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ) (external : External σ)
    (allocator owner lifetime capacity index object : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (input : AssemblyClone.NativeFields.ItemValue) (arguments : Storage.ArgumentSlice) (before : Session σ)
    (initial : Valid before)
    (ownerFound : before.memory.heap.lookup owner = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (rowOwned : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity before)
    (inside : index < capacity) (itemOwned : AssemblyItem.Owned allocator object before)
    (itemRead : Fields.item before.memory ⟨lifetime, index * 32⟩ = .ok ⟨object, 0⟩)
    (argumentRead : Expression.readField before.memory false ⟨lifetime, index * 32⟩ Expression.argumentsOffset =
      .ok (.slice Expression.argumentsType ⟨arguments.address, 0⟩ arguments.items.length))
    (live : Memory.SliceValid allocator before.heap arguments)
    (represented : AssemblyClone.NativeFields.Represents before.memory ⟨object, 0⟩ input)
    (payloadOwned : ∀ slice, AssemblyClone.Physical.payload input = some slice → AssemblyItemDeinit.Owned allocator slice before) :
    ∃ after, run bytes objects external allocator ⟨lifetime, index * 32⟩ before = (.ok (), after) ∧
      Valid after.memory ∧ after.invalidated = true ∧
      after.memory.heap lifetime = before.heap lifetime ∧ Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity after.memory ∧
      after.memory.heap owner = before.heap owner ∧ after.memory.memory.heap.lookup owner = before.memory.heap.lookup owner ∧
      after.memory.memory.nextId = before.memory.nextId ∧ after.memory.memory.nextAddress = before.memory.nextAddress ∧
      (∀ argumentAllocator survivor, Memory.SliceValid argumentAllocator before.heap survivor →
        (arguments.items ≠ [] → survivor.items ≠ [] → survivor.address ≠ arguments.address) →
        Memory.SliceValid argumentAllocator after.memory.heap survivor) := by
  have apartItem : owner ≠ object := by
    obtain ⟨_, cell, found, typed, _, _⟩ := itemOwned
    exact before.memory.heap.lookup_ne_of_type_ne owner object ownerCell cell ownerFound found
      (by rw [ownerTyped, typed]; cases runtimeSafety <;> decide)
  have apartRow : owner ≠ lifetime := by
    obtain ⟨_, _, cell, found, typed, _, _⟩ := rowOwned
    exact before.memory.heap.lookup_ne_of_type_ne owner lifetime ownerCell cell ownerFound found
      (by simp [ownerTyped, typed, Owner.viewType, Backing.type])
  have untouched : ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload input) owner := by
    rintro ⟨slice, selected, nonempty, same⟩
    obtain ⟨_, cell, found, typed, _⟩ := (payloadOwned slice selected).resolve_left nonempty
    exact before.memory.heap.lookup_ne_of_type_ne owner slice.address ownerCell cell ownerFound found
      (by simp [ownerTyped, typed, Owner.viewType]) same
  have apartArguments (nonempty : arguments.items ≠ []) : owner ≠ arguments.address := by
    obtain ⟨⟨cell, found, typed, _, _⟩, _⟩ := initial.related allocator arguments.address arguments.items nonempty
      (live.resolve_left nonempty)
    exact before.memory.heap.lookup_ne_of_type_ne owner arguments.address ownerCell cell ownerFound found
      (by simp [ownerTyped, typed, Owner.viewType])
  obtain ⟨released, value, objectState, argumentState, after, ran, payloadPost, _, itemInvalidated, valueHeap,
      _, objectPost, argumentCall, argumentPost, rowInvalidated, finalHeap, _, marker, valid, registry, remainingOwned, survivorFrame⟩ :=
    run_verified bytes objects external allocator lifetime capacity index object input arguments before initial rowOwned inside
      itemOwned itemRead argumentRead live represented payloadOwned
  have itemFrame := Compiler.ZigAir.Memory.invalidate_frame _ _ _ _ _ itemInvalidated
  have rowFrame := Compiler.ZigAir.Memory.invalidate_frame _ _ _ _ _ rowInvalidated
  have valueOwner := payloadPost.frame owner untouched
  have objectOwner := objectPost.frame owner apartItem
  have argumentOwner : argumentState.heap owner = objectState.heap owner ∧
      argumentState.memory.heap.lookup owner = objectState.memory.heap.lookup owner := by
    by_cases empty : arguments.items = []
    · have same := (Prod.mk.inj ((free_empty external allocator arguments objectState empty).symm.trans argumentCall)).2
      rw [← same]
      exact ⟨rfl, rfl⟩
    · exact argumentPost.frame owner (apartArguments empty)
  exact ⟨after, ran, valid, marker, registry, remainingOwned,
    (congrFun finalHeap owner).trans (argumentOwner.1.trans (objectOwner.1.trans ((congrFun valueHeap owner).trans valueOwner.1))),
    (rowFrame.2.2 owner apartRow).trans (argumentOwner.2.trans (objectOwner.2.trans ((itemFrame.2.2 owner apartItem).trans valueOwner.2))),
    rowFrame.1.trans (argumentPost.nextId.trans (objectPost.nextId.trans (itemFrame.1.trans payloadPost.nextId))),
    rowFrame.2.1.trans (argumentPost.nextAddress.trans (objectPost.nextAddress.trans (itemFrame.2.1.trans payloadPost.nextAddress))), survivorFrame⟩

end Compiler.Extraction.ExpressionDeinit.Native
