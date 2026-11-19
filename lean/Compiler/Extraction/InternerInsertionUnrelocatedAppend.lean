/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionFirstOwnership
import Compiler.Extraction.InternerInsertionPreparedRollback
import Compiler.Extraction.RepresentativeRegisteredFirstAppend
import Compiler.Extraction.RepresentativeRegisteredGrowthAppendProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- First and spare append expose the same physical owners for publication or transfer. The
empty sentinel excludes no allocation; a first backing is fresh. Optional
growth callbacks do not change either source branch. This is an append proof,
not a final graph or publication-preservation assumption. -/
theorem unrelocated_append_owned_at (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container oldCapacity object : Nat) (oldData : Compiler.ZigAir.Memory.Address)
    (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (input stored : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (ownership : Storage.State) (middle : Session (Publication.Effects σ)) (ready : Frame σ)
    (growth : Option (Growth.Registered.Callbacks σ))
    (installedPost : AssemblyClone.NativeFields.Installed allocator object stored middle (memory ready))
    (objectPresent : ready.item.object = some object)
    (clonePresent : ready.item.clone.value = some stored)
    (argumentsPresent : arguments normalized ownership ready = some operands)
    (ownerFound : (memory ready).memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType safety) (ownerWritable : ownerCell.writable = true)
    (header : readHeader (memory ready).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType oldData cells.length, .scalar (.int false 64 oldCapacity)))
    (bounded : cells.length ≤ oldCapacity)
    (storage : oldCapacity ≠ 0 →
      Backing.Release.Owned allocator oldData oldCapacity (memory ready) ∧
      Memory.Vector allocator (memory ready).heap oldData.allocation cells ∧
      DescriptorRelation.Prefix (memory ready).memory oldData.allocation cells)
    (selected : oldCapacity = 0 ∨ cells.length < oldCapacity)
    (first : oldCapacity = 0 → ∃ base effects,
      allocate allocator 160 8 (memory ready).effects.allocator = (some base, effects) ∧
      Compiler.ZigAir.Memory.RegionAllocation.Fits (memory ready).memory ⟨160, 8⟩ base ∧
      Owner.NativeLock.checkHeader (memory ready).memory (Owner.headerAddress ⟨container, 0⟩) = .ok ())
    (room : cells.length < 2 ^ 32 - 1)
    (operandsBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit) :
    let row : Storage.Cell := ⟨stored.item, value, object, operands.items, key.sequence, operands.address⟩
    ∃ lifetime capacity appended finalOwner,
      append safety allocate allocator container cells input key normalized value ownership ready growth = (.ok true, appended) ∧
      append safety allocate allocator container cells input key normalized value ownership ready = (.ok true, appended) ∧
      Valid (memory appended) ∧ (memory appended).effects.keys = (memory ready).effects.keys ∧
      (memory appended).memory.heap.lookup container = some finalOwner ∧
      finalOwner.type = Owner.viewType safety ∧ finalOwner.writable = true ∧
      Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory appended) ∧
      cells.length < capacity ∧ Memory.Vector allocator (memory appended).heap lifetime (cells ++ [row]) ∧
      readHeader (memory appended).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)) ∧
      ExpressionDeinit.Native.Fields.item (memory appended).memory ⟨lifetime, cells.length * 32⟩ = .ok ⟨object, 0⟩ ∧
      Expression.readField (memory appended).memory false ⟨lifetime, cells.length * 32⟩ Expression.argumentsOffset =
        .ok (.slice Expression.argumentsType ⟨operands.address, 0⟩ operands.items.length) ∧
      AssemblyItem.Owned allocator object (memory appended) ∧
      AssemblyClone.NativeFields.Represents (memory appended).memory ⟨object, 0⟩ stored ∧
      (∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice (memory appended)) ∧
      (∀ argumentAllocator slice, Memory.SliceValid argumentAllocator (memory ready).heap slice →
        Memory.SliceValid argumentAllocator (memory appended).heap slice) ∧
      DescriptorRelation.Prefix (memory appended).memory lifetime (cells ++ [row]) ∧
      (∀ id block, (memory ready).heap id = some block →
        (oldCapacity ≠ 0 → id ≠ oldData.allocation) → (memory appended).heap id = some block) ∧
      (∀ id native, (memory ready).memory.heap.lookup id = some native → id ≠ container →
        (oldCapacity ≠ 0 → id ≠ oldData.allocation) →
        (memory appended).memory.heap.lookup id = some native ∧
        (memory appended).heap id = (memory ready).heap id ∧ id ≠ lifetime) := by
  dsimp only
  have fields := Append.readHeader_parts (memory ready).memory (Owner.headerAddress ⟨container, 0⟩) _ _ header
  by_cases zero : oldCapacity = 0
  · subst oldCapacity
    have empty : cells = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst cells
    obtain ⟨base, allocationEffects, allocated, fits, unlocked⟩ := first rfl
    obtain ⟨appended, finalOwner, run, valid, effects, found, typed, writable, owned, vector, finalHeader,
        itemRead, argumentRead, itemOwned, represented, payloadOwned, argumentsKept, _, _, rows, _, registryFrame, nativeFrame⟩ :=
      first_append_owned allocate safety allocator container object base ownerCell oldData input stored key normalized operands value
        ownership middle ready allocationEffects installedPost objectPresent clonePresent argumentsPresent ownerFound ownerTyped ownerWritable
        fields.1 fields.2 operandsBound allocated fits unlocked
    have same : append safety allocate allocator container [] input key normalized value ownership ready growth =
        append safety allocate allocator container [] input key normalized value ownership ready := by
      cases growth with
      | none => rfl
      | some growthCalls =>
        have preparedCell : cell input key normalized value ownership ready =
            ⟨stored.item, value, object, operands.items, key.sequence, operands.address⟩ := by
          simp only [cell, objectPresent, clonePresent, argumentsPresent, Option.getD_some]
        simp only [append, objectPresent, clonePresent, argumentsPresent, Option.isNone_some,
          Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        rw [Append.Registered.first_same safety (growthCallbacks growthCalls) (allocation allocate)
          allocator container base (memory ready) ownerCell oldData (cell input key normalized value ownership ready)
          { (memory ready).effects with allocator := allocationEffects } installedPost.valid ownerFound ownerTyped ownerWritable
          fields.1 fields.2 (by simpa only [preparedCell] using operandsBound)
          (by simp only [allocation, allocated]) fits unlocked]
    refine ⟨(memory ready).memory.nextId, 5, appended, finalOwner, same.trans run, run, valid,
      (by rw [effects]), found, typed, writable, owned, by decide, vector, finalHeader, itemRead, argumentRead,
      itemOwned, represented, payloadOwned, argumentsKept, rows, ?_, ?_⟩
    · intro id block stored _
      have fresh : id ≠ (memory ready).memory.nextId := by
        obtain ⟨native, found, _⟩ := installedPost.valid.injected id block stored
        have bound := (Compiler.ZigAir.Memory.valid_lookup _ _ native installedPost.valid.memory found).1
        omega
      exact (registryFrame id fresh).trans stored
    · intro id native located apart _
      have fresh : id ≠ (memory ready).memory.nextId := by
        have bound := (Compiler.ZigAir.Memory.valid_lookup (memory ready).memory id native installedPost.valid.memory located).1
        omega
      exact ⟨(nativeFrame id apart fresh).trans located, registryFrame id fresh, fresh⟩
  · have spare : cells.length < oldCapacity := selected.resolve_left zero
    obtain ⟨owned, vector, descriptors⟩ := storage zero
    obtain ⟨root, _, backing, backingFound, backingTyped, backingWritable, _⟩ := owned
    rcases oldData with ⟨oldLifetime, offset⟩
    change offset = 0 at root
    subst offset
    obtain ⟨appended, finalOwner, run, valid, effects, found, typed, writable, owned, vector, finalHeader,
        itemRead, argumentRead, itemOwned, represented, payloadOwned, argumentsKept, _, _, rows, _, registryFrame, nativeFrame, _⟩ :=
      spare_append_owned allocate safety allocator container oldLifetime oldCapacity object ownerCell backing input stored key normalized operands
        cells value ownership middle ready installedPost objectPresent clonePresent argumentsPresent ownerFound ownerTyped ownerWritable
        backingFound backingTyped backingWritable fields.1 fields.2 vector descriptors spare room operandsBound
    have same : append safety allocate allocator container cells input key normalized value ownership ready growth =
        append safety allocate allocator container cells input key normalized value ownership ready := by
      cases growth with
      | none => rfl
      | some growthCalls =>
        simp only [append, objectPresent, clonePresent, argumentsPresent, Option.isNone_some,
          Bool.or_self, Bool.false_eq_true, ↓reduceIte]
        rw [Append.Registered.spare_same safety (memory ready) allocator container oldLifetime oldCapacity ownerCell cells
          (cell input key normalized value ownership ready) (allocation allocate) (growthCallbacks growthCalls)
          installedPost.valid ownerFound ownerTyped fields.1 fields.2 spare
          (by simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega)]
    refine ⟨oldLifetime, oldCapacity, appended, finalOwner, same.trans run, run, valid, congrArg (·.keys) effects,
      found, typed, writable, owned, spare, vector, finalHeader, itemRead, argumentRead,
      itemOwned, represented, payloadOwned, argumentsKept, rows, ?_, ?_⟩
    · intro id block stored oldApart
      exact (registryFrame id (oldApart zero)).trans stored
    · intro id native located apart oldApart
      exact ⟨(nativeFrame id apart (oldApart zero)).trans located, registryFrame id (oldApart zero), oldApart zero⟩

/-- The original publication preparation is a specialization of the ownership-independent append. -/
theorem unrelocated_append_owned (allocate : Backing.Registry.Allocate σ) (safety : Bool)
    (allocator container oldCapacity object : Nat) (oldData : Compiler.ZigAir.Memory.Address)
    (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (input stored : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (middle installed : Session (Publication.Effects σ))
    (growth : Option (Growth.Registered.Callbacks σ))
    (installedPost : AssemblyClone.NativeFields.Installed allocator object stored middle installed)
    (ownerFound : installed.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType safety) (ownerWritable : ownerCell.writable = true)
    (header : readHeader installed.memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType oldData cells.length, .scalar (.int false 64 oldCapacity)))
    (bounded : cells.length ≤ oldCapacity)
    (storage : oldCapacity ≠ 0 →
      Backing.Release.Owned allocator oldData oldCapacity installed ∧
      Memory.Vector allocator installed.heap oldData.allocation cells ∧
      DescriptorRelation.Prefix installed.memory oldData.allocation cells)
    (selected : oldCapacity = 0 ∨ cells.length < oldCapacity)
    (first : oldCapacity = 0 → ∃ base effects,
      allocate allocator 160 8 installed.effects.allocator = (some base, effects) ∧
      Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base ∧
      Owner.NativeLock.checkHeader installed.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ())
    (room : cells.length < 2 ^ 32 - 1)
    (operandsBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit) :
    let ready := preparedFrame object stored operands installed
    let row : Storage.Cell := ⟨stored.item, value, object, operands.items, key.sequence, operands.address⟩
    ∃ lifetime capacity appended finalOwner,
      append safety allocate allocator container cells input key normalized value preparationOwnership ready growth = (.ok true, appended) ∧
      append safety allocate allocator container cells input key normalized value preparationOwnership ready = (.ok true, appended) ∧
      Valid (memory appended) ∧ (memory appended).effects.keys = installed.effects.keys ∧
      (memory appended).memory.heap.lookup container = some finalOwner ∧
      finalOwner.type = Owner.viewType safety ∧ finalOwner.writable = true ∧
      Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory appended) ∧
      cells.length < capacity ∧ Memory.Vector allocator (memory appended).heap lifetime (cells ++ [row]) ∧
      readHeader (memory appended).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)) ∧
      ExpressionDeinit.Native.Fields.item (memory appended).memory ⟨lifetime, cells.length * 32⟩ = .ok ⟨object, 0⟩ ∧
      Expression.readField (memory appended).memory false ⟨lifetime, cells.length * 32⟩ Expression.argumentsOffset =
        .ok (.slice Expression.argumentsType ⟨operands.address, 0⟩ operands.items.length) ∧
      AssemblyItem.Owned allocator object (memory appended) ∧
      AssemblyClone.NativeFields.Represents (memory appended).memory ⟨object, 0⟩ stored ∧
      (∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice (memory appended)) ∧
      (∀ argumentAllocator slice, Memory.SliceValid argumentAllocator installed.heap slice →
        Memory.SliceValid argumentAllocator (memory appended).heap slice) ∧
      DescriptorRelation.Prefix (memory appended).memory lifetime (cells ++ [row]) ∧
      (∀ id native, installed.memory.heap.lookup id = some native → id ≠ container →
        (oldCapacity ≠ 0 → id ≠ oldData.allocation) →
        (memory appended).memory.heap.lookup id = some native ∧
        (memory appended).heap id = installed.heap id ∧ id ≠ lifetime) := by
  obtain ⟨lifetime, capacity, appended, finalOwner, run, plain, valid, keys, found, typed, writable, owned,
    enough, vector, finalHeader, itemRead, argumentRead, itemOwned, represented, payloadOwned, kept, rows, _, frame⟩ :=
    unrelocated_append_owned_at allocate safety allocator container oldCapacity object oldData ownerCell
      input stored key normalized operands cells value preparationOwnership middle (preparedFrame object stored operands installed)
      growth installedPost rfl rfl rfl ownerFound ownerTyped ownerWritable header bounded storage selected first room operandsBound
  exact ⟨lifetime, capacity, appended, finalOwner, run, plain, valid, keys, found, typed, writable, owned,
    enough, vector, finalHeader, itemRead, argumentRead, itemOwned, represented, payloadOwned, kept, rows, frame⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
