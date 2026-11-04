/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionRollbackProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Extend the deterministic insertion cleanup sequence with the outer argument
release. Its free precondition is derived through native destruction and pop
from the initial owners. Nonempty normalized and row arguments must be distinct;
empty sentinels need no allocation or separation. Caller insertion/publication
must still establish these initial owners and distinctness. -/
theorem rollback_normalized_verified (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container lifetime capacity object : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (input stored : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized arguments : Storage.ArgumentSlice) (cells : List Storage.Cell) (last : Storage.Cell)
    (value : Word) (graph : Storage.State → Frame σ → Interner.Heap) (ownership : Storage.State) (before : Frame σ)
    (initial : Valid (memory before))
    (ownerFound : (memory before).memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (rowOwned : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory before))
    (inside : cells.length < capacity)
    (header : readItems (memory before).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1)))
    (capacityRead : readField (memory before).memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 capacity)))
    (registered : Memory.Vector allocator (memory before).heap lifetime (cells ++ [last]))
    (itemOwned : AssemblyItem.Owned allocator object (memory before))
    (itemRead : ExpressionDeinit.Native.Fields.item (memory before).memory ⟨lifetime, cells.length * 32⟩ = .ok ⟨object, 0⟩)
    (argumentRead : Expression.readField (memory before).memory false ⟨lifetime, cells.length * 32⟩ Expression.argumentsOffset =
      .ok (.slice Expression.argumentsType ⟨arguments.address, 0⟩ arguments.items.length))
    (live : Memory.SliceValid allocator (memory before).heap arguments)
    (represented : AssemblyClone.NativeFields.Represents (memory before).memory ⟨object, 0⟩ stored)
    (payloadOwned : ∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice (memory before))
    (normalizedLive : Memory.SliceValid allocator (memory before).heap normalized)
    (separate : arguments.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ arguments.address) :
    ∃ popped after,
      (Storage.Cleanup.sequence [.lastValue, .pop]).execute
        (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph)
        ownership before = ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run ownership), popped) ∧
      (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute
        (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph)
        ownership before = ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run ownership), after) ∧
      free (Publication.external ops.arguments) allocator normalized (memory popped) = (.ok (), memory after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap lifetime cells ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      Memory.Arguments.ReleasePost (memory popped).heap (memory popped).memory allocator normalized
        (memory after).heap (memory after).memory ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory popped).effects
        else (Publication.external ops.arguments).free normalized (memory popped)) ∧
      (memory after).memory.nextId = (memory before).memory.nextId ∧
      (memory after).memory.nextAddress = (memory before).memory.nextAddress ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true ∧
      Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory after) ∧
      (DescriptorRelation.Prefix (memory before).memory lifetime cells →
        DescriptorRelation.Prefix (memory after).memory lifetime cells) ∧
      (∀ id, id ≠ container → id ≠ lifetime → id ≠ object →
        ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload stored) id →
        (arguments.items ≠ [] → id ≠ arguments.address) →
        (normalized.items ≠ [] → id ≠ normalized.address) →
        (memory after).heap id = (memory before).heap id ∧
        (memory after).memory.heap.lookup id = (memory before).memory.heap.lookup id) ∧
      (∀ id, (memory before).heap id = none ∧ (memory before).memory.heap.lookup id = none →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) ∧
      (∃ finalOwner, (memory after).memory.heap.lookup container = some finalOwner ∧ ownerCell.SameShape finalOwner) ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload stored) id ∨
        (arguments.items ≠ [] ∧ id = arguments.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  obtain ⟨_, popped, _, rolled, valid, vector, finalHeader, _, nextId, nextAddress,
      objectCleared, valueCleared, invalidated, survivors, poppedOwned, rowsKept, oldFrame, oldDead, poppedOwner, destroyed⟩ :=
    rollback_verified ops allocate runtimeSafety allocator container lifetime capacity object ownerCell source itemSource input stored
      key normalized arguments cells last value graph ownership before initial ownerFound ownerTyped ownerWritable rowOwned inside
      header capacityRead registered itemOwned itemRead argumentRead live represented payloadOwned
  have normalizedKept := survivors allocator normalized normalizedLive separate
  obtain ⟨released, freed, releasedValid, post, effects⟩ :=
    free_valid (Publication.external ops.arguments) allocator normalized (memory popped) valid normalizedKept
  let after := withMemory popped released
  have freeFrame (id : Nat) (apart : normalized.items ≠ [] → id ≠ normalized.address) :
      released.heap id = (memory popped).heap id ∧
      released.memory.heap.lookup id = (memory popped).memory.heap.lookup id := by
    by_cases empty : normalized.items = []
    · have same := (Prod.mk.inj ((free_empty (Publication.external ops.arguments) allocator normalized (memory popped) empty).symm.trans freed)).2
      rw [← same]; exact ⟨rfl, rfl⟩
    · exact post.frame id (apart empty)
  have apartRow (nonempty : normalized.items ≠ []) : lifetime ≠ normalized.address := by
    have storedNormalized := normalizedLive.resolve_left nonempty
    intro same; rw [← same, registered] at storedNormalized; cases storedNormalized
  have apartOwner (nonempty : normalized.items ≠ []) : container ≠ normalized.address := by
    obtain ⟨⟨argumentCell, argumentFound, argumentTyped, _, _⟩, _⟩ :=
      initial.related allocator normalized.address normalized.items nonempty (normalizedLive.resolve_left nonempty)
    exact (memory before).memory.heap.lookup_ne_of_type_ne container normalized.address ownerCell argumentCell
      ownerFound argumentFound (by simp [ownerTyped, argumentTyped, Owner.viewType])
  have backingFrame := freeFrame lifetime apartRow
  have ownerFrame := (freeFrame container apartOwner).2
  have releaseCall : (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph).release
      .normalized ((Storage.Cleanup.sequence [.lastValue, .pop]).run ownership) popped = (.ok (), after) := by
    simp only [callbacks, Insertion.callbacks, freed, Except.mapError]
    rfl
  refine ⟨popped, after, rolled, ?_, freed, releasedValid, backingFrame.1.trans vector,
    ?_, post, effects, post.nextId.trans nextId, post.nextAddress.trans nextAddress,
    objectCleared, valueCleared, invalidated, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have tail : Storage.releaseAll
        (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph)
        [.normalized] ((Storage.Cleanup.sequence [.lastValue, .pop]).run ownership) popped =
        ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run ownership), after) := by
      simp only [Storage.releaseAll, Storage.Release.execute, releaseCall]
      rfl
    have joined := Storage.releaseAll_append
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph)
      [.lastValue, .pop] [.normalized] ownership before
    simp only [Storage.Cleanup.execute] at rolled
    rw [rolled] at joined
    exact joined.trans tail
  · change readHeader released.memory (Owner.headerAddress ⟨container, 0⟩) = _
    unfold readHeader readItems
    rw [readField_eq_of_lookup (memory popped).memory released.memory (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame,
      readField_eq_of_lookup (memory popped).memory released.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame]
    exact finalHeader
  · obtain ⟨root, _, backing, found, typed, writable, persistent⟩ := poppedOwned
    exact ⟨root, ⟨cells, backingFrame.1.trans vector⟩, backing, backingFrame.2.trans found, typed, writable, persistent⟩
  · intro rows
    exact DescriptorRelation.frame (memory popped).memory released.memory lifetime cells (rowsKept rows) backingFrame.2
  · intro id ownerApart backingApart objectApart untouched argumentsApart normalizedApart
    have kept := oldFrame id ownerApart backingApart objectApart untouched argumentsApart
    exact ⟨(freeFrame id normalizedApart).1.trans kept.1, (freeFrame id normalizedApart).2.trans kept.2⟩
  · intro id dead
    exact ExpressionDeinit.Payload.free_keeps_dead (Publication.external ops.arguments) allocator normalized
      (memory popped) released id freed post (oldDead id dead)
  · obtain ⟨finalOwner, found, shape⟩ := poppedOwner
    exact ⟨finalOwner, ownerFrame.trans found, shape⟩
  · intro id selected
    rcases selected with item | payload | arguments | ⟨nonempty, rfl⟩
    · exact ExpressionDeinit.Payload.free_keeps_dead (Publication.external ops.arguments) allocator normalized
        (memory popped) released id freed post (destroyed id (Or.inl item))
    · exact ExpressionDeinit.Payload.free_keeps_dead (Publication.external ops.arguments) allocator normalized
        (memory popped) released id freed post (destroyed id (Or.inr (Or.inl payload)))
    · exact ExpressionDeinit.Payload.free_keeps_dead (Publication.external ops.arguments) allocator normalized
        (memory popped) released id freed post (destroyed id (Or.inr (Or.inr arguments)))
    · exact post.dead nonempty

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
