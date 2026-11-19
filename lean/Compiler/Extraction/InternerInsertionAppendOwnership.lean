/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendPointees
import Compiler.Extraction.InternerInsertionPublicationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Derive the cleanup's native row and pointee premises from the actual spare
append. The clone's installed fields/owners and the old graph geometry are
initial facts; no post-append field read, owner or valid session is assumed.
The registry is refined by the existing registered executor. -/
theorem spare_append_owned (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container lifetime capacity object : Nat) (ownerCell backing : Compiler.ZigAir.Memory.Allocation)
    (input stored : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (ownership : Storage.State)
    (middle : Session (Publication.Effects σ)) (before : Frame σ)
    (installed : AssemblyClone.NativeFields.Installed allocator object stored middle (memory before))
    (objectPresent : before.item.object = some object) (clonePresent : before.item.clone.value = some stored)
    (argumentsPresent : arguments normalized ownership before = some operands)
    (ownerFound : (memory before).memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (backingFound : (memory before).memory.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (header : readItems (memory before).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (capacityRead : readField (memory before).memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 capacity)))
    (registered : Memory.Vector allocator (memory before).heap lifetime cells)
    (rows : DescriptorRelation.Prefix (memory before).memory lifetime cells)
    (spare : cells.length < capacity) (room : cells.length < 2 ^ 32 - 1)
    (operandsBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit) :
    let row : Storage.Cell := ⟨stored.item, value, object, operands.items, key.sequence, operands.address⟩
    ∃ after finalOwner,
      append runtimeSafety allocate allocator container cells input key normalized value ownership before = (.ok true, after) ∧
      Valid (memory after) ∧ (memory after).effects = (memory before).effects ∧
      (memory after).memory.heap.lookup container = some finalOwner ∧ finalOwner.type = Owner.viewType runtimeSafety ∧
      finalOwner.writable = true ∧ Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory after) ∧
      Memory.Vector allocator (memory after).heap lifetime (cells ++ [row]) ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)) ∧
      ExpressionDeinit.Native.Fields.item (memory after).memory ⟨lifetime, cells.length * 32⟩ = .ok ⟨object, 0⟩ ∧
      Expression.readField (memory after).memory false ⟨lifetime, cells.length * 32⟩ Expression.argumentsOffset =
        .ok (.slice Expression.argumentsType ⟨operands.address, 0⟩ operands.items.length) ∧
      AssemblyItem.Owned allocator object (memory after) ∧
      AssemblyClone.NativeFields.Represents (memory after).memory ⟨object, 0⟩ stored ∧
      (∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice (memory after)) ∧
      (∀ argumentAllocator slice, Memory.SliceValid argumentAllocator (memory before).heap slice →
        Memory.SliceValid argumentAllocator (memory after).heap slice) ∧
      (memory after).memory.nextId = (memory before).memory.nextId ∧
      (memory after).memory.nextAddress = (memory before).memory.nextAddress ∧
      DescriptorRelation.Prefix (memory after).memory lifetime (cells ++ [row]) ∧
      (∀ payload, stored.verbatim = some payload → AssemblyClone.Physical.Reads (memory after).memory payload.data) ∧
      (∀ id, id ≠ lifetime → (memory after).heap id = (memory before).heap id) ∧
      (∀ id, id ≠ container → id ≠ lifetime →
        (memory after).memory.heap.lookup id = (memory before).memory.heap.lookup id) ∧
      Owner.NativeLock.checkHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        Owner.NativeLock.checkHeader (memory before).memory (Owner.headerAddress ⟨container, 0⟩) := by
  dsimp only
  let row : Storage.Cell := ⟨stored.item, value, object, operands.items, key.sequence, operands.address⟩
  obtain ⟨appended, executed, heap, effects, valid, vector, finalHeader, extended, _, _⟩ :=
    DescriptorRelation.spare_registered runtimeSafety (memory before) allocator container lifetime capacity ownerCell backing cells row
      ((allocation allocate) allocator) installed.valid ownerFound ownerTyped ownerWritable backingFound backingTyped backingWritable
      header capacityRead registered rows spare room operandsBound
  obtain ⟨native, nativeRun, _, shape, _, fields, nextId, nextAddress, frame, lock⟩ :=
    Append.Execution.spare_verified runtimeSafety (memory before).memory container lifetime capacity cells.length ownerCell backing
      ⟨object, 0⟩ ⟨operands.address, 0⟩ operands.items.length (Storage.idFor cells).toNat key.sequence.toNat
      ((allocation allocate) allocator) (memory before).effects installed.valid.memory ownerFound ownerTyped ownerWritable
      backingFound backingTyped backingWritable header capacityRead spare operandsBound
      (number_valid (Storage.idFor cells)) (number_valid key.sequence)
  have same : native = appended.memory := congrArg (fun result => result.1.2) (nativeRun.symm.trans executed)
  subst native
  have finalHeader : readHeader appended.memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)) := by
    simpa only [List.length_append, List.length_singleton] using finalHeader
  have registeredRun := Append.Registered.completed runtimeSafety (allocation allocate) allocator container lifetime capacity
    cells row (memory before) appended executed heap finalHeader (Append.Registered.admit_vector allocator lifetime cells _ registered)
  dsimp only [row] at registeredRun
  let after := withMemory before appended
  have appendRun : append runtimeSafety allocate allocator container cells input key normalized value ownership before = (.ok true, after) := by
    simp only [append, objectPresent, clonePresent, argumentsPresent, Option.isNone_some, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, cell, Option.getD_some, registeredRun, Except.mapError]
    rfl
  obtain ⟨finalOwner, finalOwnerFound, ownerShape⟩ := shape container ownerCell ownerFound
  obtain ⟨finalBacking, finalBackingFound, backingShape⟩ := shape lifetime backing backingFound
  obtain ⟨initialBacking, initialBackingFound, persistent⟩ := installed.valid.injected lifetime _ registered
  have sameBacking : initialBacking = backing := Option.some.inj (initialBackingFound.symm.trans backingFound)
  subst initialBacking
  obtain ⟨itemOwned, itemRepresented, payloadOwned, argumentFrame, contents⟩ :=
    append_pointees allocator container lifetime object runtimeSafety ownerCell stored (cells ++ [row]) middle
      (memory before) appended installed ownerFound ownerTyped (Or.inr ⟨cells, registered⟩) heap frame
  have reads := Expression.readFields_parts appended.memory false ⟨lifetime, cells.length * 32⟩ _ _ _ _ fields
  refine ⟨after, finalOwner, appendRun, valid, effects, finalOwnerFound, ownerShape.2.1.trans ownerTyped,
    ownerShape.2.2.1.trans ownerWritable,
    ⟨rfl, ⟨cells ++ [row], vector⟩, finalBacking, finalBackingFound, backingShape.2.1.trans backingTyped,
      backingShape.2.2.1.trans backingWritable, backingShape.2.2.2.trans persistent⟩,
    vector, finalHeader, ExpressionDeinit.Native.Fields.item_read _ _ _ reads.1, reads.2.1,
    itemOwned, itemRepresented, payloadOwned, argumentFrame, nextId, nextAddress, extended, contents, ?_, frame, lock⟩
  intro id apart
  change appended.heap id = (memory before).heap id
  rw [heap, Memory.write_other _ _ _ _ apart]

/-- Connect actual spare append, admitted publication OOM and both deferred
cleanup stages. Every rollback premise comes from the pre-append installed
clone and graph; probing sees the appended session. This is a scoped call-chain
connection, not initialization or the complete insertion/recursive theorem. -/
theorem spare_publication_oom_cleanup (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container lifetime capacity object : Nat) (ownerCell backing : Compiler.ZigAir.Memory.Allocation)
    (input stored : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (ownership : Storage.State)
    (middle : Session (Publication.Effects σ)) (before : Frame σ)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (graph : Storage.State → Frame σ → Interner.Heap)
    (installed : AssemblyClone.NativeFields.Installed allocator object stored middle (memory before))
    (objectPresent : before.item.object = some object) (clonePresent : before.item.clone.value = some stored)
    (argumentsPresent : arguments normalized ownership before = some operands)
    (ownerFound : (memory before).memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (backingFound : (memory before).memory.heap.lookup lifetime = some backing)
    (backingTyped : backing.type = .array capacity Expression.allocationType) (backingWritable : backing.writable = true)
    (header : readItems (memory before).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (capacityRead : readField (memory before).memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 capacity)))
    (registered : Memory.Vector allocator (memory before).heap lifetime cells)
    (rows : DescriptorRelation.Prefix (memory before).memory lifetime cells)
    (spare : cells.length < capacity) (room : cells.length < 2 ^ 32 - 1)
    (operandsBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit)
    (operandLive : Memory.SliceValid allocator (memory before).heap operands)
    (normalizedLive : Memory.SliceValid allocator (memory before).heap normalized)
    (separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address)
    (publication : Publication.Input allocator source key normalized ⟨graph ownership before, memory before⟩)
    (probeEffects : σ)
    (response : ops.probe key (Publication.forget (memory
      (append runtimeSafety allocate allocator container cells input key normalized value ownership before).2)) = (false, probeEffects)) :
    let handed := (((Storage.Command.append.success ⟨true, true, fun _ => false⟩ ownership).setFlag .arguments false).setFlag .allocation false).setFlag .value false
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
    ∃ appended failed popped after,
      calls.attempt .append ownership before = (.ok true, appended) ∧
      calls.attempt .publish handed appended = (.ok false, failed) ∧
      memory failed = { memory appended with effects := { (memory appended).effects with allocator := probeEffects } } ∧
      (Storage.Cleanup.sequence [.lastValue, .pop]).execute calls handed failed =
        ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run handed), popped) ∧
      (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute calls handed failed =
        ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after) ∧
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
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true := by
  dsimp only
  let handed := (((Storage.Command.append.success ⟨true, true, fun _ => false⟩ ownership).setFlag .arguments false).setFlag .allocation false).setFlag .value false
  obtain ⟨appended, finalOwner, appendedRun, valid, effects, ownerFound, ownerTyped, ownerWritable,
      backingOwned, vector, finalHeader, itemRead, argumentRead, itemOwned, represented, payloadOwned,
      argumentsKept, nextId, nextAddress, _, _, _, _⟩ :=
    spare_append_owned allocate runtimeSafety allocator container lifetime capacity object ownerCell backing input stored key
      normalized operands cells value ownership middle before installed objectPresent clonePresent argumentsPresent ownerFound ownerTyped
      ownerWritable backingFound backingTyped backingWritable header capacityRead registered rows spare room operandsBound
  have publicationInput := Publication.Input.frame allocator source key normalized
    ⟨graph ownership before, memory before⟩ ⟨graph handed appended, memory appended⟩ publication
    (congrArg (·.keys) effects) (argumentsKept allocator)
  have probed : ops.probe key (Publication.forget (memory appended)) = (false, probeEffects) := by
    simpa only [appendedRun] using response
  obtain ⟨failed, popped, after, publicationRun, failedMemory, rolled, cleaned, freed, finalValid,
      finalVector, header, released, finalEffects, finalId, finalAddress, cleared, valueCleared, invalidated, _⟩ :=
    publication_oom_rollback ops allocate runtimeSafety allocator container lifetime capacity object finalOwner source itemSource
      input stored key normalized operands cells _ value graph handed appended valid ownerFound ownerTyped ownerWritable
      backingOwned spare finalHeader vector itemOwned itemRead argumentRead
      (argumentsKept allocator operands operandLive) represented payloadOwned
      (argumentsKept allocator normalized normalizedLive) separate publicationInput probeEffects probed
  exact ⟨appended, failed, popped, after, appendedRun, publicationRun, failedMemory, rolled, cleaned, freed,
    finalValid, finalVector, header, released, finalEffects, finalId.trans nextId, finalAddress.trans nextAddress,
    cleared, valueCleared, invalidated⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
