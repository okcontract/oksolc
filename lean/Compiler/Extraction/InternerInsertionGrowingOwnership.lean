/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionPointeeFrame
import Compiler.Extraction.RepresentativeRegisteredGrowthAppendProofs
import Compiler.Extraction.InternerInsertionPublicationFailure

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Growing append establishes every subsequent destructor premise from the
installed clone, old graph and actual allocation response. Source-selected
relocation supplies the native/registry frames; old backing death and allocation
history are retained. The captured remap identity remains a caller obligation. -/
theorem growing_append_owned (allocate : Backing.Registry.Allocate σ) (freeBacking : Backing.Release.External σ)
    (runtimeSafety : Bool) (allocator container oldLifetime oldCapacity capacity object base context returnAddress : Nat)
    (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (input stored : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (ownership : Storage.State)
    (middle : Session (Publication.Effects σ)) (before : Frame σ) (allocationEffects : σ)
    (installed : AssemblyClone.NativeFields.Installed allocator object stored middle (memory before))
    (objectPresent : before.item.object = some object) (clonePresent : before.item.clone.value = some stored)
    (argumentsPresent : arguments normalized ownership before = some operands)
    (ownerFound : (memory before).memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (oldOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity (memory before))
    (header : readItems (memory before).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨oldLifetime, 0⟩ cells.length))
    (capacityRead : readField (memory before).memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 oldCapacity)))
    (registered : Memory.Vector allocator (memory before).heap oldLifetime cells)
    (rows : DescriptorRelation.Prefix (memory before).memory oldLifetime cells)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selected : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (operandsBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit)
    (response : allocate allocator (capacity * 32) 8 (memory before).effects.allocator = (some base, allocationEffects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits (memory before).memory ⟨capacity * 32, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader (memory before).memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    let row : Storage.Cell := ⟨stored.item, value, object, operands.items, key.sequence, operands.address⟩
    let lifetime := (memory before).memory.nextId
    ∃ oldCell after finalOwner,
      (memory before).memory.heap.lookup oldLifetime = some oldCell ∧
      append runtimeSafety allocate allocator container cells input key normalized value ownership before (some growth) = (.ok true, after) ∧
      Valid (memory after) ∧ (memory after).effects = { (memory before).effects with
        allocator := freeBacking allocator oldCell.base (oldCapacity * 32) 8 allocationEffects } ∧
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
      (∀ payload, stored.verbatim = some payload → AssemblyClone.Physical.Reads (memory after).memory payload.data) ∧
      (memory after).memory.nextId = lifetime + 1 ∧
      (memory after).memory.nextAddress = max (memory before).memory.nextAddress (base + capacity * 32) ∧
      (memory after).heap oldLifetime = none ∧ (memory after).memory.heap.lookup oldLifetime = none ∧
      DescriptorRelation.Prefix (memory after).memory lifetime (cells ++ [row]) ∧
      (∀ id, id ≠ oldLifetime → id ≠ lifetime → (memory after).heap id = (memory before).heap id) ∧
      (∀ id, id ≠ oldLifetime → id ≠ lifetime → id ≠ container →
        (memory after).memory.heap.lookup id = (memory before).memory.heap.lookup id) ∧
      ownerCell.SameShape finalOwner := by
  dsimp only
  let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
  let row : Storage.Cell := ⟨stored.item, value, object, operands.items, key.sequence, operands.address⟩
  have allocated : allocation allocate allocator (capacity * 32) 8 (memory before).effects =
      (some base, { (memory before).effects with allocator := allocationEffects }) := by simp only [allocation, response]
  obtain ⟨oldCell, appended, oldFound, executed, valid, vector, backingOwned, oldDead, nativeDead, effects,
      nextId, nextAddress, registryFrame, finalHeader, finalRows, _, _, ⟨finalOwner, finalOwnerFound, ownerShape⟩, nativeFrame⟩ :=
    Append.Registered.growing_verified runtimeSafety (allocation allocate) (growthCallbacks growth).release allocator container oldLifetime
      oldCapacity capacity base context returnAddress (memory before) _ ownerCell cells row installed.valid ownerFound ownerTyped ownerWritable
      oldOwned registered oldNonempty full selected size room operandsBound allocated fits header capacityRead rows unlocked
  change Append.Registered.runWithGrowth (growthCallbacks growth) runtimeSafety (allocation allocate) allocator container cells row
    (memory before) = (.ok true, appended) at executed
  dsimp only [row] at executed
  let after := withMemory before appended
  have appendRun : append runtimeSafety allocate allocator container cells input key normalized value ownership before (some growth) = (.ok true, after) := by
    simp only [append, objectPresent, clonePresent, argumentsPresent, Option.isNone_some, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, cell, Option.getD_some, executed, Except.mapError]
    rfl
  have targets : ∀ id ∈ [oldLifetime, (memory before).memory.nextId],
      (memory before).heap id = none ∨ ∃ old, Memory.Vector allocator (memory before).heap id old := by
    intro id member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inr ⟨cells, registered⟩
    · exact Or.inl (installed.valid.injected.fresh installed.valid.memory)
  obtain ⟨itemOwned, itemRepresented, payloadOwned, argumentsKept, contentsKept⟩ :=
    representative_pointees allocator container object [oldLifetime, (memory before).memory.nextId] runtimeSafety ownerCell stored middle
      (memory before) appended installed ownerFound ownerTyped targets
      (fun id outside => by
        have apart : id ≠ oldLifetime ∧ id ≠ (memory before).memory.nextId := by simpa using outside
        exact registryFrame id apart.1 apart.2)
      (fun id ownerApart outside => by
        have apart : id ≠ oldLifetime ∧ id ≠ (memory before).memory.nextId := by simpa using outside
        exact nativeFrame id apart.1 apart.2 ownerApart)
  have fields := finalRows cells.length row (by simp)
  have reads := Expression.readFields_parts appended.memory false ⟨(memory before).memory.nextId, cells.length * 32⟩ _ _ _ _ fields
  refine ⟨oldCell, after, finalOwner, oldFound, appendRun, valid, ?_, finalOwnerFound, ownerShape.2.1.trans ownerTyped,
    ownerShape.2.2.1.trans ownerWritable, backingOwned, vector, ?_, ExpressionDeinit.Native.Fields.item_read _ _ _ reads.1,
    reads.2.1, itemOwned, itemRepresented, payloadOwned, argumentsKept, contentsKept, nextId, nextAddress, oldDead, nativeDead,
    finalRows, registryFrame, nativeFrame, ownerShape⟩
  · exact effects
  · simpa only [List.length_append, List.length_singleton] using finalHeader

/-- Actual nonempty growth, publication OOM and both cleanup stages form one
reached call chain. Cleanup retains the relocated backing, original logical
prefix and advanced history. No post-append cleanup owner is assumed. -/
theorem growing_publication_oom_cleanup (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (freeBacking : Backing.Release.External σ) (runtimeSafety : Bool)
    (allocator container oldLifetime oldCapacity capacity object base context returnAddress : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
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
    (oldOwned : Backing.Release.Owned allocator ⟨oldLifetime, 0⟩ oldCapacity (memory before))
    (header : readItems (memory before).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨oldLifetime, 0⟩ cells.length))
    (capacityRead : readField (memory before).memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 oldCapacity)))
    (registered : Memory.Vector allocator (memory before).heap oldLifetime cells)
    (rows : DescriptorRelation.Prefix (memory before).memory oldLifetime cells)
    (oldNonempty : oldCapacity ≠ 0) (full : oldCapacity < Append.nextLength cells.length)
    (selected : capacity = Capacity.grow (Append.nextLength cells.length))
    (size : capacity * 32 < Compiler.ZigAir.Memory.addressLimit) (room : cells.length < 2 ^ 32 - 1)
    (operandsBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit)
    (allocationEffects : σ)
    (allocated : allocate allocator (capacity * 32) 8 (memory before).effects.allocator = (some base, allocationEffects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits (memory before).memory ⟨capacity * 32, 8⟩ base)
    (operandLive : Memory.SliceValid allocator (memory before).heap operands)
    (normalizedLive : Memory.SliceValid allocator (memory before).heap normalized)
    (separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address)
    (publication : Publication.Input allocator source key normalized ⟨graph ownership before, memory before⟩)
    (probeEffects : σ)
    (response : ops.probe key (Publication.forget (memory
      (append runtimeSafety allocate allocator container cells input key normalized value ownership before
        (some ⟨.noRemap context returnAddress, freeBacking⟩)).2)) = (false, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader (memory before).memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
    let handed := (((Storage.Command.append.success ⟨true, true, fun _ => false⟩ ownership).setFlag .arguments false).setFlag .allocation false).setFlag .value false
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph (some growth)
    ∃ appended failed popped after,
      calls.attempt .append ownership before = (.ok true, appended) ∧
      calls.attempt .publish handed appended = (.ok false, failed) ∧
      memory failed = { memory appended with effects := { (memory appended).effects with allocator := probeEffects } } ∧
      (Storage.Cleanup.sequence [.lastValue, .pop]).execute calls handed failed =
        ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run handed), popped) ∧
      (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute calls handed failed =
        ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after) ∧
      free (Publication.external ops.arguments) allocator normalized (memory popped) = (.ok (), memory after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap (memory before).memory.nextId cells ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨(memory before).memory.nextId, 0⟩ cells.length, .scalar (.int false 64 capacity)) ∧
      Memory.Arguments.ReleasePost (memory popped).heap (memory popped).memory allocator normalized
        (memory after).heap (memory after).memory ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory popped).effects
        else (Publication.external ops.arguments).free normalized (memory popped)) ∧
      (memory after).memory.nextId = (memory before).memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max (memory before).memory.nextAddress (base + capacity * 32) ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true ∧
      Backing.Release.Owned allocator ⟨(memory before).memory.nextId, 0⟩ capacity (memory after) ∧
      DescriptorRelation.Prefix (memory after).memory (memory before).memory.nextId cells ∧
      (memory after).heap oldLifetime = none ∧ (memory after).memory.heap.lookup oldLifetime = none ∧
      (memory after).effects.keys = (memory before).effects.keys ∧
      (∀ id, id ≠ container → id ≠ oldLifetime → id ≠ (memory before).memory.nextId → id ≠ object →
        ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload stored) id →
        (operands.items ≠ [] → id ≠ operands.address) → (normalized.items ≠ [] → id ≠ normalized.address) →
        (memory after).heap id = (memory before).heap id ∧
        (memory after).memory.heap.lookup id = (memory before).memory.heap.lookup id) ∧
      (∃ finalOwner, (memory after).memory.heap.lookup container = some finalOwner ∧ ownerCell.SameShape finalOwner) ∧
      (∀ id, id = object ∨ AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload stored) id ∨
        (operands.items ≠ [] ∧ id = operands.address) ∨ (normalized.items ≠ [] ∧ id = normalized.address) →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) := by
  dsimp only
  let growth : Growth.Registered.Callbacks σ := ⟨.noRemap context returnAddress, freeBacking⟩
  let handed := (((Storage.Command.append.success ⟨true, true, fun _ => false⟩ ownership).setFlag .arguments false).setFlag .allocation false).setFlag .value false
  obtain ⟨oldCell, appended, finalOwner, _, appendedRun, valid, effects, ownerFound, ownerTyped, ownerWritable,
      backingOwned, vector, finalHeader, itemRead, argumentRead, itemOwned, represented, payloadOwned,
      argumentsKept, _, nextId, nextAddress, oldDead, nativeDead, appendedRows, registryFrame, nativeFrame, ownerShape⟩ :=
    growing_append_owned allocate freeBacking runtimeSafety allocator container oldLifetime oldCapacity capacity object base context returnAddress
      ownerCell input stored key normalized operands cells value ownership middle before allocationEffects installed objectPresent clonePresent argumentsPresent
      ownerFound ownerTyped ownerWritable oldOwned header capacityRead registered rows oldNonempty full selected size room operandsBound allocated fits unlocked
  have publicationInput := Publication.Input.frame allocator source key normalized
    ⟨graph ownership before, memory before⟩ ⟨graph handed appended, memory appended⟩ publication
    (by rw [effects]) (argumentsKept allocator)
  have probed : ops.probe key (Publication.forget (memory appended)) = (false, probeEffects) := by
    simpa only [appendedRun] using response
  have width : Append.nextLength cells.length < Compiler.ZigAir.Memory.addressLimit := by
    simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega
  have enough : Append.nextLength cells.length ≤ capacity := selected ▸ Capacity.grow_sufficient _ width
  have inside : cells.length < capacity := by simp only [Append.nextLength] at enough; omega
  obtain ⟨failed, popped, after, publicationRun, failedMemory, rolled, cleaned, freed, finalValid,
      finalVector, header, released, finalEffects, finalId, finalAddress, cleared, valueCleared, invalidated,
      owned, rowsKept, cleanupFrame, deadKept, finalOwnerShape, destroyed, keys⟩ :=
    publication_oom_rollback ops allocate runtimeSafety allocator container (memory before).memory.nextId capacity object finalOwner source itemSource
      input stored key normalized operands cells _ value graph handed appended valid ownerFound ownerTyped ownerWritable
      backingOwned inside finalHeader vector itemOwned itemRead argumentRead
      (argumentsKept allocator operands operandLive) represented payloadOwned
      (argumentsKept allocator normalized normalizedLive) separate publicationInput probeEffects probed (some growth)
  have retainedRows : DescriptorRelation.Prefix (memory appended).memory (memory before).memory.nextId cells := by
    intro index cell found
    have inside : index < cells.length := by
      by_cases inside : index < cells.length
      · exact inside
      · rw [List.getElem?_eq_none (by omega)] at found; contradiction
    exact appendedRows index cell (by simpa only [List.getElem?_append_left inside] using found)
  have retired := deadKept oldLifetime ⟨oldDead, nativeDead⟩
  refine ⟨appended, failed, popped, after, appendedRun, publicationRun, failedMemory, rolled, cleaned, freed,
    finalValid, finalVector, header, released, finalEffects, finalId.trans nextId, finalAddress.trans nextAddress,
    cleared, valueCleared, invalidated, owned, rowsKept retainedRows, retired.1, retired.2, ?_, ?_, ?_, destroyed⟩
  · exact keys.trans (show (memory appended).effects.keys = (memory before).effects.keys by rw [effects])
  · intro id ownerApart oldApart newApart objectApart payloadApart argumentsApart normalizedApart
    have kept := cleanupFrame id ownerApart newApart objectApart payloadApart argumentsApart normalizedApart
    exact ⟨kept.1.trans (registryFrame id oldApart newApart), kept.2.trans (nativeFrame id oldApart newApart ownerApart)⟩
  · obtain ⟨lastOwner, found, shape⟩ := finalOwnerShape
    exact ⟨lastOwner, found, ownerShape.trans shape⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
