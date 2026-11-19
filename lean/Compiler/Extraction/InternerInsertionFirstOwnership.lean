/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionAppendOwnership

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- First native append derives its new backing and row/pointee owners from the
empty header, installed clone and actual allocation response. Neither a final
owner nor a successful native field read is an input. The sentinel is never
assumed distinct from the newly allocated backing or any empty argument. -/
theorem first_append_owned (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object base : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (sentinel : Compiler.ZigAir.Memory.Address)
    (input stored : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (value : Word) (ownership : Storage.State)
    (middle : Session (Publication.Effects σ)) (before : Frame σ) (reached : σ)
    (installed : AssemblyClone.NativeFields.Installed allocator object stored middle (memory before))
    (objectPresent : before.item.object = some object) (clonePresent : before.item.clone.value = some stored)
    (argumentsPresent : arguments normalized ownership before = some operands)
    (ownerFound : (memory before).memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (header : readItems (memory before).memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacityRead : readField (memory before).memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 0)))
    (operandsBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit)
    (response : allocate allocator 160 8 (memory before).effects.allocator = (some base, reached))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits (memory before).memory ⟨160, 8⟩ base)
    (unlocked : Owner.NativeLock.checkHeader (memory before).memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let row : Storage.Cell := ⟨stored.item, value, object, operands.items, key.sequence, operands.address⟩
    let lifetime := (memory before).memory.nextId
    ∃ after finalOwner,
      append runtimeSafety allocate allocator container [] input key normalized value ownership before = (.ok true, after) ∧
      Valid (memory after) ∧ (memory after).effects = { (memory before).effects with allocator := reached } ∧
      (memory after).memory.heap.lookup container = some finalOwner ∧ finalOwner.type = Owner.viewType runtimeSafety ∧
      finalOwner.writable = true ∧ Backing.Release.Owned allocator ⟨lifetime, 0⟩ 5 (memory after) ∧
      Memory.Vector allocator (memory after).heap lifetime [row] ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ 1, .scalar (.int false 64 5)) ∧
      ExpressionDeinit.Native.Fields.item (memory after).memory ⟨lifetime, 0⟩ = .ok ⟨object, 0⟩ ∧
      Expression.readField (memory after).memory false ⟨lifetime, 0⟩ Expression.argumentsOffset =
        .ok (.slice Expression.argumentsType ⟨operands.address, 0⟩ operands.items.length) ∧
      AssemblyItem.Owned allocator object (memory after) ∧
      AssemblyClone.NativeFields.Represents (memory after).memory ⟨object, 0⟩ stored ∧
      (∀ slice, AssemblyClone.Physical.payload stored = some slice → AssemblyItemDeinit.Owned allocator slice (memory after)) ∧
      (∀ argumentAllocator slice, Memory.SliceValid argumentAllocator (memory before).heap slice →
        Memory.SliceValid argumentAllocator (memory after).heap slice) ∧
      (memory after).memory.nextId = lifetime + 1 ∧
      (memory after).memory.nextAddress = max (memory before).memory.nextAddress (base + 160) ∧
      DescriptorRelation.Prefix (memory after).memory lifetime [row] ∧
      (∀ payload, stored.verbatim = some payload → AssemblyClone.Physical.Reads (memory after).memory payload.data) ∧
      (∀ id, id ≠ lifetime → (memory after).heap id = (memory before).heap id) ∧
      (∀ id, id ≠ container → id ≠ lifetime →
        (memory after).memory.heap.lookup id = (memory before).memory.heap.lookup id) := by
  dsimp only
  let row : Storage.Cell := ⟨stored.item, value, object, operands.items, key.sequence, operands.address⟩
  have allocated : allocation allocate allocator 160 8 (memory before).effects =
      (some base, { (memory before).effects with allocator := reached }) := by simp only [allocation, response]
  obtain ⟨appended, executed, heap, effects, valid, vector, backingOwned, finalHeader, rows, _, _, _, _⟩ :=
    DescriptorRelation.first_registered runtimeSafety (memory before) allocator container ownerCell sentinel row base
      (allocation allocate) _ installed.valid ownerFound ownerTyped ownerWritable header capacityRead operandsBound allocated fits unlocked
  obtain ⟨native, nativeRun, _, shape, _, fields, nextId, nextAddress, frame⟩ :=
    Append.Execution.first_verified runtimeSafety (memory before).memory container ownerCell sentinel
      ⟨object, 0⟩ ⟨operands.address, 0⟩ operands.items.length 0 key.sequence.toNat base
      ((allocation allocate) allocator) (memory before).effects _ installed.valid.memory ownerFound ownerTyped ownerWritable
      header capacityRead operandsBound (by decide) (number_valid key.sequence) allocated fits unlocked
  have same : native = appended.memory := congrArg (fun result => result.1.2) (nativeRun.symm.trans executed)
  subst native
  have registeredRun := Append.Registered.completed runtimeSafety (allocation allocate) allocator container (memory before).memory.nextId 5
    [] row (memory before) appended executed heap finalHeader (Append.Registered.admit_first allocator _ installed.valid)
  dsimp only [row] at registeredRun
  let after := withMemory before appended
  have appendRun : append runtimeSafety allocate allocator container [] input key normalized value ownership before = (.ok true, after) := by
    simp only [append, objectPresent, clonePresent, argumentsPresent, Option.isNone_some, Bool.or_self, Bool.false_eq_true,
      ↓reduceIte, cell, Option.getD_some, registeredRun, Except.mapError]
    rfl
  obtain ⟨finalOwner, finalOwnerFound, ownerShape⟩ := shape container ownerCell ownerFound
  obtain ⟨itemOwned, itemRepresented, payloadOwned, argumentFrame, contents⟩ :=
    append_pointees allocator container (memory before).memory.nextId object runtimeSafety ownerCell stored [row] middle
      (memory before) appended installed ownerFound ownerTyped
      (Or.inl (installed.valid.injected.fresh installed.valid.memory)) heap frame
  have reads := Expression.readFields_parts appended.memory false ⟨(memory before).memory.nextId, 0⟩ _ _ _ _ fields
  exact ⟨after, finalOwner, appendRun, valid, effects, finalOwnerFound, ownerShape.2.1.trans ownerTyped,
    ownerShape.2.2.1.trans ownerWritable, backingOwned, vector, finalHeader,
    ExpressionDeinit.Native.Fields.item_read _ _ _ reads.1, reads.2.1,
    itemOwned, itemRepresented, payloadOwned, argumentFrame, nextId, nextAddress, rows, contents,
    (by intro id apart; change appended.heap id = _; rw [heap, Memory.write_other _ _ _ _ apart]), frame⟩

/-- First allocation, failed publication and both cleanup stages are one reached
call chain. Cleanup retains the newly allocated empty backing and its advanced
history; no backing owner or post-append input contract is assumed. -/
theorem first_publication_oom_cleanup (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object base : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (sentinel : Compiler.ZigAir.Memory.Address)
    (input stored : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (value : Word) (ownership : Storage.State)
    (middle : Session (Publication.Effects σ)) (before : Frame σ)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (graph : Storage.State → Frame σ → Interner.Heap)
    (installed : AssemblyClone.NativeFields.Installed allocator object stored middle (memory before))
    (objectPresent : before.item.object = some object) (clonePresent : before.item.clone.value = some stored)
    (argumentsPresent : arguments normalized ownership before = some operands)
    (ownerFound : (memory before).memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (header : readItems (memory before).memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacityRead : readField (memory before).memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 0)))
    (operandsBound : operands.items.length < Compiler.ZigAir.Memory.addressLimit)
    (allocationEffects : σ)
    (allocated : allocate allocator 160 8 (memory before).effects.allocator = (some base, allocationEffects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits (memory before).memory ⟨160, 8⟩ base)
    (operandLive : Memory.SliceValid allocator (memory before).heap operands)
    (normalizedLive : Memory.SliceValid allocator (memory before).heap normalized)
    (separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address)
    (publication : Publication.Input allocator source key normalized ⟨graph ownership before, memory before⟩)
    (probeEffects : σ)
    (response : ops.probe key (Publication.forget (memory
      (append runtimeSafety allocate allocator container [] input key normalized value ownership before).2)) = (false, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader (memory before).memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let handed := (((Storage.Command.append.success ⟨true, true, fun _ => false⟩ ownership).setFlag .arguments false).setFlag .allocation false).setFlag .value false
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized [] value graph
    ∃ appended failed popped after,
      calls.attempt .append ownership before = (.ok true, appended) ∧
      calls.attempt .publish handed appended = (.ok false, failed) ∧
      memory failed = { memory appended with effects := { (memory appended).effects with allocator := probeEffects } } ∧
      (Storage.Cleanup.sequence [.lastValue, .pop]).execute calls handed failed =
        ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop]).run handed), popped) ∧
      (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).execute calls handed failed =
        ((.ok (), (Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run handed), after) ∧
      free (Publication.external ops.arguments) allocator normalized (memory popped) = (.ok (), memory after) ∧
      Valid (memory after) ∧ Memory.Vector allocator (memory after).heap (memory before).memory.nextId [] ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨(memory before).memory.nextId, 0⟩ 0, .scalar (.int false 64 5)) ∧
      Memory.Arguments.ReleasePost (memory popped).heap (memory popped).memory allocator normalized
        (memory after).heap (memory after).memory ∧
      (memory after).effects = (if normalized.items.isEmpty then (memory popped).effects
        else (Publication.external ops.arguments).free normalized (memory popped)) ∧
      (memory after).memory.nextId = (memory before).memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max (memory before).memory.nextAddress (base + 160) ∧
      after.item.object = none ∧ after.item.clone.value = none ∧ after.item.clone.execution.invalidated = true := by
  dsimp only
  let handed := (((Storage.Command.append.success ⟨true, true, fun _ => false⟩ ownership).setFlag .arguments false).setFlag .allocation false).setFlag .value false
  obtain ⟨appended, finalOwner, appendedRun, valid, effects, ownerFound, ownerTyped, ownerWritable,
      backingOwned, vector, finalHeader, itemRead, argumentRead, itemOwned, represented, payloadOwned,
      argumentsKept, nextId, nextAddress, _, _, _, _⟩ :=
    first_append_owned allocate runtimeSafety allocator container object base ownerCell sentinel input stored key
      normalized operands value ownership middle before allocationEffects installed objectPresent clonePresent argumentsPresent
      ownerFound ownerTyped ownerWritable header capacityRead operandsBound allocated fits unlocked
  have publicationInput := Publication.Input.frame allocator source key normalized
    ⟨graph ownership before, memory before⟩ ⟨graph handed appended, memory appended⟩ publication
    (by rw [effects]) (argumentsKept allocator)
  have probed : ops.probe key (Publication.forget (memory appended)) = (false, probeEffects) := by
    simpa only [appendedRun] using response
  obtain ⟨failed, popped, after, publicationRun, failedMemory, rolled, cleaned, freed, finalValid,
      finalVector, header, released, finalEffects, finalId, finalAddress, cleared, valueCleared, invalidated, _⟩ :=
    publication_oom_rollback ops allocate runtimeSafety allocator container (memory before).memory.nextId 5 object finalOwner source itemSource
      input stored key normalized operands [] _ value graph handed appended valid ownerFound ownerTyped ownerWritable
      backingOwned (by decide) finalHeader vector itemOwned itemRead argumentRead
      (argumentsKept allocator operands operandLive) represented payloadOwned
      (argumentsKept allocator normalized normalizedLive) separate publicationInput probeEffects probed
  exact ⟨appended, failed, popped, after, appendedRun, publicationRun, failedMemory, rolled, cleaned, freed,
    finalValid, finalVector, header, released, finalEffects, finalId.trans nextId, finalAddress.trans nextAddress,
    cleared, valueCleared, invalidated⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
