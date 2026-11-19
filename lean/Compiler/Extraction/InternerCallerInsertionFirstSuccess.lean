/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReachedFirstSuccess

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- The first successful deterministic insertion starts with the actual caller
origin and empty native-container facts. It establishes the nonempty graph's
rows, pointees, payload contents and global key ownership for subsequent calls.
Native map probing, allocator binding and word semantics remain separate. -/
theorem CallerInput.first_success (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object base : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (sentinel : Compiler.ZigAir.Memory.Address) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (meaning : Meaning) (request : Interner.Request) (values : List NodeId)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (lookup remaining : Handle) (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
    (duplicated allocated middle : Session (Publication.Effects σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (admitted : Admitted ops.arguments) (emptyKeys : before.memory.effects.keys = fun _ => none)
    (ownerFound : before.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType sentinel 0))
    (capacityRead : readField before.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 0)))
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ taken.world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (allocationEffects : σ)
    (backing : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator 160 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base)
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append runtimeSafety allocate allocator container [] input key normalized
        ((key.eval meaning taken.world.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)).2)) =
        (true, probeEffects))
    (unlocked : Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok ()) :
    let value := (key.eval meaning taken.world.graph.read).getD 0
    let row : Storage.Cell := ⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩
    ∃ after finalOwner,
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true [] taken.world =
        ((.ok (some .success), Storage.publishedOwnership), after) ∧
      Valid (memory after) ∧
      (memory after).memory.heap.lookup container = some finalOwner ∧ finalOwner.type = Owner.viewType runtimeSafety ∧
      finalOwner.writable = true ∧
      Memory.Vector allocator (memory after).heap middle.memory.nextId [row] ∧
      Backing.Release.Owned allocator ⟨middle.memory.nextId, 0⟩ 5 (memory after) ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨middle.memory.nextId, 0⟩ 1, .scalar (.int false 64 5)) ∧
      DescriptorRelation.Prefix (memory after).memory middle.memory.nextId [row] ∧
      (∀ id, representativeFields (memory after).memory (Owner.headerAddress ⟨container, 0⟩) id =
        .ok ((Storage.representativeProgram.run [row] id).map (DescriptorRelation.values id.toNat))) ∧
      Memory.GraphResident allocator (memory after).heap [row] ∧
      AssemblyItem.Owned allocator object (memory after) ∧
      AssemblyClone.NativeFields.Represents (memory after).memory ⟨object, 0⟩ copied ∧
      (∀ slice, AssemblyClone.Physical.payload copied = some slice → AssemblyItemDeinit.Owned allocator slice (memory after)) ∧
      (∀ payload, copied.verbatim = some payload → AssemblyClone.Physical.Reads (memory after).memory payload.data) ∧
      Memory.SliceValid allocator (memory after).heap normalized ∧
      OwnedKeys.Live allocator ⟨(memory after).effects.keys, (memory after).heap⟩ ∧
      OwnedKeys.Unique (memory after).effects.keys ∧
      (memory after).effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨normalized.address, 0⟩ ∧
      (memory after).effects.allocator = probeEffects ∧
      (memory after).memory.nextId = middle.memory.nextId + 1 ∧
      (memory after).memory.nextAddress = max middle.memory.nextAddress (base + 160) ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → id ≠ container →
        (memory after).memory.heap.lookup id = some cell) ∧
      ((input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues →
        BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨container, 0⟩) [row] (memory after)) ∧
      OwnedKeys.Apart (memory after).effects.keys (fun id => operands.items ≠ [] ∧ id = operands.address) ∧
      cell input key normalized value Storage.publishedOwnership after = row := by
  have ownerFrame := entry.native_frame container ownerCell ownerFound
  obtain ⟨installed, appended, after, finalOwner, _, _, executed, valid, finalOwnerFound,
      finalOwnerTyped, finalOwnerWritable, vector, owned, finalHeader, finalRows, queries,
      resident, ownedItem, itemReads, ownedPayload, contents, normalizedKept, live, unique,
      keys, effects, nextId, nextAddress, native, accepted, apart, candidate, _, _⟩ :=
    first_success_reached ops allocate runtimeSafety allocator container object base ownerCell sentinel source itemSource
      meaning input copied key normalized operands remaining taken.world duplicated allocated middle
      entry.origin.held.1.1 entry.item (entry.graph_custody [] (by intro cell member; cases member))
      entry.publication entry.live entry.unique admitted (entry.origin.memory _ _ ownerFound) ownerTyped ownerWritable
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      duplicateCall createCall cloneCall allocationEffects backing probeEffects response
      ((Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety before.memory.memory taken.world.memory.memory
        container ownerCell entry.origin.held.1.1.memory ownerFound ownerTyped ownerFrame).trans unlocked)
  dsimp only at *
  refine ⟨after, finalOwner, executed, valid, finalOwnerFound, finalOwnerTyped, finalOwnerWritable,
    vector, owned, finalHeader, finalRows, queries, resident, ownedItem, itemReads, ownedPayload,
    contents, normalizedKept, live, unique, ?_, ?_, nextId, nextAddress, ?_, accepted, apart, candidate⟩
  · simpa only [entry.keys] using keys
  · simpa only [entry.keys, emptyKeys] using effects
  · intro id cell found apart
    exact native id cell (entry.origin.memory _ _ found) apart (by
      intro old impossible _
      rw [entry.keys, emptyKeys] at impossible
      cases impossible)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
