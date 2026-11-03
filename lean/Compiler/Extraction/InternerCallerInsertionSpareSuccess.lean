/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionSpareSuccess

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Successful deterministic insertion into existing spare capacity, starting
at the actual caller's take boundary. Preparation, append and publication derive
the extended resident/native graph, new pointees and global key ownership.
Initial graph correspondence and key/argument separation are explicit; no
reached owner, resident graph, query or preservation conclusion is a premise. -/
theorem CallerInput.spare_success (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container lifetime capacity object : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (meaning : Meaning)
    (request : Interner.Request) (values : List NodeId) (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized operands : ArgumentSlice) (lookup remaining : Handle)
    (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ)) (cells : List Storage.Cell)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (admitted : Admitted ops.arguments)
    (ownerFound : before.memory.memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety) (ownerWritable : ownerCell.writable = true)
    (backingOwned : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity before.memory)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) = .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (capacityRead : readField before.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset = .ok (.scalar (.int false 64 capacity)))
    (registered : Memory.Vector allocator before.memory.heap lifetime cells)
    (rows : DescriptorRelation.Prefix before.memory.memory lifetime cells)
    (resident : Memory.GraphResident allocator before.memory.heap cells)
    (keyApart : OwnedKeys.Apart before.memory.effects.keys
      (fun address => ∃ cell ∈ cells, cell.arguments ≠ [] ∧ address = cell.argumentsAddress))
    (oldItems : ∀ cell ∈ cells, ∃ native, before.memory.memory.heap.lookup cell.itemAddress = some native ∧
      native.type = AssemblyItem.viewType ∧ Operation.Item before.memory.memory cell)
    (domain : (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues)
    (spare : cells.length < capacity) (room : cells.length < 2 ^ 32 - 1)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ taken.world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle))
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (memory (append runtimeSafety allocate allocator container cells input key normalized
        ((key.eval meaning taken.world.graph.read).getD 0) preparationOwnership (preparedFrame object copied operands installed)).2)) =
        (true, probeEffects))
    (growth : Option (Growth.Registered.Callbacks σ) := none) :
    let value := (key.eval meaning taken.world.graph.read).getD 0
    let row : Storage.Cell := ⟨copied.item, value, object, operands.items, key.sequence, operands.address⟩
    ∃ installed appended after finalOwner,
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      append runtimeSafety allocate allocator container cells input key normalized value preparationOwnership
        (preparedFrame object copied operands installed) growth = (.ok true, appended) ∧
      execution ops allocate runtimeSafety allocator container source itemSource meaning input key normalized true cells taken.world growth =
        ((.ok (some .success), Storage.publishedOwnership), after) ∧
      Valid (memory after) ∧ (memory after).memory.heap.lookup container = some finalOwner ∧
      finalOwner.type = Owner.viewType runtimeSafety ∧ finalOwner.writable = true ∧
      Memory.Vector allocator (memory after).heap lifetime (cells ++ [row]) ∧
      Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory after) ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ (cells.length + 1), .scalar (.int false 64 capacity)) ∧
      DescriptorRelation.Prefix (memory after).memory lifetime (cells ++ [row]) ∧
      Memory.GraphResident allocator (memory after).heap (cells ++ [row]) ∧
      AssemblyItem.Owned allocator object (memory after) ∧
      AssemblyClone.NativeFields.Represents (memory after).memory ⟨object, 0⟩ copied ∧
      (∀ slice, AssemblyClone.Physical.payload copied = some slice → AssemblyItemDeinit.Owned allocator slice (memory after)) ∧
      (∀ payload, copied.verbatim = some payload → AssemblyClone.Physical.Reads (memory after).memory payload.data) ∧
      Memory.SliceValid allocator (memory after).heap normalized ∧
      OwnedKeys.Live allocator ⟨(memory after).effects.keys, (memory after).heap⟩ ∧
      OwnedKeys.Unique (memory after).effects.keys ∧
      OwnedKeys.Apart (memory after).effects.keys
        (fun address => ∃ cell ∈ cells ++ [row], cell.arguments ≠ [] ∧ address = cell.argumentsAddress) ∧
      BorrowedQuery.Native.AcceptedQueries allocator (Owner.headerAddress ⟨container, 0⟩) (cells ++ [row]) (memory after) ∧
      (memory after).effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨normalized.address, BitVec.ofNat 32 cells.length⟩ ∧
      (memory after).effects.allocator = (match before.memory.effects.keys key with
        | none => probeEffects
        | some old => if key.arguments.isEmpty then probeEffects else
            ops.arguments.free (OwnedKeys.slice key old) { Publication.forget (memory appended) with effects := probeEffects }) ∧
      (memory after).memory.nextId = middle.memory.nextId ∧ (memory after).memory.nextAddress = middle.memory.nextAddress ∧
      (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] →
        (memory after).heap old.address = none ∧ (memory after).memory.heap.lookup old.address = none) ∧
      (∀ id native, before.memory.memory.heap.lookup id = some native → id ≠ container → id ≠ lifetime →
        (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        (memory after).memory.heap.lookup id = some native) ∧
      (∀ id block, before.memory.heap id = some block → id ≠ lifetime →
        (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        (memory after).heap id = some block) ∧
      (∀ logical ∈ cells ++ [row], ∃ native, (memory after).memory.heap.lookup logical.itemAddress = some native ∧
        native.type = AssemblyItem.viewType ∧ Operation.Item (memory after).memory logical) ∧
      cell input key normalized value Storage.publishedOwnership after = row ∧
      Owner.NativeLock.checkHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        Owner.NativeLock.checkHeader before.memory.memory (Owner.headerAddress ⟨container, 0⟩) := by
  have ownerFrame := entry.native_frame container ownerCell ownerFound
  obtain ⟨_, _, backing, backingFound, backingTyped, backingWritable, backingPersistent⟩ := backingOwned
  have backingFrame := entry.native_frame lifetime backing backingFound
  have takenBacking : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity taken.world.memory :=
    ⟨rfl, ⟨cells, entry.origin.registry _ _ registered⟩, backing, entry.origin.memory _ _ backingFound,
      backingTyped, backingWritable, backingPersistent⟩
  have takenResident : Memory.GraphResident allocator taken.world.memory.heap cells := by
    intro logical member
    refine ⟨entry.origin.registry _ _ (resident logical member).1, ?_⟩
    rcases (resident logical member).2 with empty | stored
    · exact Or.inl empty
    · exact Or.inr (entry.origin.registry _ _ stored)
  have takenItems : ∀ logical ∈ cells, ∃ native, taken.world.memory.memory.heap.lookup logical.itemAddress = some native ∧
      native.type = AssemblyItem.viewType ∧ Operation.Item taken.world.memory.memory logical := by
    intro logical member
    obtain ⟨native, found, typed, query⟩ := oldItems logical member
    exact ⟨native, entry.origin.memory _ _ found, typed,
      AssemblyItem.Query.frame _ _ logical (entry.native_frame _ _ found) query⟩
  obtain ⟨installed, appended, after, finalOwner, assigned, appendedRun, executed, valid,
      finalOwnerFound, finalOwnerTyped, finalOwnerWritable, vector, owned, finalHeader, finalRows,
      finalResident, ownedItem, itemReads, ownedPayload, contents, normalizedKept, live, unique,
      apart, accepted, keys, effects, nextId, nextAddress, retired, native, registry, items, candidate, lock⟩ :=
    spare_success_reached ops allocate runtimeSafety allocator container lifetime capacity object ownerCell source itemSource meaning
      input copied key normalized operands remaining taken.world cells duplicated allocated middle
      entry.origin.held.1.1 entry.item (entry.graph_custody cells resident) entry.publication entry.live entry.unique
      admitted (entry.origin.memory _ _ ownerFound) ownerTyped ownerWritable takenBacking
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header)
      ((readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead)
      (entry.origin.registry _ _ registered) (DescriptorRelation.frame _ _ lifetime cells rows backingFrame)
      takenResident (by simpa only [entry.keys] using keyApart) takenItems domain spare room
      duplicateCall createCall cloneCall probeEffects response growth
  dsimp only at *
  refine ⟨installed, appended, after, finalOwner, assigned, appendedRun, executed, valid,
    finalOwnerFound, finalOwnerTyped, finalOwnerWritable, vector, owned, finalHeader, finalRows,
    finalResident, ownedItem, itemReads, ownedPayload, contents, normalizedKept, live, unique,
    apart, accepted, ?_, ?_, nextId, nextAddress, ?_, ?_, ?_, items, candidate, ?_⟩
  · simpa only [entry.keys] using keys
  · simpa only [entry.keys] using effects
  · intro old found nonempty
    exact retired old (by simpa only [entry.keys] using found) nonempty
  · intro id cell found ownerApart backingApart keyApart
    exact native id cell (entry.origin.memory _ _ found) ownerApart backingApart
      (by simpa only [entry.keys] using keyApart)
  · intro id block found backingApart keyApart
    exact registry id block (entry.origin.registry _ _ found) backingApart
      (by simpa only [entry.keys] using keyApart)
  · exact lock.trans (Owner.NativeLock.checkHeader_eq_of_lookup runtimeSafety before.memory.memory taken.world.memory.memory
      container ownerCell entry.origin.held.1.1.memory ownerFound ownerTyped ownerFrame)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
