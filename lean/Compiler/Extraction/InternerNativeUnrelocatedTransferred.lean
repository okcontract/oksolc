/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeTransferredCompletion
import Compiler.Extraction.InternerInsertionUnrelocatedAppend

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Actual source observations for transfer into empty or spare storage. Only
empty storage requires a backing allocation and an unlocked header. Neither
branch consults optional growth, duplication or publication callbacks. -/
def UnrelocatedTransferred (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (allocator owner : Nat) (input : AssemblyClone.NativeFields.ItemValue)
    (world : World (Publication.Effects σ)) : Prop :=
  (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues ∧
  ∃ oldCapacity : Nat,
    readField world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)) ∧
    (oldCapacity = 0 ∨ (world.graph.representatives.getD []).length < oldCapacity) ∧
  ∃ object allocated copied middle,
    AssemblyItem.Creation.create (observe ops.create) allocator input.item world.memory = (.ok object, allocated) ∧
    AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle) ∧
    (oldCapacity = 0 → ∃ base allocationEffects,
      (∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
        allocate allocator 160 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base) ∧
      Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ())

/-- Success observations for the three derived backing branches. -/
def TransferredObservation (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (allocator owner : Nat) (input : AssemblyClone.NativeFields.ItemValue)
    (growth : Option (Growth.Registered.Callbacks σ)) (world : World (Publication.Effects σ)) : Prop :=
  UnrelocatedTransferred ops allocate allocator owner input world ∨
    RelocatedTransferred ops allocate allocator owner input growth world

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native

/-- First and spare transfer specialize the same physical append as publication
rollback, and the same graph reconstruction and ancestor frame as relocation. -/
theorem CallFrame.transferred_unrelocated {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (success : UnrelocatedTransferred ops allocate allocator owner native world) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized false growth world
    TransferredReturn safety allocator owner rows normalized world actual := by
  dsimp only [TransferredReturn]
  obtain ⟨domain, oldCapacity, capacityRead, selected, object, allocated, copied, middle, createCall, cloneCall, first⟩ := success
  obtain ⟨added, oldData, reachedCapacity, facts, custody, _⟩ := frame.1.1
  have same : reachedCapacity = oldCapacity := by
    have equal := (readHeader_capacity _ _ _ _ facts.header).symm.trans capacityRead
    simpa only [Except.ok.injEq, Compiler.ZigAir.Memory.Value.scalar.injEq, Compiler.ZigAir.Scalar.Value.int.injEq,
      true_and, Int.ofNat_inj] using equal
  subst reachedCapacity
  simp only [facts.projected, Option.getD_some] at selected room ⊢
  let cells := rows ++ added
  let value := (key.eval meaning world.graph.read).getD 0
  let row : Storage.Cell := ⟨copied.item, value, object, normalized.items, key.sequence, normalized.address⟩
  let graph : Storage.State → Insertion.Native.Frame σ → Interner.Heap := fun state reached => Interner.InsertionExecution.project cells world.graph.table
    (cell native key normalized value state reached) key state
  obtain ⟨installed, createRun, cloneRun, installedPost, assigned, normalizedLive, allLive, unique, keys,
      nativeFrame, registryFrame, objectRegistered, sameItem⟩ :=
    prepare_transferred_reached ops allocate safety allocator owner object source address native copied key
      normalized world cells value graph allocated middle facts.valid frame.2.1 custody.toCustody.live
      facts.live facts.unique createCall cloneCall
  have prepared := facts.frame (after := { world with memory := installed }) installedPost.valid
    facts.projected rfl keys (fun id cell found _ => nativeFrame id cell found) registryFrame
  obtain ⟨ownerCell, ownerFound, ownerTyped, ownerWritable⟩ := facts.ownerLive
  have preparedFirst (zero : oldCapacity = 0) : ∃ base effects,
      allocate allocator 160 8 installed.effects.allocator = (some base, effects) ∧
      Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base ∧
      Owner.NativeLock.checkHeader installed.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok () := by
    obtain ⟨base, effects, allocation, unlocked⟩ := first zero
    exact ⟨base, effects, (allocation installed assigned).1, (allocation installed assigned).2,
      (Owner.NativeLock.checkHeader_eq_of_lookup safety world.memory.memory installed.memory owner ownerCell
        installedPost.valid.memory ownerFound ownerTyped ((nativeFrame _ _ ownerFound).trans ownerFound.symm)).trans unlocked⟩
  have argumentBound : normalized.items.length < Compiler.ZigAir.Memory.addressLimit := by
    have represented := (borrowed_ready allocator normalized world.memory facts.valid custody.toCustody.live).contents
    have bound := Compiler.ZigAir.Memory.WordAllocation.source_bytes_bound world.memory.memory (view normalized) normalized.items represented
    omega
  let ready := transferredFrame object copied installed
  obtain ⟨lifetime, capacity, after, finalOwner, appended, _, valid, appendKeys, found, typed, writable, owned,
    enough, vector, header, _, _, itemOwned, represented, _, argumentsKept, descriptors, appendRegistry, appendFrame⟩ :=
    unrelocated_append_owned_at allocate safety allocator owner oldCapacity object oldData ownerCell native copied key
      normalized normalized cells value transferredPreparation middle ready growth installedPost rfl rfl rfl
      (nativeFrame _ _ ownerFound) ownerTyped ownerWritable prepared.header prepared.bounded prepared.storage
      selected preparedFirst room argumentBound
  have finalKeys := appendKeys.trans keys
  have retained (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation)
      (found : world.memory.memory.heap.lookup id = some cell) (apart : id ≠ owner)
      (backing : oldCapacity ≠ 0 → id ≠ oldData.allocation) :
      (memory after).memory.heap.lookup id = some cell :=
    (appendFrame id cell (nativeFrame _ _ found) apart backing).1
  have registry (id : Nat) (block : Memory.Allocation) (stored : world.memory.heap id = some block)
      (backing : oldCapacity ≠ 0 → id ≠ oldData.allocation) : (memory after).heap id = some block :=
    appendRegistry id block (registryFrame _ _ stored) backing
  have resident : Memory.GraphResident allocator (memory after).heap (cells ++ [row]) := by
    intro logical member
    rcases List.mem_append.mp member with previous | added
    · have old := prepared.resident logical previous
      refine ⟨appendRegistry _ _ old.1 ?_, argumentsKept allocator _ old.2⟩
      intro positive same
      have stored := old.1
      rw [same, (prepared.storage positive).2.1] at stored
      cases stored
    · have same := List.mem_singleton.mp added
      subst logical
      refine ⟨appendRegistry _ _ objectRegistered ?_, argumentsKept allocator _ normalizedLive⟩
      intro positive same
      change object = oldData.allocation at same
      have stored := objectRegistered
      rw [same, (prepared.storage positive).2.1] at stored
      cases stored
  have items : ∀ logical ∈ cells ++ [row], ∃ item,
      (memory after).memory.heap.lookup logical.itemAddress = some item ∧
      item.type = AssemblyItem.viewType ∧ Operation.Item (memory after).memory logical := by
    intro logical member
    rcases List.mem_append.mp member with previous | added
    · obtain ⟨item, located, shape, query⟩ := facts.items logical previous
      have apart := world.memory.memory.heap.lookup_ne_of_type_ne _ _ item ownerCell located ownerFound
        (by simp [shape, ownerTyped, AssemblyItem.viewType, Owner.viewType])
      have backing (positive : oldCapacity ≠ 0) : logical.itemAddress ≠ oldData.allocation := by
        obtain ⟨_, _, array, stored, arrayType, _⟩ := (facts.storage positive).1
        exact world.memory.memory.heap.lookup_ne_of_type_ne _ _ item array located stored
          (by simp [shape, arrayType, AssemblyItem.viewType, Backing.type])
      have kept := retained _ _ located apart backing
      exact ⟨item, kept, shape, AssemblyItem.Query.frame _ _ logical (kept.trans located.symm) query⟩
    · have same := List.mem_singleton.mp added
      subst logical
      obtain ⟨_, item, located, shape, _⟩ := itemOwned
      refine ⟨item, located, shape, ?_⟩
      apply AssemblyItem.Query.of_members (memory after).memory row item valid.memory located shape
      · simpa only [row, sameItem] using domain
      · simpa only [row, (AssemblyClone.NativeFields.key_fields copied).1] using represented .kind
      · simpa only [row, (AssemblyClone.NativeFields.key_fields copied).2.1] using represented .instruction
  have apart : OwnedKeys.Apart (memory after).effects.keys
      (fun address => ∃ logical ∈ cells ++ [row], logical.arguments ≠ [] ∧ address = logical.argumentsAddress) := by
    rw [finalKeys]
    intro query old stored nonempty kept
    obtain ⟨logical, member, nonemptyArguments, aliases⟩ := kept
    rcases List.mem_append.mp member with previous | added
    · exact facts.apart query old stored nonempty ⟨logical, previous, nonemptyArguments, aliases⟩
    · have same := List.mem_singleton.mp added
      subst logical
      exact custody.toCustody.apart query old stored nonempty ⟨nonemptyArguments, aliases⟩
  let calls := callbacks ops allocate safety allocator owner source address native key normalized cells value graph growth
  let start : Insertion.Native.Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
  let made : Insertion.Native.Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, none⟩
  change ∀ state, calls.attempt .item state start = (.ok true, made) at createRun
  change ∀ state, calls.attempt .clone state made = (.ok true, ready) at cloneRun
  have executed := Storage.insert_transferred_success calls start made ready after createRun cloneRun appended
  have execution : Insertion.Native.execution ops allocate safety allocator owner source address meaning native key normalized false cells world growth =
      ((.ok (some .success), Storage.transferredOwnership), after) := by
    simpa only [Insertion.Native.execution, cells, room, decide_true] using executed
  have candidate := append_cell safety allocate allocator owner cells native key normalized value transferredPreparation
    transferredOwnership ready growth
  rw [appended] at candidate
  have completed := facts.insert_success_at false ops allocate growth source address meaning native key normalized after row lifetime capacity
    execution candidate valid ⟨finalOwner, found, typed, writable⟩ header (Nat.succ_le_of_lt enough) owned vector descriptors resident items
    (by intro query old stored; rw [appendKeys] at stored; exact argumentsKept allocator _ (allLive query old stored))
    (by rw [appendKeys]; exact unique) apart finalKeys (by intro _; exact represented .data)
    (fun id cell located ownerApart backingApart _ => retained id cell located ownerApart (fun _ => backingApart))
  refine ⟨congrArg Prod.fst completed.1, added, oldData, oldCapacity, row, facts, ?_⟩
  rw [completed.1]
  exact ⟨⟨⟨lifetime, 0⟩, capacity, completed.1 ▸ completed.2⟩, finalKeys, rfl, retained, registry⟩

/-- The recursive consumer selects a derived transfer proof from source facts. -/
theorem CallFrame.transferred {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (success : TransferredObservation ops allocate allocator owner native growth world) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized false growth world
    TransferredReturn safety allocator owner rows normalized world actual := by
  rcases success with unrelocated | relocated
  · exact frame.transferred_unrelocated ops allocate growth meaning key room unrelocated
  · exact frame.transferred_growing ops allocate growth meaning key room relocated

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
