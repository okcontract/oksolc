/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReachedTransferredGrowth
import Compiler.Extraction.InternerNativeGraphInsertion
import Compiler.Extraction.InternerNativeTransferredFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Actual create/clone and allocator responses for transferred nonempty
relocation. There is no duplicate or key-probe response in this source branch. -/
def RelocatedTransferred (ops : Operations σ) (allocate : Backing.Registry.Allocate σ)
    (allocator owner : Nat) (input : AssemblyClone.NativeFields.ItemValue)
    (growth : Option (Growth.Registered.Callbacks σ)) (world : World (Publication.Effects σ)) : Prop :=
  (input.item.kind.toNat : Int) ∈ AssemblyItem.itemTagValues ∧
  ∃ oldCapacity capacity : Nat,
    readField world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset = .ok (.scalar (.int false 64 oldCapacity)) ∧
    oldCapacity ≠ 0 ∧ oldCapacity < Append.nextLength (world.graph.representatives.getD []).length ∧
    capacity = Capacity.grow (Append.nextLength (world.graph.representatives.getD []).length) ∧
    capacity * 32 < Compiler.ZigAir.Memory.addressLimit ∧
  ∃ context returnAddress freeBacking, growth = some ⟨.noRemap context returnAddress, freeBacking⟩ ∧
  ∃ object allocated copied middle base allocationEffects,
    AssemblyItem.Creation.create (observe ops.create) allocator input.item world.memory = (.ok object, allocated) ∧
    AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle) ∧
    (∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      allocate allocator (capacity * 32) 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨capacity * 32, 8⟩ base) ∧
    Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ()

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray
open Insertion Insertion.Native

/-- The reached call frame and actual source observations derive transfer
completion. Graph reconstruction is shared with successful publication; native
preparation and relocation are the same results consumed by the older caller. -/
theorem CallFrame.transferred_growing {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (success : RelocatedTransferred ops allocate allocator owner native growth world) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized false growth world
    TransferredReturn safety allocator owner rows normalized world actual := by
  dsimp only [TransferredReturn]
  obtain ⟨domain, oldCapacity, capacity, capacityRead, oldNonempty, full, selected, size,
    context, returnAddress, freeBacking, growthIdentity, object, allocated, copied, middle, base, allocationEffects,
    createCall, cloneCall, backing, unlocked⟩ := success
  rw [growthIdentity]
  obtain ⟨added, data, reachedCapacity, facts, custody, _⟩ := frame.1.1
  have same : reachedCapacity = oldCapacity := by
    have equal := (readHeader_capacity _ _ _ _ facts.header).symm.trans capacityRead
    simpa only [Except.ok.injEq, Compiler.ZigAir.Memory.Value.scalar.injEq, Compiler.ZigAir.Scalar.Value.int.injEq,
      true_and, Int.ofNat_inj] using equal
  subst reachedCapacity
  simp only [facts.projected, Option.getD_some] at full selected room ⊢
  have root := (facts.storage oldNonempty).1.1
  rcases data with ⟨lifetime, offset⟩
  change offset = 0 at root
  subst offset
  obtain ⟨ownerCell, ownerFound, ownerTyped, ownerWritable⟩ := facts.ownerLive
  obtain ⟨backingOwned, vector, descriptors⟩ := facts.storage oldNonempty
  have fields := Append.readHeader_parts world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) _ _ facts.header
  obtain ⟨installed, after, finalOwner, _, _, executed, valid, finalOwnerFound, finalOwnerTyped,
    finalOwnerWritable, vector, owned, header, finalRows, resident, _, itemReads, _, _, _, live, unique,
    apart, _, keys, _, _, _, _, _, memory, registry, items, candidate⟩ :=
    transferred_growing_success_reached ops allocate freeBacking safety allocator owner lifetime oldCapacity capacity object base context returnAddress
      ownerCell source address meaning native copied key normalized world (rows ++ added) allocated middle
      facts.valid frame.2.1 custody.toCustody facts.live facts.unique ownerFound ownerTyped ownerWritable backingOwned
      fields.1 fields.2 vector descriptors facts.resident facts.apart facts.items domain oldNonempty full selected size room
      createCall cloneCall allocationEffects backing unlocked
  have width : Append.nextLength (rows ++ added).length < Compiler.ZigAir.Memory.addressLimit := by
    simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]
    omega
  have enough : (rows ++ added).length + 1 ≤ capacity := selected ▸ Capacity.grow_sufficient _ width
  let row : Storage.Cell := ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object,
    normalized.items, key.sequence, normalized.address⟩
  have completed := facts.insert_success_at false ops allocate (some ⟨.noRemap context returnAddress, freeBacking⟩)
    source address meaning native key normalized after row middle.memory.nextId capacity executed candidate valid
    ⟨finalOwner, finalOwnerFound, finalOwnerTyped, finalOwnerWritable⟩ header enough owned vector finalRows
    resident items live unique apart keys (by intro _; exact itemReads .data)
    (fun id cell found ownerApart backingApart _ => memory id cell found ownerApart backingApart)
  refine ⟨congrArg Prod.fst completed.1, added, ⟨lifetime, 0⟩, oldCapacity, row, facts, ?_⟩
  rw [completed.1]
  exact ⟨⟨⟨middle.memory.nextId, 0⟩, capacity, completed.1 ▸ completed.2⟩, keys, rfl,
    fun id cell found apart storage => memory id cell found apart (storage oldNonempty),
    fun id block stored storage => registry id block stored (storage oldNonempty)⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
