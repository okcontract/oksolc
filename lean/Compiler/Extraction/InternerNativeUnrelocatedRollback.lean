/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReachedUnrelocatedRollback
import Compiler.Extraction.InternerNativeRollbackFrame
import Compiler.Extraction.InternerInsertionNativeBody

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- First/spare rollback reconstructs the same reached graph from derived
native postconditions, retaining the same storage facts for enclosing callers.
The preparation and probe equations describe actual calls, not preservation. -/
theorem CallFrame.unrelocated_rollback_frame {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (capacity object : Nat) (operands : ArgumentSlice) (remaining : Handle)
    (duplicated allocated middle : Session (Publication.Effects σ)) (copied : AssemblyClone.NativeFields.ItemValue)
    (capacityRead : readField world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 capacity)))
    (selected : capacity = 0 ∨ (world.graph.representatives.getD []).length < capacity)
    (first : capacity = 0 → ∃ base allocationEffects,
      (∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
        allocate allocator 160 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base) ∧
      Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ())
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (Insertion.observe ops.create) allocator native.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (Insertion.observe ops.copy) allocator native allocated = (.ok copied, middle))
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (Insertion.memory (Insertion.Native.append safety allocate allocator owner
        (world.graph.representatives.getD []) native key normalized ((key.eval meaning world.graph.read).getD 0)
        Storage.preparationOwnership (Insertion.Native.preparedFrame object copied operands installed)).2)) = (false, probeEffects)) :
    RollbackReturn safety allocator owner rows normalized world
      (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world) := by
  obtain ⟨added, data, reachedCapacity, facts, custody, privateSource⟩ := frame.1.1
  have same : reachedCapacity = capacity := by
    simpa only [Except.ok.injEq, Compiler.ZigAir.Memory.Value.scalar.injEq,
      Compiler.ZigAir.Scalar.Value.int.injEq, true_and, Int.ofNat_inj] using
      (readHeader_capacity _ _ _ _ facts.header).symm.trans capacityRead
  subst reachedCapacity
  simp only [facts.projected, Option.getD_some] at selected room response
  obtain ⟨ownerCell, ownerFound, ownerTyped, ownerWritable⟩ := facts.ownerLive
  obtain ⟨after, executed, lifetime, finalCapacity, valid, vector, owned, header, inside, descriptors,
      keys, retained, finalOwner, consumed⟩ :=
    Insertion.Native.unrelocated_publication_oom_reached ops allocate safety allocator owner capacity object data ownerCell
      source address meaning native copied key normalized operands remaining world (rows ++ added) duplicated allocated middle growth
      facts.valid custody.live frame.2.1 (custody.publication source key aligned privateSource facts.live) admitted
      ownerFound ownerTyped ownerWritable facts.header facts.bounded facts.storage selected first room
      duplicateCall createCall cloneCall probeEffects response
  have inserted := Insertion.Native.insert_unpublished_projected ops allocate safety allocator owner source address meaning native key normalized
    true world (rows ++ added) growth data
    (readHeader_items _ _ _ _ facts.header) facts.projected (some .allocationFailure)
    ((Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership) after rfl rfl executed
  have preserved := facts.frame_storage normalized (Insertion.memory after) ⟨lifetime, 0⟩ finalCapacity
    custody.live custody.apart custody.operands valid retained keys finalOwner header (Nat.le_of_lt inside)
    (fun _ => ⟨owned, vector, descriptors⟩)
  rw [inserted]
  refine ⟨rfl, added, data, capacity, facts, ?_⟩
  refine {
    native := ⟨⟨lifetime, 0⟩, finalCapacity, preserved.logical_fields _ rfl rfl⟩
    projected := rfl
    keys := keys
    retained := retained
    consumed := ?_ }
  by_cases empty : normalized.items = []
  · exact Or.inl empty
  · exact Or.inr (consumed empty)

/-- The original graph-only interface is a projection of the shared rollback
completion. Its read-coherence premise is used only for exact logical equality. -/
theorem CallFrame.unrelocated_rollback {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (reads : world.graph.read = Storage.readValue (world.graph.representatives.getD []))
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (capacity object : Nat) (operands : ArgumentSlice) (remaining : Handle)
    (duplicated allocated middle : Session (Publication.Effects σ)) (copied : AssemblyClone.NativeFields.ItemValue)
    (capacityRead : readField world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 capacity)))
    (selected : capacity = 0 ∨ (world.graph.representatives.getD []).length < capacity)
    (first : capacity = 0 → ∃ base allocationEffects,
      (∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
        allocate allocator 160 8 installed.effects.allocator = (some base, allocationEffects) ∧
        Compiler.ZigAir.Memory.RegionAllocation.Fits installed.memory ⟨160, 8⟩ base) ∧
      Owner.NativeLock.checkHeader world.memory.memory (Owner.headerAddress ⟨owner, 0⟩) = .ok ())
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (Insertion.observe ops.create) allocator native.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (Insertion.observe ops.copy) allocator native allocated = (.ok copied, middle))
    (probeEffects : σ)
    (response : ∀ installed, AssemblyClone.NativeFields.install copied object middle = .ok installed →
      ops.probe key (Publication.forget (Insertion.memory (Insertion.Native.append safety allocate allocator owner
        (world.graph.representatives.getD []) native key normalized ((key.eval meaning world.graph.read).getD 0)
        Storage.preparationOwnership (Insertion.Native.preparedFrame object copied operands installed)).2)) = (false, probeEffects)) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world
    actual.1 = .error (.language .outOfMemory) ∧
      (∃ added data capacity, NativeGraph.Facts safety allocator owner data capacity actual.2 (rows ++ added)) ∧
      actual.2.graph = world.graph ∧ Consumed normalized actual.2.memory := by
  exact (frame.unrelocated_rollback_frame ops allocate growth meaning key admitted aligned room capacity object operands remaining
    duplicated allocated middle copied capacityRead selected first duplicateCall createCall cloneCall probeEffects response).graph reads

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
