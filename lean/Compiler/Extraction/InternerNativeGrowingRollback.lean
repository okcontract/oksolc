/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionReachedGrowingRollback
import Compiler.Extraction.InternerRelocatedPublication
import Compiler.Extraction.InternerNativeRollbackFrame
import Compiler.Extraction.InternerInsertionNativeBody

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Actual reached relocation and publication refusal derive the restored
native graph with the new backing still live. The old rows and keys survive,
while preparation owners and normalized input are consumed.
The retained storage postconditions also serve enclosing-parent preservation. -/
theorem CallFrame.growing_rollback_frame {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (refused : Insertion.Native.RelocatedPublication ops allocate safety allocator owner meaning native key normalized growth false world) :
    RollbackReturn safety allocator owner rows normalized world
      (Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world) := by
  obtain ⟨oldCapacity, capacity, capacityRead, oldNonempty, full, selected, size,
    context, returnAddress, release, growthIdentity, operands, remaining, duplicated, object, allocated, copied, middle,
    base, allocationEffects, probeEffects, duplicateCall, createCall, cloneCall, backing, response, unlocked⟩ := refused
  rw [growthIdentity]
  obtain ⟨added, data, reachedCapacity, facts, custody, privateSource⟩ := frame.1.1
  have same : reachedCapacity = oldCapacity := by
    have equal := (readHeader_capacity _ _ _ _ facts.header).symm.trans capacityRead
    simpa only [Except.ok.injEq, Compiler.ZigAir.Memory.Value.scalar.injEq, Compiler.ZigAir.Scalar.Value.int.injEq,
      true_and, Int.ofNat_inj] using equal
  subst reachedCapacity
  simp only [facts.projected, Option.getD_some] at full selected room response
  obtain ⟨owned, vector, descriptors⟩ := facts.storage oldNonempty
  have root := owned.1
  rcases data with ⟨lifetime, offset⟩
  change offset = 0 at root
  subst offset
  obtain ⟨ownerCell, ownerFound, ownerTyped, ownerWritable⟩ := facts.ownerLive
  obtain ⟨after, executed, valid, finalVector, finalOwned, header, finalRows, keys, _, _,
      _, _, _, _, _, retained, finalOwner, destroyed⟩ :=
    Insertion.Native.growing_publication_oom_reached ops allocate release safety allocator owner lifetime oldCapacity capacity
      object base context returnAddress ownerCell source address meaning native copied key normalized operands remaining world (rows ++ added)
      duplicated allocated middle facts.valid custody.live frame.2.1
      (custody.publication source key aligned privateSource facts.live) admitted ownerFound ownerTyped ownerWritable owned
      (readHeader_items _ _ _ _ facts.header) capacityRead vector descriptors oldNonempty full selected size room
      duplicateCall createCall cloneCall allocationEffects backing probeEffects response unlocked
  have inserted := Insertion.Native.insert_unpublished_projected ops allocate safety allocator owner source address meaning native key normalized
    true world (rows ++ added) (some ⟨.noRemap context returnAddress, release⟩) ⟨lifetime, 0⟩
    (readHeader_items _ _ _ _ facts.header) facts.projected (some .allocationFailure)
    ((Storage.Cleanup.sequence [.lastValue, .pop, .normalized]).run Storage.publicationOwnership) after rfl rfl executed
  have width : Append.nextLength (rows ++ added).length < Compiler.ZigAir.Memory.addressLimit := by
    simp only [Append.nextLength, Compiler.ZigAir.Memory.addressLimit]; omega
  have enough := selected ▸ Capacity.grow_sufficient _ width
  obtain ⟨finalCell, found, shape⟩ := finalOwner
  have storageFrame := fun id cell located ownerApart (oldApart : oldCapacity ≠ 0 → id ≠ lifetime) normalizedApart =>
    retained id cell located ownerApart (oldApart oldNonempty) normalizedApart
  have preserved := facts.frame_storage normalized (Insertion.memory after) ⟨middle.memory.nextId, 0⟩ capacity
    custody.live custody.apart custody.operands valid
    storageFrame
    keys ⟨finalCell, found, shape.2.1.trans ownerTyped, shape.2.2.1.trans ownerWritable⟩ header
    (by simp only [Append.nextLength] at enough; omega) (fun _ => ⟨finalOwned, finalVector, finalRows⟩)
  rw [inserted]
  refine ⟨rfl, added, ⟨lifetime, 0⟩, oldCapacity, facts, ?_⟩
  refine {
    native := ⟨⟨middle.memory.nextId, 0⟩, capacity, preserved.logical_fields _ rfl rfl⟩
    projected := rfl
    keys := keys
    retained := storageFrame
    consumed := ?_ }
  by_cases empty : normalized.items = []
  · exact Or.inl empty
  · exact Or.inr (destroyed normalized.address (Or.inr (Or.inr (Or.inr ⟨empty, rfl⟩))))

/-- The original graph-only interface is a projection of the shared rollback
completion. Its read-coherence premise is used only for exact logical equality. -/
theorem CallFrame.growing_rollback {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (reads : world.graph.read = Storage.readValue (world.graph.representatives.getD []))
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (refused : Insertion.Native.RelocatedPublication ops allocate safety allocator owner meaning native key normalized growth false world) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world
    actual.1 = .error (.language .outOfMemory) ∧
      (∃ added data capacity, NativeGraph.Facts safety allocator owner data capacity actual.2 (rows ++ added)) ∧
      actual.2.graph = world.graph ∧ Consumed normalized actual.2.memory := by
  exact (frame.growing_rollback_frame ops allocate growth meaning key admitted aligned room refused).graph reads

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
