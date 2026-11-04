/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeSpareInsertion
import Compiler.Extraction.InternerNativePublishedFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- The reached proper-child frame derives successful spare insertion and
retains allocation and key frames for the common enclosing-parent proof.
No entry origin is reconstructed. -/
theorem CallFrame.spare_published {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (room : (world.graph.representatives.getD []).length < 2 ^ 32 - 1)
    (success : Insertion.Native.SparePublished ops allocate safety allocator owner meaning native key normalized world) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world
    PublishedReturn safety allocator owner rows key normalized world actual := by
  dsimp only [PublishedReturn]
  obtain ⟨domain, capacity, capacityRead, spare, operands, remaining, duplicated, object, allocated, copied, middle,
    probeEffects, duplicateCall, createCall, cloneCall, response⟩ := success
  obtain ⟨added, data, reachedCapacity, facts, custody, privateSource⟩ := frame.1.1
  have same : reachedCapacity = capacity := by
    have equal := (readHeader_capacity _ _ _ _ facts.header).symm.trans capacityRead
    simpa only [Except.ok.injEq, Compiler.ZigAir.Memory.Value.scalar.injEq, Compiler.ZigAir.Scalar.Value.int.injEq,
      true_and, Int.ofNat_inj] using equal
  subst reachedCapacity
  simp only [facts.projected, Option.getD_some] at spare room response ⊢
  have positive : capacity ≠ 0 := by omega
  have root := (facts.storage positive).1.1
  rcases data with ⟨lifetime, offset⟩
  change offset = 0 at root
  subst offset
  have checked := NativeGraph.Facts.spare_success ops allocate safety allocator owner lifetime capacity object source address meaning
    native copied key normalized operands remaining world (rows ++ added) duplicated allocated middle facts frame.2.1 custody
    aligned privateSource admitted domain spare room duplicateCall createCall cloneCall probeEffects response growth
  obtain ⟨result, afterFacts, keys, memory, registry⟩ := checked
  have fresh := (Insertion.Native.duplicate_taken ops allocator normalized operands world.memory duplicated remaining
    facts.valid custody.live admitted duplicateCall).freshBorrow rfl
  refine ⟨result, added, ⟨lifetime, 0⟩, capacity,
    ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩,
    facts, ⟨⟨⟨lifetime, 0⟩, capacity, afterFacts⟩, keys, fresh, ?_, ?_⟩⟩
  · exact fun id cell found apart storage old => memory id cell found apart (storage positive) old
  · exact fun id block found storage old => registry id block found (storage positive) old

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
