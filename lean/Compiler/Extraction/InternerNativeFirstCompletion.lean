/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFirstInsertion
import Compiler.Extraction.InternerNativePublishedFrame

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Zero reached capacity entails no prior rows. Actual first-publication
observations derive the new native graph with either capacity adapter, retaining
allocation and key frames without excluding the old empty sentinel. -/
theorem CallFrame.first_published {safety : Bool} {allocator owner : Nat} {rows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {world : World (Publication.Effects σ)}
    (frame : CallFrame safety allocator owner rows source values normalized address native parent world)
    (ops : Insertion.Operations σ) (allocate : Backing.Registry.Allocate σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (meaning : Meaning) (key : Key)
    (admitted : Admitted ops.arguments) (aligned : key.arguments = normalized.items)
    (success : Insertion.Native.FirstPublished ops allocate safety allocator owner meaning native key normalized world) :
    let actual := Insertion.Native.insert ops allocate safety allocator owner source address meaning native key normalized true growth world
    PublishedReturn safety allocator owner rows key normalized world actual := by
  dsimp only [PublishedReturn]
  obtain ⟨domain, capacityRead, operands, remaining, duplicated, object, allocated, copied, middle,
    base, allocationEffects, probeEffects, duplicateCall, createCall, cloneCall, backing, response, unlocked⟩ := success
  obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1.1
  have observedZero : (capacity : Int) = 0 := by
    simpa only [Except.ok.injEq, Compiler.ZigAir.Memory.Value.scalar.injEq,
      Compiler.ZigAir.Scalar.Value.int.injEq, true_and] using
      (readHeader_capacity _ _ _ _ facts.header).symm.trans capacityRead
  have zero : capacity = 0 := by omega
  subst capacity
  have empty : rows ++ added = [] := List.eq_nil_of_length_eq_zero (by have bound := facts.bounded; omega)
  have projected : world.graph.representatives = some [] := facts.projected.trans (congrArg some empty)
  rw [empty] at facts custody
  have checked := NativeGraph.Facts.first_success ops allocate safety allocator owner object base data source address meaning
    native copied key normalized operands remaining world duplicated allocated middle facts frame.2.1 custody aligned privateSource
    admitted domain duplicateCall createCall cloneCall allocationEffects backing probeEffects response unlocked growth
  obtain ⟨result, afterFacts, keys, _, _, memory, _, registry⟩ := checked
  have fresh := (Insertion.Native.duplicate_taken ops allocator normalized operands world.memory duplicated remaining
    facts.valid custody.live admitted duplicateCall).freshBorrow rfl
  refine ⟨?_, added, data, 0,
    ⟨copied.item, (key.eval meaning world.graph.read).getD 0, object, operands.items, key.sequence, operands.address⟩,
    ?_, ?_⟩
  · simpa only [projected, Option.getD_some] using result
  · simpa only [empty] using facts
  · refine ⟨⟨⟨middle.memory.nextId, 0⟩, 5, ?_⟩, ?_, fresh, ?_, ?_⟩
    · simpa only [empty, List.nil_append] using afterFacts
    · simpa only [empty, Storage.idFor] using keys
    · exact fun id cell found apart _ old => memory id cell found apart old
    · exact fun id block found _ old => registry id block found old

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
