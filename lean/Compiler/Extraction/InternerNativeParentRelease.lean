/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeParentReturn
import Compiler.Extraction.InternerCallerReleaseFrame
import Compiler.Extraction.InternerNativeStorageSeparation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

/-- Shared parent preservation for private cleanup and storage rollback. The
original child origin separates live parent allocations from the private owner;
reached allocation types separate them from storage writes. -/
theorem CallFrame.storage_frame_rows
    {safety : Bool} {allocator owner oldCapacity : Nat} {oldData : Compiler.ZigAir.Memory.Address}
    {rows parentRows : List Storage.Cell} {source : View} {values : List NodeId}
    {normalized : ArgumentSlice} {address : Compiler.ZigAir.Memory.Address}
    {native : AssemblyClone.NativeFields.ItemValue} {outer : World (Publication.Effects σ) → Prop}
    {original before after : World (Publication.Effects σ)}
    {childSource : View} {request : Interner.Request} {childValues : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator childSource request childValues original taken owned lookup)
    (initial : CallFrame safety allocator owner parentRows source values normalized address native outer original)
    (reached : CallFrame safety allocator owner parentRows source values normalized address native outer before)
    (facts : NativeGraph.Facts safety allocator owner oldData oldCapacity before rows)
    (suffix : List Storage.Cell)
    (transferred : ∀ row ∈ suffix, row.arguments ≠ [] → row.argumentsAddress = owned.address)
    (afterNative : ∃ data capacity, NativeGraph.Facts safety allocator owner data capacity after (rows ++ suffix))
    (keys : after.memory.effects.keys = before.memory.effects.keys)
    (retained : ∀ id cell, before.memory.memory.heap.lookup id = some cell → id ≠ owner →
      (oldCapacity ≠ 0 → id ≠ oldData.allocation) → (owned.items ≠ [] → id ≠ owned.address) →
      after.memory.memory.heap.lookup id = some cell)
    (registered : ∀ id block, before.memory.heap id = some block → id ≠ owner →
      (oldCapacity ≠ 0 → id ≠ oldData.allocation) → (owned.items ≠ [] → id ≠ owned.address) →
      after.memory.heap id = some block)
    (outerKept : outer after) :
    CallFrame safety allocator owner parentRows source values normalized address native outer after := by
  obtain ⟨added, _, _, parentFacts, custody, privateSource⟩ := reached.1.1
  have sameRows := Option.some.inj (parentFacts.projected.symm.trans facts.projected)
  subst rows
  have sourceApart := reached.arraySource.storage facts
  have itemApart := reached.2.1.storage facts
  have sourceMemory : source.length ≠ 0 → ∀ cell, before.memory.memory.heap.lookup source.allocation = some cell →
      after.memory.memory.heap.lookup source.allocation = some cell := by
    intro nonempty cell found
    obtain ⟨old, originalFound⟩ := initial.1.2.1.backed nonempty
    exact (retained _ cell found (sourceApart nonempty).1 (sourceApart nonempty).2
      (fun _ => (origin.freshNative _ old originalFound).symm))
  have live : SliceValid allocator after.memory.heap normalized := by
    by_cases empty : normalized.items = []
    · exact Or.inl empty
    · have stored := reached.1.2.2.1.resolve_left empty
      have nonzero : (view normalized).length ≠ 0 := by
        change normalized.items.length ≠ 0
        exact Nat.ne_of_gt (List.length_pos_iff.mpr empty)
      have apart := (ArraySource.registered facts.valid reached.1.2.2.1).storage facts nonzero
      have distinct := origin.fresh _ _ (initial.1.2.2.1.resolve_left empty)
      exact Or.inr (registered _ _ stored apart.1 apart.2 (fun _ => distinct.symm))
  have sourceKept : Represents after.memory.memory source values := by
    by_cases empty : values = []
    · exact ⟨reached.1.2.1.2.1, by intro index inside; simp [empty] at inside⟩
    · have nonempty : source.length ≠ 0 := by
        rw [← reached.1.2.1.2.1]; exact Nat.ne_of_gt (List.length_pos_iff.mpr empty)
      obtain ⟨cell, found⟩ := reached.1.2.1.backed nonempty
      exact represented_frame source values reached.1.2.1.2 ((sourceMemory nonempty cell found).trans found.symm)
  obtain ⟨oldItem, originalItem⟩ := initial.2.1.live
  obtain ⟨item, found⟩ := reached.2.1.live
  have itemKept := reached.2.1.frame ((retained _ item found itemApart.1 itemApart.2
    (fun _ => (origin.freshNative _ oldItem originalItem).symm)).trans found.symm)
  obtain ⟨data, capacity, afterFacts⟩ := afterNative
  have operands : normalized.items ≠ [] → ∀ row ∈ (parentRows ++ added) ++ suffix,
      row.arguments ≠ [] → normalized.address ≠ row.argumentsAddress := by
    intro nonempty row member arguments
    rcases List.mem_append.mp member with old | new
    · exact custody.operands nonempty row old arguments
    · rw [transferred row new arguments]
      exact (origin.fresh _ _ (initial.1.2.2.1.resolve_left nonempty)).symm
  exact ⟨⟨⟨added ++ suffix, data, capacity, by simpa only [List.append_assoc] using afterFacts,
      ⟨⟨live, by rw [keys]; exact custody.apart⟩, by simpa only [List.append_assoc] using operands⟩,
      by rw [keys]; exact privateSource⟩,
      ⟨afterFacts.valid, sourceKept⟩, live, reached.1.2.2.2⟩,
    itemKept, outerKept, reached.arraySource.frame sourceMemory⟩

/-- Cleanup and rollback specialize the storage frame without adding rows. -/
theorem CallFrame.storage_frame
    {safety : Bool} {allocator owner oldCapacity : Nat} {oldData : Compiler.ZigAir.Memory.Address}
    {rows parentRows : List Storage.Cell} {source : View} {values : List NodeId}
    {normalized : ArgumentSlice} {address : Compiler.ZigAir.Memory.Address}
    {native : AssemblyClone.NativeFields.ItemValue} {outer : World (Publication.Effects σ) → Prop}
    {original before after : World (Publication.Effects σ)}
    {childSource : View} {request : Interner.Request} {childValues : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator childSource request childValues original taken owned lookup)
    (initial : CallFrame safety allocator owner parentRows source values normalized address native outer original)
    (reached : CallFrame safety allocator owner parentRows source values normalized address native outer before)
    (facts : NativeGraph.Facts safety allocator owner oldData oldCapacity before rows)
    (afterNative : ∃ data capacity, NativeGraph.Facts safety allocator owner data capacity after rows)
    (keys : after.memory.effects.keys = before.memory.effects.keys)
    (retained : ∀ id cell, before.memory.memory.heap.lookup id = some cell → id ≠ owner →
      (oldCapacity ≠ 0 → id ≠ oldData.allocation) → (owned.items ≠ [] → id ≠ owned.address) →
      after.memory.memory.heap.lookup id = some cell ∧ after.memory.heap id = before.memory.heap id)
    (outerKept : outer after) :
    CallFrame safety allocator owner parentRows source values normalized address native outer after := by
  exact CallFrame.storage_frame_rows origin initial reached facts [] (by simp)
    (by simpa only [List.append_nil] using afterNative) keys
    (fun id cell found ownerApart backingApart childApart => (retained id cell found ownerApart backingApart childApart).1)
    (by
      intro id block stored ownerApart backingApart childApart
      obtain ⟨cell, found, _⟩ := facts.valid.injected _ _ stored
      exact (retained id cell found ownerApart backingApart childApart).2.trans stored) outerKept

/-- A child-private cleanup frames the live parent using the child's actual
normalization origin. Reached graph custody protects graph objects; original
parent liveness separates its source, normalized allocation and item from the
child owner. Allocation history, effects and new temporary allocations remain
those of the reached cleanup. -/
theorem CallFrame.private_frame {safety : Bool} {allocator owner : Nat} {rows currentRows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before world : World (Publication.Effects σ)}
    {childSource : View} {childRequest : Interner.Request} {childValues : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator childSource childRequest childValues before taken owned lookup)
    (initial : CallFrame safety allocator owner rows source values normalized address native parent before)
    (reached : CallFrame safety allocator owner rows source values normalized address native parent world)
    {after : Session (Publication.Effects σ)}
    (projected : world.graph.representatives = some currentRows)
    (custody : Caller.GraphCustody allocator owned currentRows world.memory)
    (valid : Valid after) (frame : Insertion.Native.PrivateFrame owned world.memory after)
    (outer : parent { world with memory := after }) :
    CallFrame safety allocator owner rows source values normalized address native parent { world with memory := after } := by
  obtain ⟨added, data, capacity, facts, parentCustody, privateSource⟩ := reached.1.1
  have sameRows := Option.some.inj (facts.projected.symm.trans projected)
  have privateOwned : Caller.GraphCustody allocator owned (rows ++ added) world.memory := sameRows.symm ▸ custody
  have kept := facts.frame_private owned after privateOwned.live privateOwned.apart
    privateOwned.operands valid frame.allocations frame.keys
  exact CallFrame.storage_frame origin initial reached facts ⟨data, capacity, kept⟩ frame.keys
    (fun id cell found _ _ apart => frame.allocations id cell found apart) outer

/-- Actual free specializes the same parent frame used by private insertion
cleanup. The release-parent law requires the current private graph custody;
publication/handoff never supplies this condition for an installed owner. -/
theorem CallFrame.release {safety : Bool} {allocator owner : Nat} {rows currentRows : List Storage.Cell}
    {source : View} {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects σ) → Prop} {before world : World (Publication.Effects σ)}
    {childSource : View} {childRequest : Interner.Request} {childValues : List NodeId}
    {taken : State (Publication.Effects σ)} {owned : ArgumentSlice} {lookup : Handle}
    (origin : Caller.Origin allocator childSource childRequest childValues before taken owned lookup)
    (initial : CallFrame safety allocator owner rows source values normalized address native parent before)
    (reached : CallFrame safety allocator owner rows source values normalized address native parent world)
    (host : External σ) (projected : world.graph.representatives = some currentRows)
    (custody : Caller.GraphCustody allocator owned currentRows world.memory)
    (localOuter : ∀ after, free (Publication.external host) allocator owned world.memory = (.ok (), after) →
      parent { world with memory := after }) :
    ∀ after, free (Publication.external host) allocator owned world.memory = (.ok (), after) →
      CallFrame safety allocator owner rows source values normalized address native parent { world with memory := after } := by
  intro after freed
  obtain ⟨actual, ran, valid, released, _⟩ :=
    origin.release_frame (Publication.external host) world reached.1.2.1.1 custody.live
  have same : actual = after := congrArg Prod.snd (ran.symm.trans freed)
  subst actual
  exact CallFrame.private_frame origin initial reached projected custody valid
    (Insertion.Native.free_private_frame host allocator owned world.memory after freed released) (localOuter after freed)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.NativeRecursion
