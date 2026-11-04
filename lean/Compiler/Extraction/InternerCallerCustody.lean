/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionInput

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- An argument buffer protected from map-key retirement while a child changes
the graph. Actual local ownership additionally requires caller provenance; this
predicate alone does not authorize consumption. Unlike normalization provenance,
custody does not equate reached graphs or key tables. Empty slices do not own
their sentinel address. -/
structure Custody (allocator : Nat) (slice : ArgumentSlice)
    (memory : Session (Publication.Effects σ)) : Prop where
  live : Memory.SliceValid allocator memory.heap slice
  apart : OwnedKeys.Apart memory.effects.keys
    (fun address => slice.items ≠ [] ∧ address = slice.address)

/-- Native validity connects the surviving owner to exact initialized words;
no final word representation is supplied. -/
theorem Custody.good {allocator : Nat} {slice : ArgumentSlice}
    {memory : Session (Publication.Effects σ)} (custody : Custody allocator slice memory)
    (valid : Valid memory) (graph : Interner.Heap) :
    Good (view slice) slice.items ⟨graph, memory⟩ :=
  ⟨valid, (Insertion.borrowed_ready allocator slice memory valid custody.live).contents⟩

/-- Publishing the child's fresh owner preserves reached parent privacy.
Original liveness separates the new key; current custody protects old keys. -/
theorem Origin.custody_after_publication
    {allocator : Nat} {source : View} {request : Interner.Request} {values : List NodeId}
    {before : World (Publication.Effects σ)} {taken : State (Publication.Effects σ)}
    {owned : ArgumentSlice} {lookup : Handle} {memory : Session (Publication.Effects σ)}
    {key : Key} {id : NodeId}
    (origin : Origin allocator source request values before taken owned lookup)
    (parent : ArgumentSlice) (initial : SliceValid allocator before.memory.heap parent)
    (current : Custody allocator parent memory) (after : Session (Publication.Effects σ))
    (live : SliceValid allocator after.heap parent)
    (keys : after.effects.keys = OwnedKeys.store memory.effects.keys key ⟨owned.address, id⟩) :
    Custody allocator parent after := by
  refine ⟨live, ?_⟩
  intro query old found nonempty alias
  rw [keys, OwnedKeys.store] at found
  split at found
  · have same := Option.some.inj found
    have fresh := origin.fresh _ _ (initial.resolve_left alias.1)
    exact fresh ((congrArg OwnedKeys.Entry.address same).trans alias.2)
  · exact current.apart query old found nonempty alias

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

variable {σ : Type} {allocator : Nat} {source : View} {itemSource : Compiler.ZigAir.Memory.Address}
  {request : Interner.Request} {values : List NodeId} {input : AssemblyClone.NativeFields.ItemValue}
  {key : Key} {before : World (Publication.Effects σ)} {taken : OwnedCall.State (Publication.Effects σ)}
  {normalized : ArgumentSlice} {lookup : Handle}

/-- The actual normalization/take prefix establishes private caller custody. -/
theorem CallerInput.custody
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup) :
    Caller.Custody allocator normalized taken.world.memory := by
  refine ⟨entry.origin.held.2.1, ?_⟩
  intro query old found nonempty alias
  exact entry.fresh query old found nonempty alias.2.symm

/-- Transport a parent's private buffer through the native child growth frame.
Backing separation follows from the registry block kind; separation from the
newly published key follows from that child's actual normalization freshness.
The reached frame and table below are native execution conclusions, not a
recursive preservation contract. -/
theorem CallerInput.custody_after_growth
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (parent : ArgumentSlice) (custody : Caller.Custody allocator parent before.memory)
    (oldLifetime : Nat) (cells : List Storage.Cell) (after : Session (Publication.Effects σ)) (id : NodeId)
    (vector : Memory.Vector allocator before.memory.heap oldLifetime cells)
    (registry : ∀ address block, before.memory.heap address = some block → address ≠ oldLifetime →
      (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] → address ≠ old.address) →
      after.heap address = some block)
    (keys : after.effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨normalized.address, id⟩) :
    Caller.Custody allocator parent after := by
  apply entry.origin.custody_after_publication parent custody.live custody after ?_ keys
  rcases custody.live with empty | stored
  · exact Or.inl empty
  · by_cases empty : parent.items = []
    · exact Or.inl empty
    · have kept := registry _ _ stored (by
        intro same
        rw [same, vector] at stored
        cases stored) (by
        intro old found nonempty same
        exact custody.apart key old found nonempty ⟨empty, same.symm⟩)
      exact Or.inr kept

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
