/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeFrames
import Compiler.Extraction.InternerPublicationEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Storage

/-- Native graph facts inspect the graph, memory, ownership registry and keys,
not allocator-private instrumentation. All those concrete fields are retained. -/
theorem NativeGraph.Facts.mapAllocator_iff (project : σ → τ) {safety : Bool}
    {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {world : World (Publication.Effects σ)} {rows : List Storage.Cell} :
    NativeGraph.Facts safety allocator owner data capacity (world.mapEffects (Publication.Effects.mapAllocator project)) rows ↔
      NativeGraph.Facts safety allocator owner data capacity world rows := by
  constructor <;> intro facts <;> exact {
    valid := ⟨facts.valid.memory, facts.valid.related, facts.valid.injected⟩, projected := facts.projected, linked := facts.linked,
    ownerLive := facts.ownerLive, header := facts.header, bounded := facts.bounded,
    storage := facts.storage, resident := facts.resident, items := facts.items,
    live := facts.live, unique := facts.unique, apart := facts.apart, data := facts.data }

namespace ConstructorItem.NativeRecursion

/-- Input ownership and graph facts ignore allocator-private instrumentation. -/
theorem InputFrame.mapAllocator_iff (project : σ → τ) {safety : Bool} {allocator owner : Nat}
    {rows : List Storage.Cell} {source : Compiler.ZigAir.Memory.WordArray.View}
    {values : List NodeId} {normalized : ArgumentSlice} {world : World (Publication.Effects σ)} :
    InputFrame safety allocator owner rows source values normalized
      (world.mapEffects (Publication.Effects.mapAllocator project)) ↔
      InputFrame safety allocator owner rows source values normalized world := by
  constructor <;> intro frame
  · obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1
    exact ⟨⟨added, data, capacity, (NativeGraph.Facts.mapAllocator_iff project).mp facts,
      ⟨⟨custody.live, custody.apart⟩, custody.operands⟩, privateSource⟩,
      ⟨⟨⟨frame.2.1.1.memory, frame.2.1.1.related, frame.2.1.1.injected⟩,
        frame.2.1.2⟩, frame.2.2⟩⟩
  · obtain ⟨added, data, capacity, facts, custody, privateSource⟩ := frame.1
    exact ⟨⟨added, data, capacity, (NativeGraph.Facts.mapAllocator_iff project).mpr facts,
      ⟨⟨custody.live, custody.apart⟩, custody.operands⟩, privateSource⟩,
      ⟨⟨⟨frame.2.1.1.memory, frame.2.1.1.related, frame.2.1.1.injected⟩,
        frame.2.1.2⟩, frame.2.2⟩⟩

/-- A live call's structural frame is independent of allocator-private state.
The outer predicate is pulled back explicitly; an allocation admission invariant
in that predicate is not erased by this theorem. -/
theorem CallFrame.mapAllocator_iff (project : σ → τ) {safety : Bool} {allocator owner : Nat}
    {rows : List Storage.Cell} {source : Compiler.ZigAir.Memory.WordArray.View}
    {values : List NodeId} {normalized : ArgumentSlice}
    {address : Compiler.ZigAir.Memory.Address} {native : AssemblyClone.NativeFields.ItemValue}
    {parent : World (Publication.Effects τ) → Prop} {world : World (Publication.Effects σ)} :
    CallFrame safety allocator owner rows source values normalized address native parent
      (world.mapEffects (Publication.Effects.mapAllocator project)) ↔
    CallFrame safety allocator owner rows source values normalized address native
      (fun reached => parent (reached.mapEffects (Publication.Effects.mapAllocator project))) world := by
  exact and_congr (InputFrame.mapAllocator_iff project) Iff.rfl

/-- Erasing allocator instrumentation retains the actual native graph frame;
the parent predicate is transported along that same world map. -/
theorem GraphFrame.mapAllocator (project : σ → τ) {safety : Bool} {allocator owner : Nat}
    {rows : List Storage.Cell} {parent : World (Publication.Effects τ) → Prop} {world : World (Publication.Effects σ)}
    (frame : GraphFrame safety allocator owner rows (fun world => parent (world.mapEffects (Publication.Effects.mapAllocator project))) world) :
    GraphFrame safety allocator owner rows parent (world.mapEffects (Publication.Effects.mapAllocator project)) := by
  obtain ⟨⟨added, data, capacity, facts⟩, retained⟩ := frame
  exact ⟨⟨added, data, capacity, (NativeGraph.Facts.mapAllocator_iff project).mpr facts⟩, retained⟩

end ConstructorItem.NativeRecursion
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
