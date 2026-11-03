/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionInput
import Compiler.Extraction.StorageTransferredInsertion

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

def transferredFrame (object : Nat) (copied : AssemblyClone.NativeFields.ItemValue)
    (installed : Session (Publication.Effects σ)) : Frame σ :=
  ⟨⟨⟨⟨installed, false⟩, some copied⟩, some object⟩, none⟩

/-- Nondeterministic insertion creates and installs the clone directly from the
caller's taken state. The normalized buffer remains the only argument owner;
all old allocations and keys survive this same production preparation. -/
theorem prepare_transferred_reached (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice)
    (world : World (Publication.Effects σ))
    (cells : List Storage.Cell) (value : Contract.Yul.Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (normalizedLive : Memory.SliceValid allocator world.memory.heap normalized)
    (live : OwnedKeys.Live allocator ⟨world.memory.effects.keys, world.memory.heap⟩)
    (unique : OwnedKeys.Unique world.memory.effects.keys)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item world.memory = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
    let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
    let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, none⟩
    ∃ installed,
      let ready := transferredFrame object copied installed
      (∀ owner, calls.attempt .item owner start = (.ok true, made)) ∧
      (∀ owner, calls.attempt .clone owner made = (.ok true, ready)) ∧
      AssemblyClone.NativeFields.Installed allocator object copied middle installed ∧
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      Memory.SliceValid allocator installed.heap normalized ∧
      OwnedKeys.Live allocator ⟨installed.effects.keys, installed.heap⟩ ∧
      OwnedKeys.Unique installed.effects.keys ∧ installed.effects.keys = world.memory.effects.keys ∧
      (∀ id cell, world.memory.memory.heap.lookup id = some cell → installed.memory.heap.lookup id = some cell) ∧
      (∀ id block, world.memory.heap id = some block → installed.heap id = some block) ∧
      installed.heap object = some ⟨allocator, .item copied.item⟩ ∧ copied.item = input.item := by
  dsimp only
  let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
  obtain ⟨installed, created, cloned, installedPost, assigned, frame, keys, registered, sameItem⟩ :=
    prepare_item ops allocate runtimeSafety allocator container object source itemSource input copied key normalized cells value graph
      start allocated middle initial represented rfl createCall cloneCall
  change installed.effects.keys = world.memory.effects.keys at keys
  change ∀ id cell, world.memory.memory.heap.lookup id = some cell →
    installed.memory.heap.lookup id = some cell ∧ installed.heap id = world.memory.heap id at frame
  have retained := arguments_retained world.memory installed initial
    (fun id cell found => (frame id cell found).2) allocator
  refine ⟨installed, created, cloned, installedPost, assigned, retained _ normalizedLive,
    ?_, ?_, keys, ?_, ?_, registered, sameItem⟩
  · intro query old found
    rw [keys] at found
    exact retained _ (live query old found)
  · rw [keys]; exact unique
  · intro id cell found
    exact (frame id cell found).1
  · intro id block stored
    obtain ⟨cell, found, _⟩ := initial.injected id block stored
    exact (frame id cell found).2.trans stored

/-- The original caller interface specializes preparation at its actual taken world. -/
theorem CallerInput.prepare_transferred (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (request : Interner.Request) (values : List NodeId) (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
    (cells : List Storage.Cell) (value : Contract.Yul.Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (allocated middle : Session (Publication.Effects σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
    let start : Frame σ := ⟨⟨⟨⟨taken.world.memory, false⟩, none⟩, none⟩, none⟩
    let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, none⟩
    ∃ installed,
      let ready := transferredFrame object copied installed
      (∀ owner, calls.attempt .item owner start = (.ok true, made)) ∧
      (∀ owner, calls.attempt .clone owner made = (.ok true, ready)) ∧
      AssemblyClone.NativeFields.Installed allocator object copied middle installed ∧
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      Memory.SliceValid allocator installed.heap normalized ∧
      OwnedKeys.Live allocator ⟨installed.effects.keys, installed.heap⟩ ∧
      OwnedKeys.Unique installed.effects.keys ∧ installed.effects.keys = before.memory.effects.keys ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → installed.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → installed.heap id = some block) ∧
      installed.heap object = some ⟨allocator, .item copied.item⟩ ∧ copied.item = input.item := by
  obtain ⟨installed, created, cloned, post, assigned, normalizedLive, live, unique, keys, native, registry, registered, same⟩ :=
    prepare_transferred_reached ops allocate runtimeSafety allocator container object source itemSource input copied key normalized
      taken.world cells value graph allocated middle entry.origin.held.1.1 entry.item entry.origin.held.2.1 entry.live entry.unique
      createCall cloneCall
  exact ⟨installed, created, cloned, post, assigned, normalizedLive, live, unique, keys.trans entry.keys,
    fun id cell found => native id cell (entry.origin.memory id cell found),
    fun id block found => registry id block (entry.origin.registry id block found), registered, same⟩

/-- Actual transfer, item creation and clone allocation separate every cleanup
address from every pre-caller native allocation. Empty sentinels do not create
an additional owner or a required second release. -/
theorem CallerInput.transferred_cleanup_apart (ops : Operations σ) (allocator object : Nat)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (request : Interner.Request) (values : List NodeId)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice) (lookup : Handle)
    (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
    (allocated middle : Session (Publication.Effects σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item taken.world.memory = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    ∀ id cell, before.memory.memory.heap.lookup id = some cell →
      id ≠ object ∧ ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∧ id ≠ normalized.address := by
  intro id cell found
  have apart := item_cleanup_apart ops allocator object input copied taken.world.memory allocated middle
    entry.origin.held.1.1 createCall cloneCall id cell (entry.origin.memory id cell found)
  exact ⟨apart.1, apart.2, (entry.origin.freshNative id cell found).symm⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
