/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInsertionInput
import Compiler.Extraction.InternerInsertionPreparedRollback
import Compiler.Extraction.InternerInsertionOperandSeparation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Shared facts from successful native preparation at the actual reached
world. This proposition names existing execution/ownership observations; it
introduces no state representation and carries no normalization origin. -/
def Preparation (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (world : World (Publication.Effects σ)) (cells : List Storage.Cell) (value : Contract.Yul.Word)
    (graph : Storage.State → Frame σ → Interner.Heap)
    (duplicated allocated middle installed : Session (Publication.Effects σ)) : Prop :=
  let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
  let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
  let dupe : Frame σ := ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩
  let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, some operands⟩
  let ready := preparedFrame object copied operands installed
  (∀ owner, calls.attempt .arguments owner start = (.ok true, dupe)) ∧
  (∀ owner, calls.attempt .item owner dupe = (.ok true, made)) ∧
  (∀ owner, calls.attempt .clone owner made = (.ok true, ready)) ∧
  AssemblyClone.NativeFields.Installed allocator object copied middle installed ∧
  AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
  operands.items = normalized.items ∧ Memory.SliceValid allocator installed.heap operands ∧
  Memory.SliceValid allocator installed.heap normalized ∧
  (operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address) ∧
  Publication.Input allocator source key normalized ⟨graph preparationOwnership ready, installed⟩ ∧
  OwnedKeys.Live allocator ⟨installed.effects.keys, installed.heap⟩ ∧
  OwnedKeys.Unique installed.effects.keys ∧ installed.effects.keys = world.memory.effects.keys ∧
  (∀ id cell, world.memory.memory.heap.lookup id = some cell → installed.memory.heap.lookup id = some cell) ∧
  (∀ id block, world.memory.heap id = some block → installed.heap id = some block) ∧
  installed.heap object = some ⟨allocator, .item copied.item⟩ ∧
  copied.item = input.item ∧ operands.address = world.memory.memory.nextId

/-- The reached validity, item and key owners suffice for native preparation.
Prior child growth/publication is retained; no entry graph or origin is rebased. -/
theorem prepare_reached (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (remaining : Handle) (world : World (Publication.Effects σ)) (cells : List Storage.Cell) (value : Contract.Yul.Word)
    (graph : Storage.State → Frame σ → Interner.Heap) (duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid world.memory) (normalizedLive : Memory.SliceValid allocator world.memory.heap normalized)
    (represented : AssemblyClone.NativeFields.Represents world.memory.memory itemSource input)
    (publication : Publication.Input allocator source key normalized world)
    (live : OwnedKeys.Live allocator ⟨world.memory.effects.keys, world.memory.heap⟩)
    (unique : OwnedKeys.Unique world.memory.effects.keys) (admitted : Admitted ops.arguments)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    ∃ installed, Preparation ops allocate runtimeSafety allocator container object source itemSource input copied key
      normalized operands world cells value graph duplicated allocated middle installed := by
  let start : Frame σ := ⟨⟨⟨⟨world.memory, false⟩, none⟩, none⟩, none⟩
  obtain ⟨installed, duplicateRun, createRun, cloneRun, installedPost, assigned, values, operandsLive,
      normalizedLive, separate, frame, keys, registered, sameItem, fresh⟩ :=
    prepare_owned ops allocate runtimeSafety allocator container object source itemSource input copied key normalized operands cells value graph
      start duplicated allocated middle remaining initial normalizedLive represented rfl admitted duplicateCall createCall cloneCall
  change installed.effects.keys = world.memory.effects.keys at keys
  change ∀ id cell, world.memory.memory.heap.lookup id = some cell →
    installed.memory.heap.lookup id = some cell ∧ installed.heap id = world.memory.heap id at frame
  have retained := arguments_retained world.memory installed initial (fun id cell found => (frame id cell found).2) allocator
  refine ⟨installed, duplicateRun, createRun, cloneRun, installedPost, assigned, values, operandsLive,
    normalizedLive, separate, Publication.Input.frame allocator source key normalized world _ publication keys retained,
    ?_, keys ▸ unique, keys, (fun id cell found => (frame id cell found).1), ?_, registered, sameItem, fresh⟩
  · intro query old found
    rw [keys] at found
    exact retained _ (live query old found)
  · intro id block stored
    obtain ⟨cell, found, _⟩ := initial.injected id block stored
    exact (frame id cell found).2.trans stored

/-- Compose the actual caller origin with insertion's duplication, item creation
and clone installation. The same execution supplies both argument owners, all
installed clone fields, publication admission and the complete old-key invariant.
No post-normalization or post-clone ownership premise is supplied separately. -/
theorem CallerInput.prepare (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (request : Interner.Request) (values : List NodeId) (input copied : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized operands : ArgumentSlice) (lookup remaining : Handle)
    (before : World (Publication.Effects σ)) (taken : OwnedCall.State (Publication.Effects σ))
    (cells : List Storage.Cell) (value : Contract.Yul.Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (admitted : Admitted ops.arguments)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ taken.world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
    let start : Frame σ := ⟨⟨⟨⟨taken.world.memory, false⟩, none⟩, none⟩, none⟩
    let dupe : Frame σ := ⟨⟨⟨⟨duplicated, false⟩, none⟩, none⟩, some operands⟩
    let made : Frame σ := ⟨⟨⟨⟨allocated, false⟩, none⟩, some object⟩, some operands⟩
    ∃ installed,
      let ready := preparedFrame object copied operands installed
      (∀ owner, calls.attempt .arguments owner start = (.ok true, dupe)) ∧
      (∀ owner, calls.attempt .item owner dupe = (.ok true, made)) ∧
      (∀ owner, calls.attempt .clone owner made = (.ok true, ready)) ∧
      AssemblyClone.NativeFields.Installed allocator object copied middle installed ∧
      AssemblyClone.NativeFields.install copied object middle = .ok installed ∧
      operands.items = normalized.items ∧ Memory.SliceValid allocator installed.heap operands ∧
      Memory.SliceValid allocator installed.heap normalized ∧
      (operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address) ∧
      Publication.Input allocator source key normalized ⟨graph preparationOwnership ready, installed⟩ ∧
      OwnedKeys.Live allocator ⟨installed.effects.keys, installed.heap⟩ ∧
      OwnedKeys.Unique installed.effects.keys ∧ installed.effects.keys = before.memory.effects.keys ∧
      (∀ id cell, before.memory.memory.heap.lookup id = some cell → installed.memory.heap.lookup id = some cell) ∧
      (∀ id block, before.memory.heap id = some block → installed.heap id = some block) ∧
      installed.heap object = some ⟨allocator, .item copied.item⟩ ∧
      copied.item = input.item ∧ operands.address = taken.world.memory.memory.nextId := by
  dsimp only
  obtain ⟨installed, duplicateRun, createRun, cloneRun, installedPost, assigned, items, operandsLive,
      normalizedLive, separate, publication, live, unique, keys, nativeFrame, registryFrame, registered, sameItem, fresh⟩ :=
    prepare_reached ops allocate runtimeSafety allocator container object source itemSource input copied key normalized operands
      remaining taken.world cells value graph duplicated allocated middle entry.origin.held.1.1 entry.origin.held.2.1
      entry.item entry.publication entry.live entry.unique admitted duplicateCall createCall cloneCall
  exact ⟨installed, duplicateRun, createRun, cloneRun, installedPost, assigned, items, operandsLive,
    normalizedLive, separate, publication, live, unique, keys.trans entry.keys,
    (fun id cell found => nativeFrame id cell (entry.origin.memory id cell found)),
    (fun id block stored => registryFrame id block (entry.origin.registry id block stored)), registered, sameItem, fresh⟩

variable {σ : Type} {allocator : Nat} {source : View} {itemSource : Compiler.ZigAir.Memory.Address}
  {request : Interner.Request} {values : List NodeId} {input : AssemblyClone.NativeFields.ItemValue}
  {key : Key} {before : World (Publication.Effects σ)} {taken : OwnedCall.State (Publication.Effects σ)}
  {normalized : ArgumentSlice} {lookup : Handle}

/-- The actual caller origin, duplicate, create and clone calls make every
cleanup-owned allocation fresh relative to every native allocation live before
the caller. This includes old key buffers and parent-borrowed allocations;
neither their final survival nor cleanup separation is an input premise. -/
theorem CallerInput.cleanup_apart (ops : Operations σ) (object : Nat)
    (copied : AssemblyClone.NativeFields.ItemValue) (operands : ArgumentSlice) (remaining : Handle)
    (duplicated allocated middle : Session (Publication.Effects σ))
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (admitted : Admitted ops.arguments)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ taken.world.memory = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    ∀ id cell, before.memory.memory.heap.lookup id = some cell →
      id ≠ object ∧ ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∧
      id ≠ operands.address ∧ id ≠ normalized.address := by
  have fresh := preparation_cleanup_apart ops allocator object input copied normalized operands remaining
    taken.world.memory duplicated allocated middle entry.origin.held.1.1 entry.origin.held.2.1
    admitted duplicateCall createCall cloneCall
  intro id cell found
  have apart := fresh id cell (entry.origin.memory id cell found)
  exact ⟨apart.1, apart.2.1, apart.2.2, (entry.origin.freshNative id cell found).symm⟩

/-- The caller's fresh normalized owner and preparation's fresh duplicate are
disjoint from every old key and resident argument. Both spare append and
relocation use this same address argument before publishing the extended graph. -/
theorem CallerInput.extended_arguments_apart
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (cells : List Storage.Cell) (operands : ArgumentSlice) (row : Storage.Cell)
    (resident : Memory.GraphResident allocator before.memory.heap cells)
    (keyApart : OwnedKeys.Apart before.memory.effects.keys
      (fun address => ∃ cell ∈ cells, cell.arguments ≠ [] ∧ address = cell.argumentsAddress))
    (arguments : row.arguments = operands.items) (address : row.argumentsAddress = operands.address)
    (fresh : operands.address = taken.world.memory.memory.nextId)
    (separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address) :
    OwnedKeys.Apart before.memory.effects.keys
      (fun location => ∃ cell ∈ cells ++ [row], cell.arguments ≠ [] ∧ location = cell.argumentsAddress) ∧
    (key.arguments ≠ [] → ¬ (∃ cell ∈ cells ++ [row], cell.arguments ≠ [] ∧ normalized.address = cell.argumentsAddress)) := by
  have checked := Insertion.Native.extended_arguments_apart allocator taken.world normalized operands key cells row
    entry.origin.held.1.1 entry.live (entry.graph_custody cells resident) entry.publication.aligned
    (by simpa only [entry.keys] using keyApart) arguments address fresh separate
  simpa only [entry.keys] using checked

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
