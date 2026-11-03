/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionItemPreparation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

theorem ownsArguments_complete (allocator : Nat) (slice : ArgumentSlice) (heap : Memory.Heap)
    (live : Memory.SliceValid allocator heap slice) : ownsArguments allocator slice heap = true := by
  rcases live with empty | stored
  · simp [ownsArguments, empty]
  · simp [ownsArguments, stored]

/-- Existing typed allocations carry the registry facts needed to preserve
arbitrary argument owners; an empty sentinel requires no allocation. -/
theorem arguments_retained (before after : Session σ) (initial : Valid before)
    (frame : ∀ id cell, before.memory.heap.lookup id = some cell → after.heap id = before.heap id)
    (allocator : Nat) (slice : ArgumentSlice) (live : Memory.SliceValid allocator before.heap slice) :
    Memory.SliceValid allocator after.heap slice := by
  rcases live with empty | stored
  · exact Or.inl empty
  · obtain ⟨cell, found, _⟩ := initial.injected slice.address _ stored
    exact Or.inr ((frame slice.address cell found).trans stored)

/-- Invert the actual successful duplication, deriving contents, ownership,
freshness and old-allocation frames from the existing complete take theorem. -/
theorem duplicate_taken (ops : Operations σ) (allocator : Nat) (normalized operands : ArgumentSlice)
    (before after : Session (Publication.Effects σ)) (remaining : Handle)
    (initial : Valid before) (live : Memory.SliceValid allocator before.heap normalized)
    (admitted : Admitted ops.arguments)
    (executed : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before = (.ok (operands, remaining), after)) :
    Taken allocator (view normalized) normalized.items ⟨view normalized, normalized.items, none⟩
      before operands remaining after := by
  obtain ⟨result, reached, ran, post⟩ := take_refines (Publication.external ops.arguments) allocator
    (view normalized) normalized.items ⟨view normalized, normalized.items, none⟩ before
    (borrowed_ready allocator normalized before initial live) (Publication.external_admitted ops.arguments admitted)
  have same := Prod.mk.inj (ran.symm.trans executed)
  rcases same with ⟨rfl, rfl⟩
  exact post

/-- Successful preparation allocates its duplicate, object and clone payload
after every allocation in the reached input. The normalized owner may already
be present there; its separation is an enclosing cleanup obligation. -/
theorem preparation_cleanup_apart (ops : Operations σ) (allocator object : Nat)
    (input copied : AssemblyClone.NativeFields.ItemValue) (normalized operands : ArgumentSlice)
    (remaining : Handle) (before duplicated allocated middle : Session (Publication.Effects σ))
    (initial : Valid before) (live : Memory.SliceValid allocator before.heap normalized)
    (admitted : Admitted ops.arguments)
    (duplicateCall : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ before = (.ok (operands, remaining), duplicated))
    (createCall : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloneCall : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    ∀ id cell, before.memory.heap.lookup id = some cell →
      id ≠ object ∧ ¬AssemblyItemDeinit.Touches (AssemblyClone.Physical.payload copied) id ∧
      id ≠ operands.address := by
  have duplicatedPost := duplicate_taken ops allocator normalized operands before duplicated remaining
    initial live admitted duplicateCall
  intro id cell found
  have apart := item_cleanup_apart ops allocator object input copied duplicated allocated middle
    duplicatedPost.ready.valid createCall cloneCall id cell (duplicatedPost.frame id cell found).1
  refine ⟨apart.1, apart.2, ?_⟩
  rw [duplicatedPost.freshBorrow rfl]
  exact Nat.ne_of_lt (Compiler.ZigAir.Memory.valid_lookup before.memory id cell initial.memory found).1

/-- The actual duplication/create/clone callbacks establish the installed clone
and both argument owners. No final object/payload owner or field read is a premise.
Every original native allocation and its registry entry survives preparation. -/
theorem prepare_owned (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container object : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input copied : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized operands : ArgumentSlice)
    (cells : List Storage.Cell) (value : Word) (graph : Storage.State → Frame σ → Interner.Heap)
    (before : Frame σ) (duplicated allocated middle : Session (Publication.Effects σ)) (remaining : Handle)
    (initial : Valid (memory before)) (normalizedLive : Memory.SliceValid allocator (memory before).heap normalized)
    (represented : AssemblyClone.NativeFields.Represents (memory before).memory itemSource input)
    (absent : before.item.object = none) (admitted : Admitted ops.arguments)
    (taken : takeOwned normalizationOwnershipCode (Publication.external ops.arguments) allocator
      ⟨view normalized, normalized.items, none⟩ (memory before) = (.ok (operands, remaining), duplicated))
    (created : AssemblyItem.Creation.create (observe ops.create) allocator input.item duplicated = (.ok object, allocated))
    (cloned : AssemblyClone.Physical.run (observe ops.copy) allocator input allocated = (.ok copied, middle)) :
    let calls := callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph
    let dupe : Frame σ := { withMemory before duplicated with duplicate := some operands }
    let made : Frame σ := { withMemory dupe allocated with item := { (withMemory dupe allocated).item with object := some object } }
    ∃ installed,
      let ready : Frame σ := { withMemory made installed with item := { (withMemory made installed).item with clone :=
        { (withMemory made installed).item.clone with value := some copied } } }
      (∀ owner, calls.attempt .arguments owner before = (.ok true, dupe)) ∧
      (∀ owner, calls.attempt .item owner dupe = (.ok true, made)) ∧
      (∀ owner, calls.attempt .clone owner made = (.ok true, ready)) ∧
      AssemblyClone.NativeFields.Installed allocator object copied middle (memory ready) ∧
      AssemblyClone.NativeFields.install copied object middle = .ok (memory ready) ∧
      operands.items = normalized.items ∧ Memory.SliceValid allocator (memory ready).heap operands ∧
      Memory.SliceValid allocator (memory ready).heap normalized ∧
      (operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address) ∧
      (∀ id cell, (memory before).memory.heap.lookup id = some cell →
        (memory ready).memory.heap.lookup id = some cell ∧ (memory ready).heap id = (memory before).heap id) ∧
      (memory ready).effects.keys = (memory before).effects.keys ∧
      (memory ready).heap object = some ⟨allocator, .item copied.item⟩ ∧
      copied.item = input.item ∧ operands.address = (memory before).memory.nextId := by
  dsimp only
  let dupe : Frame σ := { withMemory before duplicated with duplicate := some operands }
  let made : Frame σ := { withMemory dupe allocated with item := { (withMemory dupe allocated).item with object := some object } }
  have duplicatedPost := duplicate_taken ops allocator normalized operands (memory before) duplicated remaining initial normalizedLive admitted taken
  obtain ⟨sourceCell, sourceFound⟩ := represented.live
  have sourceKept := represented.frame ((duplicatedPost.frame itemSource.allocation sourceCell sourceFound).1.trans sourceFound.symm)
  obtain ⟨installed, createCall, cloneCall, installedPost, assigned, itemFrame, itemKeys, registered, sameItem⟩ :=
    prepare_item ops allocate runtimeSafety allocator container object source itemSource input copied key normalized cells value graph
      dupe allocated middle duplicatedPost.ready.valid sourceKept absent created cloned
  have originalFrame : ∀ id cell, (memory before).memory.heap.lookup id = some cell →
      installed.memory.heap.lookup id = some cell ∧ installed.heap id = (memory before).heap id := by
    intro id cell found
    have duplicateFrame := duplicatedPost.frame id cell found
    have kept := itemFrame id cell duplicateFrame.1
    exact ⟨kept.1, kept.2.trans duplicateFrame.2⟩
  have retained := arguments_retained duplicated installed duplicatedPost.ready.valid
    (fun id cell found => (itemFrame id cell found).2) allocator
  have duplicateKeys := arguments_keys ops.arguments allocator normalized (memory before)
  rw [taken] at duplicateKeys
  refine ⟨installed, ?_, createCall, cloneCall, installedPost, assigned, duplicatedPost.values,
    retained operands duplicatedPost.live,
    arguments_retained (memory before) installed initial (fun id cell found => (originalFrame id cell found).2)
      allocator normalized normalizedLive,
    (fun _ nonempty => duplicatedPost.separate nonempty), originalFrame, itemKeys.trans duplicateKeys,
    registered, sameItem, duplicatedPost.freshBorrow rfl⟩
  intro owner
  have owned := ownsArguments_complete allocator normalized (memory before).heap normalizedLive
  simp only [callbacks, Insertion.callbacks, owned, Bool.not_true, Bool.false_eq_true, ↓reduceIte, taken, Except.mapError]

/-- Transport the existing native graph geometry and publication admission
through preparation's derived old-allocation frame. Both insertion outcomes
use this connection; none of these reached-state facts is an extra premise. -/
theorem preparation_graph_frame (allocator container lifetime capacity : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (key : Key) (normalized : ArgumentSlice) (cells : List Storage.Cell)
    (before after : World (Publication.Effects σ)) (initial : Valid before.memory)
    (frame : ∀ id cell, before.memory.memory.heap.lookup id = some cell →
      after.memory.memory.heap.lookup id = some cell ∧ after.memory.heap id = before.memory.heap id)
    (keys : after.memory.effects.keys = before.memory.effects.keys)
    (ownerFound : before.memory.memory.heap.lookup container = some ownerCell)
    (owned : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity before.memory)
    (header : readItems before.memory.memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length))
    (capacityRead : readField before.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 capacity)))
    (registered : Memory.Vector allocator before.memory.heap lifetime cells)
    (rows : DescriptorRelation.Prefix before.memory.memory lifetime cells)
    (publication : Publication.Input allocator source key normalized before) :
    after.memory.memory.heap.lookup container = some ownerCell ∧
    Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity after.memory ∧
    readItems after.memory.memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ cells.length) ∧
    readField after.memory.memory (Owner.headerAddress ⟨container, 0⟩) capacityOffset =
      .ok (.scalar (.int false 64 capacity)) ∧
    Memory.Vector allocator after.memory.heap lifetime cells ∧
    DescriptorRelation.Prefix after.memory.memory lifetime cells ∧
    Publication.Input allocator source key normalized after := by
  have ownerFrame := (frame container ownerCell ownerFound).1.trans ownerFound.symm
  obtain ⟨root, _, backing, found, typed, writable, persistent⟩ := owned
  have backingFrame := (frame lifetime backing found).1.trans found.symm
  have vector : Memory.Vector allocator after.memory.heap lifetime cells := (frame lifetime backing found).2.trans registered
  exact ⟨(frame container ownerCell ownerFound).1, ⟨root, ⟨cells, vector⟩, backing, (frame lifetime backing found).1, typed, writable, persistent⟩,
    (readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame).trans header,
    (readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame).trans capacityRead,
    vector, DescriptorRelation.frame _ _ lifetime cells rows backingFrame,
    Publication.Input.frame allocator source key normalized before after publication keys
      (arguments_retained before.memory after.memory initial (fun id cell found => (frame id cell found).2) allocator)⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
