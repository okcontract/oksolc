/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionNative
import Compiler.Extraction.InternerPublicationSuccess
import Compiler.Extraction.OwnedKeysPhysicalGraph
import Compiler.Extraction.RepresentativeDescriptorRelation

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache Contract.Yul
open Compiler.ZigAir.Memory.WordArray
open RepresentativeArray

/-- Retiring a key's argument allocation cannot retire a cloned byte payload:
the registry kinds distinguish their owners. Preserve both ownership and actual
byte reads through the same publication frame, for spare and relocated storage. -/
theorem publication_payload (allocator : Nat) (key : Key) (copied : AssemblyClone.NativeFields.ItemValue)
    (before after : Session (Publication.Effects σ))
    (live : ∀ old, before.effects.keys key = some old →
      Memory.SliceValid allocator before.heap (OwnedKeys.slice key old))
    (owned : ∀ slice, AssemblyClone.Physical.payload copied = some slice →
      AssemblyItemDeinit.Owned allocator slice before)
    (contents : ∀ payload, copied.verbatim = some payload →
      AssemblyClone.Physical.Reads before.memory payload.data)
    (preserved : ∀ id,
      (∀ old, before.effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
      after.heap id = before.heap id ∧ after.memory.heap.lookup id = before.memory.heap.lookup id) :
    (∀ slice, AssemblyClone.Physical.payload copied = some slice →
      AssemblyItemDeinit.Owned allocator slice after) ∧
    (∀ payload, copied.verbatim = some payload → AssemblyClone.Physical.Reads after.memory payload.data) := by
  have payloadFrame (slice : AssemblyItemDeinit.Bytes) (selected : AssemblyClone.Physical.payload copied = some slice)
      (nonempty : slice.length ≠ 0) :
      after.heap slice.address = before.heap slice.address ∧
        after.memory.heap.lookup slice.address = before.memory.heap.lookup slice.address := by
    have stored := (owned slice selected).resolve_left nonempty
    apply preserved slice.address
    intro old found keyNonempty same
    have keyStored := (live old found).resolve_left keyNonempty
    change before.heap old.address = some ⟨allocator, .arguments key.arguments⟩ at keyStored
    rw [← same, stored.1] at keyStored
    cases keyStored
  constructor
  · intro slice selected
    by_cases empty : slice.length = 0
    · exact Or.inl empty
    · obtain ⟨stored, native, found, typed, writable, stack, offset⟩ := (owned slice selected).resolve_left empty
      have frame := payloadFrame slice selected empty
      exact Or.inr ⟨frame.1.trans stored, native, frame.2.trans found, typed, writable, stack, offset⟩
  · intro payload selected
    by_cases empty : payload.data.contents = []
    · intro byte index present
      simp [empty] at present
    · have selectedSlice : AssemblyClone.Physical.payload copied = some (AssemblyClone.Physical.descriptor payload.data) := by
        simp only [AssemblyClone.Physical.payload, selected, Option.map_some]
      have nonempty : (AssemblyClone.Physical.descriptor payload.data).length ≠ 0 := by
        intro zero
        exact empty (List.eq_nil_of_length_eq_zero zero)
      exact (contents payload selected).frame _ _ payload.data (payloadFrame _ selectedSlice nonempty).2

/-- Publication derives its old-key release precondition from the reached input.
The existing representative storage cannot be that argument allocation: registry
kinds separate the backing, and native types separate its owner. -/
theorem publication_rows (ops : Operations σ) (allocate : Backing.Registry.Allocate σ) (runtimeSafety : Bool)
    (allocator container lifetime capacity : Nat) (ownerCell : Compiler.ZigAir.Memory.Allocation)
    (source : View) (itemSource : Compiler.ZigAir.Memory.Address) (input : AssemblyClone.NativeFields.ItemValue)
    (key : Key) (normalized : ArgumentSlice) (cells retained : List Storage.Cell) (value : Word)
    (graph : Storage.State → Frame σ → Interner.Heap) (ownership : Storage.State) (before : Frame σ)
    (growth : Option (Growth.Registered.Callbacks σ)) (effects : σ)
    (initial : Valid (memory before))
    (ownerFound : (memory before).memory.heap.lookup container = some ownerCell)
    (ownerTyped : ownerCell.type = Owner.viewType runtimeSafety)
    (owned : Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory before))
    (registered : Memory.Vector allocator (memory before).heap lifetime retained)
    (header : readHeader (memory before).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ retained.length, .scalar (.int false 64 capacity)))
    (rows : DescriptorRelation.Prefix (memory before).memory lifetime retained) (bounded : retained.length ≤ capacity)
    (live : Memory.SliceValid allocator (memory before).heap normalized)
    (publication : Publication.Input allocator source key normalized ⟨graph ownership before, memory before⟩)
    (response : ops.probe key (Publication.forget (memory before)) = (true, effects)) :
    ∃ after,
      (callbacks ops allocate runtimeSafety allocator container source itemSource input key normalized cells value graph growth).attempt
        .publish ownership before = (.ok true, after) ∧
      Valid (memory after) ∧ Backing.Release.Owned allocator ⟨lifetime, 0⟩ capacity (memory after) ∧
      Memory.Vector allocator (memory after).heap lifetime retained ∧
      readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
        .ok (.slice itemsType ⟨lifetime, 0⟩ retained.length, .scalar (.int false 64 capacity)) ∧
      DescriptorRelation.Prefix (memory after).memory lifetime retained ∧
      (∀ id, representativeFields (memory after).memory (Owner.headerAddress ⟨container, 0⟩) id =
        .ok ((Storage.representativeProgram.run retained id).map (DescriptorRelation.values id.toNat))) ∧
      Memory.SliceValid allocator (memory after).heap normalized ∧
      (memory after).effects.keys = OwnedKeys.store (memory before).effects.keys key ⟨normalized.address, BitVec.ofNat 32 cells.length⟩ ∧
      (memory after).memory.nextId = (memory before).memory.nextId ∧
      (memory after).memory.nextAddress = (memory before).memory.nextAddress ∧
      (memory after).effects.allocator = (match (memory before).effects.keys key with
        | none => effects
        | some old => if key.arguments.isEmpty then effects else
            ops.arguments.free (OwnedKeys.slice key old) { Publication.forget (memory before) with effects }) ∧
      (∀ old, (memory before).effects.keys key = some old → key.arguments ≠ [] →
        (memory after).heap old.address = none ∧ (memory after).memory.heap.lookup old.address = none) ∧
      (∀ id, (memory before).heap id = none ∧ (memory before).memory.heap.lookup id = none →
        (memory after).heap id = none ∧ (memory after).memory.heap.lookup id = none) ∧
      (∀ id, (∀ old, (memory before).effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) →
        (memory after).heap id = (memory before).heap id ∧
        (memory after).memory.heap.lookup id = (memory before).memory.heap.lookup id) ∧
      (∀ kept, OwnedKeys.Live allocator ⟨(memory before).effects.keys, (memory before).heap⟩ →
        OwnedKeys.Unique (memory before).effects.keys →
        OwnedKeys.Fresh (memory before).effects.keys key ⟨normalized.address, BitVec.ofNat 32 cells.length⟩ →
        OwnedKeys.Apart (memory before).effects.keys kept →
        (key.arguments ≠ [] → ¬ kept normalized.address) →
        OwnedKeys.Physical.Preserved allocator kept normalized
          ⟨(memory before).effects.keys, memory before⟩ ⟨(memory after).effects.keys, memory after⟩) ∧
      (∀ residentCells, Memory.GraphResident allocator (memory before).heap residentCells →
        OwnedKeys.Apart (memory before).effects.keys
          (fun address => ∃ cell ∈ residentCells, cell.arguments ≠ [] ∧ address = cell.argumentsAddress) →
        Memory.GraphResident allocator (memory after).heap residentCells ∧
          (∀ cell ∈ residentCells,
            (memory after).memory.heap.lookup cell.itemAddress = (memory before).memory.heap.lookup cell.itemAddress ∧
            (cell.arguments ≠ [] → (memory after).memory.heap.lookup cell.argumentsAddress =
              (memory before).memory.heap.lookup cell.argumentsAddress))) := by
  let world : World (Publication.Effects σ) := ⟨graph ownership before, memory before⟩
  obtain ⟨published, ran, completed, incoming⟩ := Publication.publish_success ops.probe ops.arguments allocator source key normalized
    (BitVec.ofNat 32 cells.length) world effects initial publication live response
  dsimp only [world] at ran
  let after := withMemory before { published.memory with effects := { published.memory.effects with keys := published.table } }
  have frame (id : Nat)
      (apart : ∀ old, (memory before).effects.keys key = some old → key.arguments ≠ [] → id ≠ old.address) :
      (memory after).heap id = (memory before).heap id ∧
      (memory after).memory.heap.lookup id = (memory before).memory.heap.lookup id :=
    ⟨completed.registry_frame _ _ _ _ _ id apart, completed.frame id apart⟩
  have backingApart (old : OwnedKeys.Entry) (found : (memory before).effects.keys key = some old)
      (nonempty : key.arguments ≠ []) : lifetime ≠ old.address := by
    have stored := (publication.live old found).resolve_left nonempty
    change (memory before).heap old.address = some ⟨allocator, .arguments key.arguments⟩ at stored
    intro same; rw [← same, registered] at stored; cases stored
  have ownerApart (old : OwnedKeys.Entry) (found : (memory before).effects.keys key = some old)
      (nonempty : key.arguments ≠ []) : container ≠ old.address := by
    have stored := (publication.live old found).resolve_left nonempty
    obtain ⟨⟨cell, found, typed, _⟩, _⟩ := initial.related allocator old.address key.arguments nonempty stored
    exact (memory before).memory.heap.lookup_ne_of_type_ne container old.address ownerCell cell ownerFound found
      (by simp [ownerTyped, typed, Owner.viewType])
  have backingFrame := frame lifetime backingApart
  have ownerFrame := (frame container ownerApart).2
  have vector : Memory.Vector allocator (memory after).heap lifetime retained := backingFrame.1.trans registered
  have finalRows := DescriptorRelation.frame (memory before).memory (memory after).memory lifetime retained rows backingFrame.2
  have finalHeader : readHeader (memory after).memory (Owner.headerAddress ⟨container, 0⟩) =
      .ok (.slice itemsType ⟨lifetime, 0⟩ retained.length, .scalar (.int false 64 capacity)) := by
    unfold readHeader readItems
    rw [readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) itemsOffset ownerFrame,
      readField_eq_of_lookup _ _ (Owner.headerAddress ⟨container, 0⟩) capacityOffset ownerFrame]
    exact header
  obtain ⟨root, _, backing, found, typed, writable, persistent⟩ := owned
  have finalValid : Valid (memory after) := ⟨completed.valid.memory, completed.valid.related, completed.valid.injected⟩
  refine ⟨after, ?_, finalValid, ⟨root, ⟨retained, vector⟩, backing, backingFrame.2.trans found, typed, writable, persistent⟩,
    vector, finalHeader, finalRows, ?_, incoming, ?_, completed.nextId, completed.nextAddress, ?_, ?_, ?_, frame, ?_, ?_⟩
  · simp only [callbacks, Insertion.callbacks, ran, Publication.commit, Except.mapError]
    rfl
  · intro id
    exact DescriptorRelation.query _ _ lifetime capacity backing retained id finalValid.memory
      (readHeader_items _ _ _ _ finalHeader) (backingFrame.2.trans found) typed writable bounded finalRows
  · exact congrArg OwnedKeys.State.table completed.logical
  · have observed := congrArg Publication.Effects.allocator completed.effects
    dsimp only [world] at observed
    cases found : (memory before).effects.keys key with
    | none => simpa only [found] using observed
    | some old =>
      by_cases empty : key.arguments.isEmpty = true <;>
        simpa only [found, empty, ↓reduceIte, Publication.external, Publication.forget] using observed
  · intro old present nonempty
    exact ⟨completed.registry_dead _ _ _ _ _ old present nonempty, completed.dead old present nonempty⟩
  · intro id dead
    have apart (old : OwnedKeys.Entry) (present : (memory before).effects.keys key = some old) (nonempty : key.arguments ≠ []) : id ≠ old.address := by
      have stored := (publication.live old present).resolve_left nonempty
      change (memory before).heap old.address = some ⟨allocator, .arguments key.arguments⟩ at stored
      intro same; rw [same, stored] at dead; cases dead.1
    exact ⟨(frame id apart).1.trans dead.1, (frame id apart).2.trans dead.2⟩
  · intro kept allLive unique fresh apart incomingApart
    have preserved := completed.preserves (Publication.external ops.arguments) allocator key
      ⟨normalized.address, BitVec.ofNat 32 cells.length⟩ _ published kept allLive unique
      (by simpa only [OwnedKeys.slice, publication.aligned] using live) fresh apart incomingApart
    exact ⟨finalValid, preserved.live, preserved.unique, preserved.apart, preserved.frame, preserved.typedFrame,
      preserved.nextId, preserved.nextAddress, incoming⟩
  · intro residentCells resident apart
    exact completed.graph_resident (Publication.external ops.arguments) allocator key _ _ published residentCells
      publication.live resident apart

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
