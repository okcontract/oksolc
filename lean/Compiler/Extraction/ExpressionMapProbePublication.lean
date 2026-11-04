/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapProbeVacancy
import Compiler.Extraction.ExpressionMapTablePublication

namespace Compiler.Extraction.ExpressionMap.Probe
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray Buckets Insertion
open Compiler.Extraction.Cache (Key)

variable {place : Initialization.Placement} {safety : Bool} {receiver bucket index : Nat} {capacity : BitVec 32}
    {fp : BitVec 7} {available size : BitVec 32} {key : Key} {arguments : Address} {id : BitVec 32}
    {before after : State} {hashes : Key → BitVec 64} {table : OwnedKeys.Table}

/-- Retain the complete fingerprint byte through both key writes and the ID
write. The previous boolean metadata frame specializes the same load frame. -/
theorem metadata_published (post : Published place safety receiver bucket index capacity fp available size key arguments id before after)
    (inside : index < capacity.toNat) : Metadata.readByte after bucket index = .ok (Metadata.occupied fp) := by
  obtain ⟨down, marked, middle, erased, counted, installed, keyed, prepared, firstKey, pair⟩ := post.stages
  have geometry := Buckets.geometry capacity.toNat capacity.isLt
  have apart : KeyFields.Outside capacity.toNat index Metadata.byte (24 + index) := by
    simp only [KeyFields.Outside, Metadata.byte, Ty.readOffsets, List.mem_singleton]
    intro position same; subst position; left; omega
  apply Metadata.read_byte_of_load
  exact (pair.metadata_load index inside).trans ((firstKey.outside true false Metadata.byte (24 + index) apart).trans prepared.metadataRead)

theorem Canonical.published (canonical : Canonical before capacity bucket)
    (post : Published place safety receiver bucket index capacity fp available size key arguments id before after)
    (layout : Layout place safety receiver bucket capacity before) (inside : index < capacity.toNat) :
    Canonical after capacity bucket := by
  intro other bound bits read
  by_cases same : other = index
  · subst other
    have equal := Except.ok.inj (read.symm.trans (metadata_published post inside))
    subst bits
    exact Or.inr (Or.inr (Metadata.packed_exact 0 fp).2.2.2.1)
  · exact canonical other bound bits ((post.metadata_other layout other bound same).symm.trans read)

theorem nonfree_published (post : Published place safety receiver bucket index capacity fp available size key arguments id before after)
    (layout : Layout place safety receiver bucket capacity before) (inside : index < capacity.toNat)
    (other : Nat) (bound : other < capacity.toNat) (prior : NonFree before bucket other) : NonFree after bucket other := by
  by_cases same : other = index
  · subst other
    exact ⟨_, metadata_published post inside, (Metadata.packed_exact 0 fp).2.2.2.2⟩
  · obtain ⟨bits, read, notFree⟩ := prior
    exact ⟨bits, (post.metadata_other layout other bound same).trans read, notFree⟩

/-- A probe-selected unused slot extends the placement invariant. Old keys
retain their entry and fingerprint, and marking cannot introduce an early free
slot into any existing path. No post-state routing invariant is assumed. -/
theorem Routing.published (routing : Routing hashes before capacity bucket table) (power : Power capacity)
    (binding : Table.Binding place safety receiver bucket capacity before table)
    (incoming : OwnedKeys.Entry)
    (post : Published place safety receiver bucket index capacity (fingerprint (hashes key)) available size key
      ⟨incoming.address, 0⟩ incoming.id before after)
    (inside : index < capacity.toNat) (vacant : ¬Table.Used before bucket index)
    (route : RouteTo before capacity bucket (hashes key) index)
    (view : Table.EntryView capacity bucket index after key incoming) :
    Routing hashes after capacity bucket (OwnedKeys.store table key incoming) := by
  constructor
  intro query entry found
  by_cases same : query = key
  · subst query
    have equal : incoming = entry := Option.some.inj (by simpa [OwnedKeys.store] using found)
    subst entry
    obtain ⟨distance, bound, selected, earlier⟩ := route
    refine ⟨distance, bound, selected ▸ view, selected ▸ metadata_published post inside, ?_⟩
    intro j before
    exact nonfree_published post binding.layout inside _ (slot_bound power) (earlier j before)
  · have old : table query = some entry := by simpa [OwnedKeys.store, same] using found
    obtain ⟨distance, bound, original, read, earlier⟩ := routing.entries query entry old
    have oldUsed : Table.Used before bucket (slot capacity (hashes query) distance) := by
      simp [Table.Used, Metadata.observe_read_byte, read, Except.map,
        (Metadata.packed_exact 0 (fingerprint (hashes query))).2.2.2.1,
        (Metadata.packed_exact 0 (fingerprint (hashes query))).2.2.2.2]
    have apart : slot capacity (hashes query) distance ≠ index := by intro equal; exact vacant (equal ▸ oldUsed)
    refine ⟨distance, bound, original.frame incoming.id post binding.layout inside (slot_bound power) apart,
      (post.metadata_other binding.layout _ (slot_bound power) apart).trans read, ?_⟩
    intro j before
    exact nonfree_published post binding.layout inside _ (slot_bound power) (earlier j before)

end Compiler.Extraction.ExpressionMap.Probe
