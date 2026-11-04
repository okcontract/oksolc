/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ExpressionMapCandidate
import Compiler.Extraction.ExpressionMapTablePublication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray ExpressionMap

/-- One admission proof supplies native query words and their byte extent to
both individual candidate checks and the complete probe. -/
theorem Facts.query_view {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (key : Key) (owned : ArgumentSlice) (aligned : key.arguments = owned.items)
    (custody : Caller.GraphCustody allocator owned rows before.memory) :
    Represents before.memory.memory (view owned) key.arguments ∧
      (view owned).length * 4 < Compiler.ZigAir.Memory.addressLimit := by
  have contents : Represents before.memory.memory (view owned) key.arguments := by
    rw [aligned]; exact (custody.toCustody.good facts.valid before.graph).2
  have bounded : (view owned).length * 4 < Compiler.ZigAir.Memory.addressLimit := by
    by_cases empty : owned.items = []
    · simp [view, empty, Compiler.ZigAir.Memory.addressLimit]
    · obtain ⟨⟨cell, found, typed, writable, _⟩, _⟩ := facts.valid.related allocator owned.address owned.items empty
        (custody.live.resolve_left empty)
      exact ArgumentScan.byte_length_bound before.memory.memory (view owned) facts.valid.memory
        ⟨owned.items.length, cell, found, typed, writable, by simp [view]⟩
  exact ⟨contents, bounded⟩

/-- Original caller custody supplies the query's actual words and byte extent.
The table supplies the stored candidate and ID; neither a correct equality
callback nor a selected logical entry is an input. -/
theorem Facts.lookup_candidate {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (place : Initialization.Placement) (receiver : Nat) (bucketCapacity : BitVec 32) (bucket index remaining : Nat)
    (binding : Table.Binding place safety receiver bucket bucketCapacity before.memory.memory before.memory.effects.keys)
    (inside : index < bucketCapacity.toNat) (fp : BitVec 7) (key : Key) (owned : ArgumentSlice)
    (aligned : key.arguments = owned.items) (custody : Caller.GraphCustody allocator owned rows before.memory) :
    ∃ bits result, Buckets.Metadata.readByte before.memory.memory bucket index = .ok bits ∧
      Candidate.run before.memory.memory bucketCapacity bucket index remaining fp key (view owned) = .ok result ∧
      Candidate.Correct before.memory.memory bucketCapacity bucket index remaining fp key before.memory.effects.keys bits result := by
  obtain ⟨contents, bounded⟩ := facts.query_view key owned aligned custody
  exact Candidate.run_verified before.memory.memory bucketCapacity bucket index remaining fp key (view owned)
    before.memory.effects.keys binding inside contents bounded

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
