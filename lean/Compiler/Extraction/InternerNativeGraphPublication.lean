/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerNativeGraphFrame
import Compiler.Extraction.InternerPublicationSuccess
import Compiler.Extraction.InternerCallerGraphCustody
import Compiler.Extraction.OwnedKeysPhysicalGraph

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- The reached world of successful publication of an absent key. This is an
update of the existing execution state, not a separate cache representation. -/
def freshWorld (key : Key) (owned : ArgumentSlice) (id : NodeId) (effects : σ) (before : World (Effects σ)) : World (Effects σ) :=
  { graph := { before.graph with table := Cache.put equalityFields before.graph.table key id }
    memory := { before.memory with effects := ⟨OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩, effects⟩ } }

/-- Probing an absent key neither releases a previous owner nor mutates native
cells. The exact probe response and descriptor alignment select this branch. -/
theorem publish_absent (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (allocator : Nat)
    (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) (effects : σ) (before : World (Effects σ))
    (aligned : key.arguments = owned.items) (absent : before.memory.effects.keys key = none)
    (response : hostProbe key (forget before.memory) = (true, effects)) :
    publish hostProbe host allocator source key owned id before = (.ok (), freshWorld key owned id effects before) := by
  simp only [publish, admit, aligned, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, absent,
    body, OwnedKeys.Physical.run, OwnedKeys.Code.execute, OwnedKeys.Physical.operations, physical, probe, response,
    OwnedKeys.Code.complete, OwnedKeys.publicationCode, Scalar.run, commit, Except.mapError, freshWorld]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

/-- Reconstruct the native graph after the actual publication completion,
including retirement of an existing key. Resident separation and native types
derive the protected allocation frames; final correspondence is not a premise. -/
theorem Facts.publication_completed {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows) (host : External σ)
    (key : Key) (owned : ArgumentSlice) (id : NodeId) (effects : σ)
    (after : OwnedKeys.Physical.State (Publication.Effects σ))
    (aligned : key.arguments = owned.items)
    (custody : Caller.GraphCustody allocator owned rows before.memory)
    (completed : OwnedKeys.Physical.Completed (Publication.external host) key ⟨owned.address, id⟩
      ⟨before.memory.effects.keys, { before.memory with effects := ⟨before.memory.effects.keys, effects⟩ }⟩ after) :
    Facts safety allocator owner data capacity (Publication.commit key id before (.ok (), after)).2 rows := by
  have fresh : OwnedKeys.Fresh before.memory.effects.keys key ⟨owned.address, id⟩ := by
    intro query old found incoming nonempty alias
    exact custody.apart query old found nonempty ⟨by simpa only [← aligned] using incoming, alias.symm⟩
  have preserved := completed.preserves (Publication.external host) allocator key ⟨owned.address, id⟩ _ after
    (fun address => ∃ row ∈ rows, row.arguments ≠ [] ∧ address = row.argumentsAddress)
    facts.live facts.unique (by simpa only [OwnedKeys.slice, aligned] using custody.live) fresh facts.apart (by
      intro nonempty ⟨row, member, arguments, alias⟩
      exact custody.operands (by simpa only [← aligned] using nonempty) row member arguments alias)
  have resident := completed.graph_resident (Publication.external host) allocator key _ _ after rows
    (facts.live key) facts.resident facts.apart
  obtain ⟨ownerCell, found, typed, writable⟩ := facts.ownerLive
  have ownerApart (old : OwnedKeys.Entry) (present : before.memory.effects.keys key = some old)
      (nonempty : key.arguments ≠ []) : owner ≠ old.address := by
    have stored := (facts.live key old present).resolve_left nonempty
    obtain ⟨⟨native, located, shape, _⟩, _⟩ := facts.valid.related allocator old.address key.arguments nonempty stored
    exact before.memory.memory.heap.lookup_ne_of_type_ne owner old.address ownerCell native found located
      (by simp [typed, shape, Owner.viewType])
  have ownerFrame := completed.frame owner ownerApart
  have header : readHeader after.memory.memory (Owner.headerAddress ⟨owner, 0⟩) =
      .ok (.slice itemsType data rows.length, .scalar (.int false 64 capacity)) := by
    unfold readHeader readItems
    rw [readField_eq_of_lookup _ _ (Owner.headerAddress ⟨owner, 0⟩) itemsOffset ownerFrame,
      readField_eq_of_lookup _ _ (Owner.headerAddress ⟨owner, 0⟩) capacityOffset ownerFrame]
    exact facts.header
  refine ⟨⟨completed.valid.memory, completed.valid.related, completed.valid.injected⟩, facts.projected, ?_,
    ⟨ownerCell, ownerFrame.trans found, typed, writable⟩, header, facts.bounded, ?_, resident.1, ?_,
    preserved.live, preserved.unique, preserved.apart, ?_⟩
  · change Cache.put equalityFields before.graph.table key id = OwnedKeys.view after.table
    have keys : after.table = OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩ :=
      congrArg OwnedKeys.State.table completed.logical
    rw [keys, OwnedKeys.view_store, facts.linked]
  · intro nonempty
    obtain ⟨⟨offset, _, backing, located, shape, writable, persistent⟩, vector, descriptors⟩ := facts.storage nonempty
    have frame := completed.non_arguments_frame (Publication.external host) allocator key _ _ after
      (facts.live key) data.allocation ⟨allocator, .representatives rows⟩ vector (by intro impossible; cases impossible)
    exact ⟨⟨offset, ⟨rows, frame.1.trans vector⟩, backing, frame.2.trans located, shape, writable, persistent⟩,
      frame.1.trans vector, DescriptorRelation.frame _ _ _ rows descriptors frame.2⟩
  · intro row member
    obtain ⟨native, located, shape, query⟩ := facts.items row member
    have frame := (resident.2 row member).1
    exact ⟨native, frame.trans located, shape, AssemblyItem.Query.frame _ _ row frame query⟩
  · intro row member
    exact (facts.data row member).frame (resident.2 row member).1

/-- The reached parent frame admits publication even when a child changed the
selected key. Both probe outcomes retain the native graph and original input;
successful replacement additionally retires exactly the old key owner. -/
theorem Facts.publish {safety : Bool} {allocator owner capacity : Nat}
    {data : Compiler.ZigAir.Memory.Address} {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (source : View) (values : List NodeId)
    (key : Key) (owned : ArgumentSlice) (id : NodeId) (accepted : Bool) (effects : σ)
    (aligned : key.arguments = owned.items) (held : Held allocator source values owned before)
    (custody : Caller.GraphCustody allocator owned rows before.memory)
    (privateSource : Caller.SourcePrivate source before.memory.effects.keys)
    (response : hostProbe key (Publication.forget before.memory) = (accepted, effects)) :
    let ran := Publication.publish hostProbe host allocator source key owned id before
    ran.1 = (if accepted then .ok () else .error (.language .outOfMemory)) ∧
    Facts safety allocator owner data capacity ran.2 rows ∧ Held allocator source values owned ran.2 ∧
    ran.2.memory.effects.keys = (if accepted then OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩
      else before.memory.effects.keys) := by
  have input := custody.publication source key aligned privateSource facts.live
  cases accepted with
  | false =>
    have called := Publication.publish_oom hostProbe host allocator source key owned id before effects
      (Publication.admit_complete _ _ _ _ _ input) response
    simp only [called, Bool.false_eq_true, ↓reduceIte]
    refine ⟨by trivial, ?_, ⟨⟨⟨held.1.1.memory, held.1.1.related, held.1.1.injected⟩, held.1.2⟩, held.2⟩, by trivial⟩
    exact facts.frame ⟨facts.valid.memory, facts.valid.related, facts.valid.injected⟩ facts.projected rfl rfl
      (fun _ _ found _ => found) (fun _ _ found => found)
  | true =>
    obtain ⟨after, called, completed, _⟩ := Publication.publish_success hostProbe host allocator source key owned id before effects
      facts.valid input held.2.1 response
    simp only [called, ↓reduceIte]
    exact ⟨rfl, facts.publication_completed host key owned id effects after aligned custody completed,
      Publication.completion_held host allocator source values key owned id before _ after input held completed,
      congrArg OwnedKeys.State.table completed.logical⟩

/-- Pure publication bookkeeping over the existing world. Native storage
correspondence is established separately; no allocator callback is required for
this absent-key table update. Empty keys do not own their sentinel. -/
theorem Facts.store_absent {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (key : Key) (owned : ArgumentSlice) (id : NodeId) (effects : σ)
    (aligned : key.arguments = owned.items) (absent : before.memory.effects.keys key = none)
    (live : SliceValid allocator before.memory.heap owned)
    (fresh : OwnedKeys.Fresh before.memory.effects.keys key ⟨owned.address, id⟩)
    (apart : owned.items ≠ [] → ∀ row ∈ rows, row.arguments ≠ [] → owned.address ≠ row.argumentsAddress) :
    Facts safety allocator owner data capacity (Publication.freshWorld key owned id effects before) rows := by
  have allLive := OwnedKeys.after_live allocator ⟨before.memory.effects.keys, before.memory.heap⟩ key ⟨owned.address, id⟩
    facts.live facts.unique (by simpa only [OwnedKeys.slice, aligned] using live) fresh
  have allApart := OwnedKeys.store_apart before.memory.effects.keys key ⟨owned.address, id⟩ _ facts.apart (by
    intro keyNonempty kept
    obtain ⟨row, member, nonempty, equal⟩ := kept
    exact apart (by simpa only [← aligned] using keyNonempty) row member nonempty equal)
  refine ⟨⟨facts.valid.memory, facts.valid.related, facts.valid.injected⟩, facts.projected, ?_, facts.ownerLive,
      facts.header, facts.bounded, facts.storage, facts.resident, facts.items, ?_,
      OwnedKeys.store_unique _ _ _ facts.unique fresh, allApart, facts.data⟩
  · change Cache.put equalityFields before.graph.table key id = OwnedKeys.view (OwnedKeys.store before.memory.effects.keys key ⟨owned.address, id⟩)
    rw [OwnedKeys.view_store, facts.linked]
  · simpa only [OwnedKeys.after, OwnedKeys.retire, absent] using allLive


/-- Compose an absent-key publication with native graph correspondence. The
incoming owner and its separation from existing keys and representative operands
must come from the caller/child execution; no reached graph invariant is assumed.
Native hash-table refinement remains outside this theorem. -/
theorem Facts.publish_absent {safety : Bool} {allocator owner capacity : Nat} {data : Compiler.ZigAir.Memory.Address}
    {before : World (Publication.Effects σ)} {rows : List Storage.Cell}
    (facts : Facts safety allocator owner data capacity before rows)
    (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ) (source : View)
    (key : Key) (owned : ArgumentSlice) (id : NodeId) (effects : σ)
    (aligned : key.arguments = owned.items) (absent : before.memory.effects.keys key = none)
    (live : SliceValid allocator before.memory.heap owned)
    (fresh : OwnedKeys.Fresh before.memory.effects.keys key ⟨owned.address, id⟩)
    (apart : ∀ row ∈ rows, row.arguments ≠ [] → owned.address ≠ row.argumentsAddress)
    (response : hostProbe key (Publication.forget before.memory) = (true, effects)) :
    Publication.publish hostProbe host allocator source key owned id before =
      (.ok (), Publication.freshWorld key owned id effects before) ∧
    Facts safety allocator owner data capacity (Publication.freshWorld key owned id effects before) rows := by
  exact ⟨Publication.publish_absent hostProbe host allocator source key owned id effects before aligned absent response,
    facts.store_absent key owned id effects aligned absent live fresh (fun _ => apart)⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.NativeGraph
