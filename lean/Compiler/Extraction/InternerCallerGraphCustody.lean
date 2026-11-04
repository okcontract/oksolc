/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerCustody

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- A caller's private normalized owner can be released without retiring a key
or a representative operand. This is a live-frame invariant, not permission to
free: consumption still requires the actual caller's ownership provenance. -/
structure GraphCustody (allocator : Nat) (slice : ArgumentSlice) (rows : List Storage.Cell)
    (memory : Session (Publication.Effects σ)) : Prop extends Custody allocator slice memory where
  operands : slice.items ≠ [] → ∀ row ∈ rows, row.arguments ≠ [] → slice.address ≠ row.argumentsAddress

/-- Original constructor input may be an unregistered stack view. Its privacy
is needed for any key a recursive child may replace, not just the entry lookup. -/
def SourcePrivate (source : View) (keys : OwnedKeys.Table) : Prop :=
  ∀ key old, keys key = some old → key.arguments ≠ [] →
    source.length ≠ 0 → source.allocation ≠ old.address

/-- The new owner is separated by original source liveness, while retained
keys use privacy in the reached table. No entry/reached table equality is needed. -/
theorem Origin.source_private_after_publication
    {allocator : Nat} {source : View} {request : Interner.Request} {values : List NodeId}
    {before : World (Publication.Effects σ)} {taken : State (Publication.Effects σ)}
    {owned : ArgumentSlice} {lookup : Handle} {current keys : OwnedKeys.Table} {key : Key} {id : NodeId}
    (origin : Origin allocator source request values before taken owned lookup)
    (parent : View) (items : List NodeId) (good : Good parent items before)
    (privateSource : SourcePrivate parent current)
    (published : keys = OwnedKeys.store current key ⟨owned.address, id⟩) :
    SourcePrivate parent keys := by
  intro query old found nonempty length
  rw [published, OwnedKeys.store] at found
  split at found
  · cases Option.some.inj found
    obtain ⟨cell, backed⟩ := good.backed length
    exact (origin.freshNative parent.allocation cell backed).symm
  · exact privateSource query old found nonempty length

/-- Derive publication admission from the reached parent frame and key owners.
The selected key may have been installed or replaced by a recursive child. -/
theorem GraphCustody.publication {allocator : Nat} {owned : ArgumentSlice} {rows : List Storage.Cell}
    {world : World (Publication.Effects σ)} (custody : GraphCustody allocator owned rows world.memory)
    (source : View) (key : Key) (aligned : key.arguments = owned.items)
    (privateSource : SourcePrivate source world.memory.effects.keys)
    (live : OwnedKeys.Live allocator ⟨world.memory.effects.keys, world.memory.heap⟩) :
    Publication.Input allocator source key owned world := by
  refine ⟨aligned, live key, ?_, privateSource key⟩
  intro old found nonempty alias
  exact custody.apart key old found nonempty ⟨by simpa only [← aligned] using nonempty, alias.symm⟩

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

variable {σ : Type} {allocator : Nat} {source : View} {itemSource : Compiler.ZigAir.Memory.Address}
  {request : Interner.Request} {values : List NodeId} {input : AssemblyClone.NativeFields.ItemValue}
  {key : Key} {before : World (Publication.Effects σ)} {taken : OwnedCall.State (Publication.Effects σ)}
  {normalized : ArgumentSlice} {lookup : Handle}

/-- Normalization/take produces the private frame from the existing resident
graph. No separation at the reached world is assumed. -/
theorem CallerInput.graph_custody
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (rows : List Storage.Cell) (resident : Memory.GraphResident allocator before.memory.heap rows) :
    Caller.GraphCustody allocator normalized rows taken.world.memory := by
  refine ⟨entry.custody, ?_⟩
  intro _ row member nonempty
  exact entry.origin.fresh _ _ ((resident row member).2.resolve_left nonempty)

/-- The actual child's fresh duplicate is apart from every live parent owner,
including equal-content buffers. Key retirement uses the same native growth
frame; operand separation uses the duplicate's derived allocation identity. -/
theorem CallerInput.graph_custody_after_growth
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (parent : ArgumentSlice) (rows : List Storage.Cell)
    (custody : Caller.GraphCustody allocator parent rows before.memory)
    (oldLifetime : Nat) (row : Storage.Cell) (after : Session (Publication.Effects σ)) (id : NodeId)
    (vector : Memory.Vector allocator before.memory.heap oldLifetime rows)
    (fresh : row.argumentsAddress = taken.world.memory.memory.nextId)
    (registry : ∀ address block, before.memory.heap address = some block → address ≠ oldLifetime →
      (∀ old, before.memory.effects.keys key = some old → key.arguments ≠ [] → address ≠ old.address) →
      after.heap address = some block)
    (keys : after.effects.keys = OwnedKeys.store before.memory.effects.keys key ⟨normalized.address, id⟩) :
    Caller.GraphCustody allocator parent (rows ++ [row]) after := by
  refine ⟨entry.custody_after_growth parent custody.toCustody oldLifetime rows after id vector registry keys, ?_⟩
  intro nonempty logical member arguments
  rcases List.mem_append.mp member with old | added
  · exact custody.operands nonempty logical old arguments
  · have same := List.mem_singleton.mp added
    subst logical
    have registered := entry.origin.registry _ _ (custody.live.resolve_left nonempty)
    obtain ⟨native, found, _⟩ := entry.origin.held.1.1.injected _ _ registered
    rw [fresh]
    exact Nat.ne_of_lt (Compiler.ZigAir.Memory.valid_lookup _ _ native entry.origin.held.1.1.memory found).1

/-- The child's actual normalization is fresh from every readable parent
source, including stack arrays absent from the allocation registry. Retained
keys use the original privacy fact; the new key uses native freshness. -/
theorem CallerInput.source_private_after_publication
    (entry : CallerInput allocator source itemSource request values input key before taken normalized lookup)
    (parent : View) (items : List NodeId) (good : Good parent items before)
    (privateSource : Caller.SourcePrivate parent before.memory.effects.keys)
    (keys : OwnedKeys.Table) (id : NodeId)
    (published : keys = OwnedKeys.store before.memory.effects.keys key ⟨normalized.address, id⟩) :
    Caller.SourcePrivate parent keys := by
  exact entry.origin.source_private_after_publication parent items good privateSource published

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
