/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemoryAllocation
import Compiler.ZigAir.MemoryWordCopy

namespace Compiler.Extraction.Memory.Arguments.Duplication
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory
open Compiler.ZigAir.Memory.WordArray

/-- Checked allocation/copy composition for a borrowed source. `items` is its
logical descriptor; inconsistent lengths reject before requesting storage.
Allocation's provisional payload becomes observable only after successful copy.
Every failure retains the reached heap and private allocator effects, including
partial copy writes. This uses the external allocation and typed memcpy
contracts, not captured allocator/dupe AIR or a verified native allocator. -/
def run (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : WordAllocation.Allocator σ) (effects : σ) :
    (Except Allocation.Fault (Option ArgumentSlice) × Heap × Compiler.ZigAir.Memory.State) × σ :=
  if source.length ≠ items.length then ((.error (.memory .sourceBounds), heap, state), effects) else
  let ((result, registered, allocated), reached) := Allocation.reserve heap state allocator items request effects
  match result with
  | .error fault => ((.error fault, registered, allocated), reached)
  | .ok none => ((.ok none, registered, allocated), reached)
  | .ok (some destination) =>
    let (copied, after) := WordCopy.copy allocated source (view destination)
    match copied with
    | .error fault => ((.error (.memory fault), registered, after), reached)
    | .ok () => ((.ok (some destination), registered, after), reached)

/-- Exact duplicate contents and independent ownership, together with the
original source, registry frame and allocation history. Empty duplicates need
no live backing storage and do not change either heap. -/
structure Post (heap : Heap) (before : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (sourceView : View) (items : List NodeId) (slice : ArgumentSlice)
    (registered : Heap) (after : Compiler.ZigAir.Memory.State) : Prop where
  descriptor : slice = ⟨before.nextId, items⟩
  valid : after.valid = true
  related : Related registered after
  copied : Represents after (view slice) items
  source : Represents after sourceView items
  live : SliceValid allocator registered slice
  registration : registered = if items.isEmpty then heap else write heap before.nextId (some ⟨allocator, .arguments items⟩)
  empty : items = [] → after = before
  fresh : items ≠ [] → heap before.nextId = none
  separate : items ≠ [] → sourceView.allocation ≠ slice.address
  owned : items ≠ [] → Owned after slice.address items.length
  frame : ∀ id, id ≠ before.nextId → after.heap.lookup id = before.heap.lookup id
  nextId : after.nextId = before.nextId + if items.isEmpty then 0 else 1
  nextAddress : before.nextAddress ≤ after.nextAddress

end Compiler.Extraction.Memory.Arguments.Duplication
