/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.Memory
import Compiler.ZigAir.MemoryRelease
import Compiler.ZigAir.MemoryWordArrayWrites

/-! A relation between existing logical argument allocations and typed storage.
No new heap or allocation registry is introduced. IDs on both sides denote the
same lifetime; establishing that correspondence for native allocations remains
an external obligation. Item and representative blocks are outside this relation.
-/
namespace Compiler.Extraction.Memory.Arguments
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

def view (slice : ArgumentSlice) : View := ⟨slice.address, 0, slice.items.length⟩

/-- A complete mutable allocation, not a borrowed sub-slice or stack buffer.
Contents are separate: uninitialized storage may still be released. -/
def Owned (state : Compiler.ZigAir.Memory.State) (id length : Nat) : Prop :=
  ∃ cell, state.heap.lookup id = some cell ∧ cell.type = .array length word ∧
    cell.writable = true ∧ cell.stack = false

/-- Initialized nonempty logical arguments have their exact typed contents.
An empty slice needs no live sentinel; other logical block kinds are not covered. -/
def Related (heap : Heap) (state : Compiler.ZigAir.Memory.State) : Prop :=
  ∀ allocator id items, items ≠ [] → heap id = some ⟨allocator, .arguments items⟩ →
    Owned state id items.length ∧ Represents state (view ⟨id, items⟩) items

inductive ReleaseFault where
  | ownership (fault : Fault)
  | memory (fault : Compiler.ZigAir.Memory.Fault)
  deriving DecidableEq, Repr

/-- Checked implementation of the release contract, not captured allocator AIR.
The original ownership operation checks allocator pairing. Nonempty releases
also check the complete typed extent and reject stack/readonly storage. Failure
has no committed effect; an empty release does not inspect the sentinel or heap. -/
def release (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat) (slice : ArgumentSlice) :
    Except ReleaseFault (Heap × Compiler.ZigAir.Memory.State) := do
  if slice.items.isEmpty then .ok (heap, state) else
  let after ← (releaseSlice heap allocator slice).mapError ReleaseFault.ownership
  let memory ← (Compiler.ZigAir.Memory.releaseOwned state slice.address
    (.array slice.items.length word)).mapError ReleaseFault.memory
  .ok (after, memory)

end Compiler.Extraction.Memory.Arguments
