/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.OwnedKeysPhysicalFrame

namespace Compiler.Extraction.OwnedKeys.Physical
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments

/-- Registry kinds separate items, byte payloads and representative backing
from the argument buffer retired by successful key replacement. -/
theorem Completed.non_arguments_frame (external : Normalization.External σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before after : State σ)
    (completed : Completed external key incoming before after)
    (live : ∀ old, before.table key = some old → Memory.SliceValid allocator before.memory.heap (slice key old))
    (address : Nat) (allocation : Memory.Allocation)
    (stored : before.memory.heap address = some allocation)
    (different : allocation.block ≠ .arguments key.arguments) :
    after.memory.heap address = before.memory.heap address ∧
      after.memory.memory.heap.lookup address = before.memory.memory.heap.lookup address := by
  have apart (old : Entry) (found : before.table key = some old) (nonempty : key.arguments ≠ []) : address ≠ old.address := by
    have owned := (live old found).resolve_left nonempty
    change before.memory.heap old.address = some ⟨allocator, .arguments key.arguments⟩ at owned
    intro same
    rw [← same, stored] at owned
    exact different (congrArg Memory.Allocation.block (Option.some.inj owned))
  exact ⟨completed.registry_frame _ _ _ _ _ address apart, completed.frame address apart⟩

/-- A successful publication preserves every resident representative and its
native item/argument allocation. Only separation of nonempty graph arguments
from owned keys is required; item separation follows from registry kinds.
Empty sentinels may alias the retired key and are never dereferenced here. -/
theorem Completed.graph_resident (external : Normalization.External σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before after : State σ) (cells : List Cell)
    (completed : Completed external key incoming before after)
    (live : ∀ old, before.table key = some old → Memory.SliceValid allocator before.memory.heap (slice key old))
    (resident : Memory.GraphResident allocator before.memory.heap cells)
    (apart : Apart before.table (fun address => ∃ cell ∈ cells, cell.arguments ≠ [] ∧ address = cell.argumentsAddress)) :
    Memory.GraphResident allocator after.memory.heap cells ∧
      (∀ cell ∈ cells,
        after.memory.memory.heap.lookup cell.itemAddress = before.memory.memory.heap.lookup cell.itemAddress ∧
        (cell.arguments ≠ [] → after.memory.memory.heap.lookup cell.argumentsAddress = before.memory.memory.heap.lookup cell.argumentsAddress)) := by
  have itemFrame (cell : Cell) (member : cell ∈ cells) := completed.non_arguments_frame external allocator key incoming before after live
    cell.itemAddress ⟨allocator, .item cell.item⟩ (resident cell member).1 (by intro impossible; cases impossible)
  have argumentApart (cell : Cell) (member : cell ∈ cells) (nonempty : cell.arguments ≠ [])
      (old : Entry) (found : before.table key = some old) (keyNonempty : key.arguments ≠ []) : cell.argumentsAddress ≠ old.address := by
    intro same
    exact apart key old found keyNonempty ⟨cell, member, nonempty, same.symm⟩
  constructor
  · intro cell member
    exact frame_resident allocator before.memory.heap after.memory.heap cell (resident cell member) (by
      intro address kept
      rcases kept with same | ⟨nonempty, same⟩
      · subst address; exact (itemFrame cell member).1
      · subst address
        exact completed.registry_frame _ _ _ _ _ cell.argumentsAddress (argumentApart cell member nonempty))
  · intro cell member
    exact ⟨(itemFrame cell member).2, fun nonempty => completed.frame cell.argumentsAddress (argumentApart cell member nonempty)⟩

end Compiler.Extraction.OwnedKeys.Physical
