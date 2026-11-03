/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerGraphCustody

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Reached custody protects the normalized owner from all old operands and
keys. The actual fresh duplicate extends that separation to the appended row,
without reconstructing an earlier normalization origin. -/
theorem extended_arguments_apart (allocator : Nat) (world : World (Publication.Effects σ))
    (normalized operands : ArgumentSlice) (key : Key) (cells : List Storage.Cell) (row : Storage.Cell)
    (valid : Valid world.memory) (live : OwnedKeys.Live allocator ⟨world.memory.effects.keys, world.memory.heap⟩)
    (custody : Caller.GraphCustody allocator normalized cells world.memory)
    (aligned : key.arguments = normalized.items)
    (keyApart : OwnedKeys.Apart world.memory.effects.keys
      (fun address => ∃ cell ∈ cells, cell.arguments ≠ [] ∧ address = cell.argumentsAddress))
    (arguments : row.arguments = operands.items) (address : row.argumentsAddress = operands.address)
    (fresh : operands.address = world.memory.memory.nextId)
    (separate : operands.items ≠ [] → normalized.items ≠ [] → normalized.address ≠ operands.address) :
    OwnedKeys.Apart world.memory.effects.keys
      (fun location => ∃ cell ∈ cells ++ [row], cell.arguments ≠ [] ∧ location = cell.argumentsAddress) ∧
    (key.arguments ≠ [] → ¬ (∃ cell ∈ cells ++ [row], cell.arguments ≠ [] ∧ normalized.address = cell.argumentsAddress)) := by
  constructor
  · intro query old found nonempty kept
    obtain ⟨logical, member, nonemptyArguments, aliases⟩ := kept
    rcases List.mem_append.mp member with previous | added
    · exact keyApart query old found nonempty ⟨logical, previous, nonemptyArguments, aliases⟩
    · have same := List.mem_singleton.mp added
      subst logical
      obtain ⟨native, found, _⟩ := valid.injected old.address _ ((live query old found).resolve_left nonempty)
      have older := (Compiler.ZigAir.Memory.valid_lookup _ _ native valid.memory found).1
      rw [address, fresh] at aliases
      exact (Nat.ne_of_lt older) aliases
  · intro nonempty kept
    obtain ⟨logical, member, nonemptyArguments, aliases⟩ := kept
    have normalizedNonempty : normalized.items ≠ [] := by simpa only [aligned] using nonempty
    rcases List.mem_append.mp member with previous | added
    · exact custody.operands normalizedNonempty logical previous nonemptyArguments aliases
    · have same := List.mem_singleton.mp added
      subst logical
      rw [arguments] at nonemptyArguments
      exact separate nonemptyArguments normalizedNonempty (address ▸ aliases)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion.Native
