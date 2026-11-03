/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublication
import Compiler.Extraction.ExpressionMapEmpty

namespace Compiler.Extraction.OwnedKeys.Physical
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments

/-- With empty key arguments, the current publication interpreter cannot change
typed native memory, regardless of probing, allocator effects or the old entry.
The table itself can change. This describes the existing abstraction, not the
native hash map's bucket or header writes. -/
theorem run_empty_memory (probe : Probe σ) (external : Normalization.External σ)
    (allocator : Nat) (key : Key) (incoming : Entry) (before : State σ)
    (empty : key.arguments = []) :
    (run probe external allocator key incoming before).2.memory.memory = before.memory.memory := by
  cases attempted : probe key before.memory with
  | mk ok effects =>
    cases ok
    · simp [run, Code.execute, operations, attempted]
    · simp only [run, Code.execute, operations, attempted, if_true]
      cases found : before.table key with
      | none => simp [Code.complete, publicationCode, found, Scalar.run]
      | some old =>
        have freed := Normalization.free_empty external allocator (slice key old)
          {before.memory with effects} (by simpa only [slice] using empty)
        simp [Code.complete, publicationCode, found, freed, Scalar.run]

end Compiler.Extraction.OwnedKeys.Physical

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Compiler.ZigAir.Memory.WordArray

/-- The admission check and logical table commit add no native map write.
A native implementation must therefore refine this interpreter through an
explicit memory projection or an interface that retains those writes. -/
theorem empty_memory (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice)
    (id : NodeId) (before : World (Effects σ)) (empty : key.arguments = []) :
    (publish hostProbe host allocator source key owned id before).2.memory.memory = before.memory.memory := by
  cases admitted : admit allocator source key owned before with
  | error reason => simp only [publish, admitted]
  | ok accepted =>
    cases accepted
    simp only [publish, admitted]
    have kept := OwnedKeys.Physical.run_empty_memory (probe hostProbe) (external host) allocator key
      ⟨owned.address, id⟩ (physical before) empty
    unfold body commit
    split <;> exact kept

theorem empty_map_size (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice)
    (id : NodeId) (before : World (Effects σ)) (empty : key.arguments = [])
    (safety : Bool) (owner : Compiler.ZigAir.Memory.Address) :
    ExpressionMap.readSize safety
      (publish hostProbe host allocator source key owned id before).2.memory.memory owner =
      ExpressionMap.readSize safety before.memory.memory owner := by
  rw [empty_memory hostProbe host allocator source key owned id before empty]

/-- A changed native map-size observation rules out attachment by equality of
the entire typed memory. It does not rule out a proved abstraction of private
map storage, and it does not contradict the existing conditional word proofs. -/
theorem changed_map_size_not_identity (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice)
    (id : NodeId) (before : World (Effects σ)) (empty : key.arguments = [])
    (safety : Bool) (owner : Compiler.ZigAir.Memory.Address) (nativeAfter : Compiler.ZigAir.Memory.State)
    (changed : ExpressionMap.readSize safety nativeAfter owner ≠
      ExpressionMap.readSize safety before.memory.memory owner) :
    (publish hostProbe host allocator source key owned id before).2.memory.memory ≠ nativeAfter := by
  intro same
  apply changed
  rw [← same]
  exact empty_map_size hostProbe host allocator source key owned id before empty safety owner

/-- The observed first insertion changes the native count from zero to one.
Only those two field observations are required to exclude memory identity. -/
theorem first_map_entry_not_identity (hostProbe : OwnedKeys.Physical.Probe σ) (host : External σ)
    (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice)
    (id : NodeId) (before : World (Effects σ)) (empty : key.arguments = [])
    (safety : Bool) (owner : Compiler.ZigAir.Memory.Address) (nativeAfter : Compiler.ZigAir.Memory.State)
    (initial : ExpressionMap.readSize safety before.memory.memory owner = .ok (.scalar (.int false 32 0)))
    (inserted : ExpressionMap.readSize safety nativeAfter owner = .ok (.scalar (.int false 32 1))) :
    (publish hostProbe host allocator source key owned id before).2.memory.memory ≠ nativeAfter := by
  apply changed_map_size_not_identity hostProbe host allocator source key owned id before empty safety owner nativeAfter
  rw [initial, inserted]
  intro impossible
  simp at impossible

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
