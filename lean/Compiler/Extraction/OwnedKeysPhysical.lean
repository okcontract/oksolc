/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.OwnedKeysProofs
import Compiler.Extraction.NormalizationMemoryContracts

namespace Compiler.Extraction.OwnedKeys.Physical
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments
open Compiler.ZigAir.Memory.WordArray

/-- Reuses the owned-key table and normalization's single memory registry.
The cache-ID projection is `OwnedKeys.view`; no second cache is maintained. -/
structure State (σ : Type) where
  table : Table
  memory : Normalization.Session σ

def State.logical (state : State σ) : OwnedKeys.State := ⟨state.table, state.memory.heap⟩

/-- Bucket allocation/probing remains an implementation-refinement obligation:
it may inspect the reached session and change private allocator effects, but
must frame existing entries and registered allocations. This is not a new host
assumption or a proof of the native hash map. -/
abbrev Probe (σ : Type) := Key → Normalization.Session σ → Bool × σ

def operations (probe : Probe σ) (external : Normalization.External σ) (allocator : Nat) :
    Operations (State σ) Normalization.Failure where
  getOrPut key before :=
    let (ok, effects) := probe key before.memory
    (ok, { before with memory := { before.memory with effects } })
  lookup key before := before.table key
  release owned before :=
    let (result, memory) := Normalization.free external allocator owned before.memory
    (result, { before with memory })
  write key entry before := { before with table := store before.table key entry }
  outOfMemory := .outOfMemory

def run (probe : Probe σ) (external : Normalization.External σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before : State σ) : Except Normalization.Failure Unit × State σ :=
  publicationCode.execute (operations probe external allocator) key incoming before

/-- Exact publication result, including typed lifetime death, all other cells,
allocation history, and the reached private state observed by native free. -/
structure Completed (external : Normalization.External σ) (key : Key) (incoming : Entry)
    (before after : State σ) : Prop where
  logical : after.logical = OwnedKeys.after before.logical key incoming
  valid : Normalization.Valid after.memory
  nextId : after.memory.memory.nextId = before.memory.memory.nextId
  nextAddress : after.memory.memory.nextAddress = before.memory.memory.nextAddress
  frame : ∀ id, (∀ old, before.table key = some old → key.arguments ≠ [] → id ≠ old.address) →
    after.memory.memory.heap.lookup id = before.memory.memory.heap.lookup id
  dead : ∀ old, before.table key = some old → key.arguments ≠ [] →
    after.memory.memory.heap.lookup old.address = none
  effects : after.memory.effects = match before.table key with
    | none => before.memory.effects
    | some old => if key.arguments.isEmpty then before.memory.effects
        else external.free (slice key old) before.memory

theorem complete_local_verified (probe : Probe σ) (external : Normalization.External σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before : State σ)
    (valid : Normalization.Valid before.memory)
    (live : ∀ old, before.table key = some old → Memory.SliceValid allocator before.memory.heap (slice key old)) :
    ∃ after, publicationCode.complete (operations probe external allocator) key incoming before = (.ok (), after) ∧
      Completed external key incoming before after := by
  cases found : before.table key with
  | none =>
    refine ⟨⟨store before.table key incoming, before.memory⟩, ?_, ?_⟩
    · simp [Code.complete, operations, publicationCode, found, Scalar.run]
    · exact ⟨by simp [State.logical, OwnedKeys.after, retire, found], valid, rfl, rfl,
        fun _ _ => rfl, fun _ impossible _ => by simp [found] at impossible, by simp [found]⟩
  | some old =>
    have owned := live old found
    by_cases empty : key.arguments = []
    · refine ⟨⟨store before.table key incoming, before.memory⟩, ?_, ?_⟩
      · simp [Code.complete, operations, publicationCode, found, Normalization.free, release, slice, empty, Scalar.run]
      · exact ⟨by simp [State.logical, OwnedKeys.after, retire, found, empty], valid, rfl, rfl,
          fun _ _ => rfl, fun _ _ nonempty => False.elim (nonempty empty), by simp [found, empty]⟩
    · obtain ⟨memory, freed, safe, post, effects⟩ := Normalization.free_valid external allocator (slice key old) before.memory valid owned
      have retired : memory.heap = retire before.logical key := by
        have released := post.logical
        have stored := owned.resolve_left empty
        change before.memory.heap old.address = some ⟨allocator, .arguments key.arguments⟩ at stored
        simpa [Memory.releaseSlice, Memory.release, slice, empty, stored, retire, State.logical, found] using released.symm
      refine ⟨⟨store before.table key incoming, memory⟩, ?_, ?_⟩
      · simp [Code.complete, operations, publicationCode, found, freed, Scalar.run]
      · refine ⟨?_, safe, post.nextId, post.nextAddress, ?_, ?_, ?_⟩
        · simp [State.logical, OwnedKeys.after, retired]
        · intro id apart
          exact (post.frame id (apart old found empty)).2
        · intro other present nonempty
          have same : other = old := Option.some.inj (present.symm.trans found)
          subst other
          exact (post.dead nonempty).2
        · simpa [found, slice] using effects

theorem complete_verified (probe : Probe σ) (external : Normalization.External σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before : State σ)
    (valid : Normalization.Valid before.memory) (live : Live allocator before.logical) :
    ∃ after, publicationCode.complete (operations probe external allocator) key incoming before = (.ok (), after) ∧
      Completed external key incoming before after :=
  complete_local_verified probe external allocator key incoming before valid (live key)

/-- Complete source-bound publication, including OOM before release. The
success theorem starts after probing, so free observes its actual effects. -/
theorem run_local_spec (probe : Probe σ) (external : Normalization.External σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before : State σ)
    (valid : Normalization.Valid before.memory)
    (live : ∀ old, before.table key = some old → Memory.SliceValid allocator before.memory.heap (slice key old)) :
    let attempted := probe key before.memory
    let reached := { before with memory := { before.memory with effects := attempted.2 } }
    if attempted.1 then
      ∃ after, run probe external allocator key incoming before = (.ok (), after) ∧
        Completed external key incoming reached after
    else run probe external allocator key incoming before = (.error .outOfMemory, reached) := by
  cases called : probe key before.memory with
  | mk ok effects =>
    cases ok with
    | false => simp [run, Code.execute, operations, called]
    | true =>
      simpa [run, Code.execute, operations, called] using
        complete_local_verified probe external allocator key incoming
          { before with memory := { before.memory with effects } } ⟨valid.memory, valid.related, valid.injected⟩ live

theorem run_spec (probe : Probe σ) (external : Normalization.External σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before : State σ)
    (valid : Normalization.Valid before.memory) (live : Live allocator before.logical) :
    let attempted := probe key before.memory
    let reached := { before with memory := { before.memory with effects := attempted.2 } }
    if attempted.1 then
      ∃ after, run probe external allocator key incoming before = (.ok (), after) ∧
        Completed external key incoming reached after
    else run probe external allocator key incoming before = (.error .outOfMemory, reached) :=
  run_local_spec probe external allocator key incoming before valid (live key)

/-- The publication obligation needed by an owning caller. Borrowed and graph
allocations are framed at both heap levels, including their typed contents. -/
structure Preserved (allocator : Nat) (kept : Nat → Prop) (owned : ArgumentSlice)
    (before after : State σ) : Prop where
  valid : Normalization.Valid after.memory
  live : Live allocator after.logical
  unique : Unique after.table
  apart : Apart after.table kept
  frame : Frame kept before.memory.heap after.memory.heap
  typedFrame : ∀ id, kept id → after.memory.memory.heap.lookup id = before.memory.memory.heap.lookup id
  nextId : after.memory.memory.nextId = before.memory.memory.nextId
  nextAddress : after.memory.memory.nextAddress = before.memory.memory.nextAddress
  incoming : Memory.SliceValid allocator after.memory.heap owned

theorem Completed.preserves (external : Normalization.External σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before after : State σ) (kept : Nat → Prop)
    (completed : Completed external key incoming before after)
    (live : Live allocator before.logical) (unique : Unique before.table)
    (owned : Memory.SliceValid allocator before.memory.heap (slice key incoming))
    (fresh : Fresh before.table key incoming) (apart : Apart before.table kept)
    (incomingApart : key.arguments ≠ [] → ¬ kept incoming.address) :
    Preserved allocator kept (slice key incoming) before after := by
  have table : after.table = store before.table key incoming := congrArg OwnedKeys.State.table completed.logical
  have heap : after.memory.heap = retire before.logical key := congrArg OwnedKeys.State.memory completed.logical
  refine ⟨completed.valid, ?_, ?_, ?_, ?_, ?_, completed.nextId, completed.nextAddress, ?_⟩
  · rw [completed.logical]
    exact after_live allocator before.logical key incoming live unique owned fresh
  · rw [table]; exact store_unique before.table key incoming unique fresh
  · rw [table]; exact store_apart before.table key incoming kept apart incomingApart
  · rw [heap]; exact after_frame before.logical key incoming kept apart
  · intro id keep
    exact completed.frame id (fun old found nonempty same => apart key old found nonempty (same ▸ keep))
  · rw [heap]
    exact retire_slice allocator before.logical key (slice key incoming) owned
      (fun old found nonempty _ => fresh key old found nonempty nonempty)

theorem run_preserves (probe : Probe σ) (external : Normalization.External σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before : State σ) (kept : Nat → Prop)
    (valid : Normalization.Valid before.memory) (live : Live allocator before.logical)
    (unique : Unique before.table) (owned : Memory.SliceValid allocator before.memory.heap (slice key incoming))
    (fresh : Fresh before.table key incoming) (apart : Apart before.table kept)
    (incomingApart : key.arguments ≠ [] → ¬ kept incoming.address) :
    Preserved allocator kept (slice key incoming) before (run probe external allocator key incoming before).2 := by
  have checked := run_spec probe external allocator key incoming before valid live
  cases called : probe key before.memory with
  | mk ok effects =>
    cases ok with
    | false =>
      simp only [called, Bool.false_eq_true, ↓reduceIte] at checked
      rw [checked]
      exact ⟨⟨valid.memory, valid.related, valid.injected⟩, live, unique, apart,
        fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, owned⟩
    | true =>
      simp only [called, ↓reduceIte] at checked
      obtain ⟨after, executed, completed⟩ := checked
      rw [executed]
      have post := completed.preserves external allocator key incoming _ after kept live unique owned fresh apart incomingApart
      exact ⟨post.valid, post.live, post.unique, post.apart, post.frame, post.typedFrame,
        post.nextId, post.nextAddress, post.incoming⟩

theorem run_semantics (probe : Probe σ) (external : Normalization.External σ) (allocator : Nat)
    (key : Key) (incoming : Entry) (before : State σ)
    (valid : Normalization.Valid before.memory) (live : Live allocator before.logical)
    (meaning : Meaning) (read : Read) (value : Contract.Yul.Word)
    (cache : Cache.Valid meaning read (view before.table))
    (denotation : key.eval meaning read = some value) (actual : read incoming.id = some value) :
    Cache.Valid meaning read (view (run probe external allocator key incoming before).2.table) := by
  have checked := run_spec probe external allocator key incoming before valid live
  cases called : probe key before.memory with
  | mk ok effects =>
    cases ok with
    | false =>
      simp only [called, Bool.false_eq_true, ↓reduceIte] at checked
      rw [checked]; exact cache
    | true =>
      simp only [called, ↓reduceIte] at checked
      obtain ⟨after, executed, completed⟩ := checked
      rw [executed]
      change Cache.Valid meaning read (view after.logical.table)
      rw [completed.logical]
      exact after_semantics meaning read before.logical key incoming value cache denotation actual

end Compiler.Extraction.OwnedKeys.Physical
