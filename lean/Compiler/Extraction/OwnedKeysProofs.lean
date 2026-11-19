/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.OwnedKeysProgram
import Compiler.Extraction.MemoryProofs
import Compiler.Extraction.CacheProofs

namespace Compiler.Extraction.OwnedKeys
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Storage Contract.Yul

theorem view_store (table : Table) (key : Key) (incoming : Entry) :
    view (store table key incoming) = Cache.put equalityFields (view table) key incoming.id := by
  funext query
  by_cases same : query = key
  · subst query
    simp [view, store, Cache.put, (equality_iff key key).mpr rfl]
  · have different : equal equalityFields query key = false :=
      Bool.eq_false_iff.mpr (fun equal => same ((equality_iff query key).mp equal))
    simp [view, store, Cache.put, same, different]

theorem run_failure (getOrPut : Key → σ → Bool × σ) (onFree : ArgumentSlice → σ → σ)
    (allocator : Nat) (key : Key) (incoming : Entry) (before : State) (effects next : σ)
    (failed : getOrPut key effects = (false, next)) :
    publicationCode.run getOrPut onFree allocator key incoming before effects =
      ((.error .outOfMemory, before), next) := by simp [Code.run_equation, failed]

theorem finish_eq (onFree : ArgumentSlice → σ → σ) (allocator : Nat) (key : Key)
    (incoming : Entry) (before : State) (effects : σ) (live : Live allocator before) :
    publicationCode.finish onFree allocator key incoming before effects =
      ((.ok (), after before key incoming), freeEffects before.table key onFree effects) := by
  cases found : before.table key with
  | none => simp [Code.finish_equation, publicationCode, found, after, retire, freeEffects, Scalar.run]
  | some old =>
    have valid := live key old found
    by_cases empty : key.arguments = []
    · simp [Code.finish_equation, publicationCode, found, after, retire, freeEffects, Scalar.run,
        Memory.releaseSlice, slice, empty]
    · have stored : before.memory old.address = some ⟨allocator, .arguments key.arguments⟩ :=
        valid.resolve_left empty
      simp [Code.finish_equation, publicationCode, found, after, retire, freeEffects, Scalar.run,
        Memory.releaseSlice, Memory.release, slice, empty, stored, List.isEmpty_iff]

theorem run_success (getOrPut : Key → σ → Bool × σ) (onFree : ArgumentSlice → σ → σ)
    (allocator : Nat) (key : Key) (incoming : Entry) (before : State) (effects next : σ)
    (succeeded : getOrPut key effects = (true, next)) (live : Live allocator before) :
    publicationCode.run getOrPut onFree allocator key incoming before effects =
      ((.ok (), after before key incoming), freeEffects before.table key onFree next) := by
  simp only [Code.run_equation, succeeded, ↓reduceIte]
  exact finish_eq onFree allocator key incoming before next live

/-- A free can affect only the replaced nonempty key's allocation lifetime. -/
theorem retire_frame (before : State) (key : Key) (address : Nat)
    (apart : ∀ old, before.table key = some old → key.arguments ≠ [] → address ≠ old.address) :
    retire before key address = before.memory address := by
  cases found : before.table key with
  | none => simp [retire, found]
  | some old =>
    by_cases empty : key.arguments = []
    · simp [retire, found, empty]
    · simp [retire, found, empty, Memory.write, apart old found empty]

theorem retire_slice (allocator : Nat) (before : State) (key : Key) (borrow : ArgumentSlice)
    (valid : Memory.SliceValid allocator before.memory borrow)
    (apart : ∀ old, before.table key = some old → key.arguments ≠ [] →
      borrow.items ≠ [] → borrow.address ≠ old.address) :
    Memory.SliceValid allocator (retire before key) borrow := by
  by_cases empty : borrow.items = []
  · exact Or.inl empty
  · right
    rw [retire_frame before key borrow.address (fun old found nonempty => apart old found nonempty empty)]
    exact valid.resolve_left empty

theorem replaced_released (before : State) (key : Key) (incoming old : Entry)
    (found : before.table key = some old) (nonempty : key.arguments ≠ []) :
    (after before key incoming).memory old.address = none := by
  simp [after, retire, found, nonempty, Memory.write]

theorem after_live (allocator : Nat) (before : State) (key : Key) (incoming : Entry)
    (live : Live allocator before) (unique : Unique before.table)
    (valid : Memory.SliceValid allocator before.memory (slice key incoming))
    (fresh : Fresh before.table key incoming) : Live allocator (after before key incoming) := by
  intro query entry found
  by_cases same : query = key
  · subst query
    have equal : incoming = entry := by simpa [after, store] using found
    subst entry
    exact retire_slice allocator before key (slice key incoming) valid
      (fun old stored nonempty _ => fresh key old stored nonempty nonempty)
  · have stored : before.table query = some entry := by simpa [after, store, same] using found
    exact retire_slice allocator before key (slice query entry) (live query entry stored)
      (fun old oldStored keyNonempty queryNonempty =>
        unique query entry key old stored oldStored same queryNonempty keyNonempty)

theorem store_unique (table : Table) (key : Key) (incoming : Entry)
    (unique : Unique table) (fresh : Fresh table key incoming) : Unique (store table key incoming) := by
  intro a x b y ax by_ different aNonempty bNonempty
  by_cases aKey : a = key
  · subst a
    have eqx : incoming = x := by simpa [store] using ax
    subst x
    have bKey : b ≠ key := Ne.symm different
    have old : table b = some y := by simpa [store, bKey] using by_
    exact fresh b y old aNonempty bNonempty
  · have oldA : table a = some x := by simpa [store, aKey] using ax
    by_cases bKey : b = key
    · subst b
      have eqy : incoming = y := by simpa [store] using by_
      subst y
      exact Ne.symm (fresh a x oldA bNonempty aNonempty)
    · have oldB : table b = some y := by simpa [store, bKey] using by_
      exact unique a x b y oldA oldB different aNonempty bNonempty

theorem store_apart (table : Table) (key : Key) (incoming : Entry) (kept : Nat → Prop)
    (apart : Apart table kept) (incomingApart : key.arguments ≠ [] → ¬ kept incoming.address) :
    Apart (store table key incoming) kept := by
  intro query entry found nonempty
  by_cases same : query = key
  · subst query
    have equal : incoming = entry := by simpa [store] using found
    subst entry
    exact incomingApart nonempty
  · exact apart query entry (by simpa [store, same] using found) nonempty

theorem after_frame (before : State) (key : Key) (incoming : Entry) (kept : Nat → Prop)
    (apart : Apart before.table kept) : Frame kept before.memory (after before key incoming).memory := by
  intro address keep
  exact retire_frame before key address (fun old found nonempty same =>
    apart key old found nonempty (same ▸ keep))

theorem frame_resident (allocator : Nat) (before current : Memory.Heap) (cell : Cell)
    (resident : Memory.Resident allocator before cell)
    (framed : Frame (fun address => address = cell.itemAddress ∨
      (cell.arguments ≠ [] ∧ address = cell.argumentsAddress)) before current) :
    Memory.Resident allocator current cell := by
  constructor
  · rw [framed cell.itemAddress (Or.inl rfl)]
    exact resident.1
  · by_cases empty : cell.arguments = []
    · exact Or.inl empty
    · right
      change current cell.argumentsAddress = some ⟨allocator, .arguments cell.arguments⟩
      rw [framed cell.argumentsAddress (Or.inr ⟨empty, rfl⟩)]
      exact resident.2.resolve_left empty

theorem after_semantics (meaning : Meaning) (read : Read) (before : State) (key : Key)
    (incoming : Entry) (value : Word) (valid : Valid meaning read (view before.table))
    (denotation : key.eval meaning read = some value) (actual : read incoming.id = some value) :
    Valid meaning read (view (after before key incoming).table) := by
  rw [show (after before key incoming).table = store before.table key incoming from rfl, view_store]
  exact put_valid meaning read (view before.table) valid key incoming.id value denotation actual

/-- Complete logical ownership contract for the source-bound helper, for every
private allocator state and both getOrPut outcomes. No native memory fault is
reachable under these premises; a failed getOrPut retains caller ownership. -/
theorem run_preserves (getOrPut : Key → σ → Bool × σ) (onFree : ArgumentSlice → σ → σ)
    (allocator : Nat) (key : Key) (incoming : Entry) (before : State) (effects : σ)
    (kept : Nat → Prop) (live : Live allocator before) (unique : Unique before.table)
    (valid : Memory.SliceValid allocator before.memory (slice key incoming))
    (fresh : Fresh before.table key incoming) (apart : Apart before.table kept)
    (incomingApart : key.arguments ≠ [] → ¬ kept incoming.address) :
    let ((result, current), _) := publicationCode.run getOrPut onFree allocator key incoming before effects
    Live allocator current ∧ Unique current.table ∧ Apart current.table kept ∧
      Frame kept before.memory current.memory ∧
      Memory.SliceValid allocator current.memory (slice key incoming) ∧
      match result with
      | .error .outOfMemory => current = before
      | .error _ => False
      | .ok () => current.table key = some incoming ∧
          view current.table = Cache.put equalityFields (view before.table) key incoming.id ∧
          ∀ old, before.table key = some old → key.arguments ≠ [] → current.memory old.address = none := by
  cases called : getOrPut key effects with
  | mk ok next =>
    cases ok with
    | false =>
      rw [run_failure getOrPut onFree allocator key incoming before effects next called]
      exact ⟨live, unique, apart, fun _ _ => rfl, valid, rfl⟩
    | true =>
      rw [run_success getOrPut onFree allocator key incoming before effects next called live]
      refine ⟨after_live allocator before key incoming live unique valid fresh,
        store_unique before.table key incoming unique fresh,
        store_apart before.table key incoming kept apart incomingApart,
        after_frame before key incoming kept apart, ?_, ?_⟩
      · exact retire_slice allocator before key (slice key incoming) valid
          (fun old found nonempty _ => fresh key old found nonempty nonempty)
      · exact ⟨by simp [after, store], view_store before.table key incoming,
          fun old found nonempty => replaced_released before key incoming old found nonempty⟩

theorem run_semantics (getOrPut : Key → σ → Bool × σ) (onFree : ArgumentSlice → σ → σ)
    (allocator : Nat) (key : Key) (incoming : Entry) (before : State) (effects : σ)
    (live : Live allocator before) (meaning : Meaning) (read : Read) (value : Word)
    (valid : Valid meaning read (view before.table))
    (denotation : key.eval meaning read = some value) (actual : read incoming.id = some value) :
    Valid meaning read (view (publicationCode.run getOrPut onFree allocator key incoming before effects).1.2.table) := by
  cases called : getOrPut key effects with
  | mk ok next =>
    cases ok with
    | false =>
      rw [run_failure getOrPut onFree allocator key incoming before effects next called]
      exact valid
    | true =>
      rw [run_success getOrPut onFree allocator key incoming before effects next called live]
      exact after_semantics meaning read before key incoming value valid denotation actual

end Compiler.Extraction.OwnedKeys
