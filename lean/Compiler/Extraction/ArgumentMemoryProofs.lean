/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemory
import Compiler.Extraction.MemoryProofs

namespace Compiler.Extraction.Memory.Arguments
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray

theorem owned_writable (state : Compiler.ZigAir.Memory.State) (id length : Nat)
    (owned : Owned state id length) : Writable state ⟨id, 0, length⟩ := by
  obtain ⟨cell, found, typed, writable, _⟩ := owned
  exact ⟨length, cell, found, typed, writable, by simp⟩

theorem related_read (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (slice : ArgumentSlice) (related : Related heap state) (live : SliceValid allocator heap slice)
    (index : Nat) (inside : index < slice.items.length) :
    readArgument heap slice index = .ok slice.items[index] ∧
    Compiler.ZigAir.Memory.load state ((view slice).pointer index) = .ok (number slice.items[index]) := by
  have nonempty : slice.items ≠ [] := by intro empty; simp [empty] at inside
  have stored := live.resolve_left nonempty
  exact ⟨by simp [slice_read allocator heap slice live index, List.getElem?_eq_getElem inside],
    (related allocator slice.address slice.items nonempty stored).2.2 index inside⟩

theorem release_empty (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator id : Nat) :
    release heap state allocator ⟨id, []⟩ = .ok (heap, state) := rfl

theorem release_effects (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (slice : ArgumentSlice) (valid : state.valid = true) (nonempty : slice.items ≠ [])
    (stored : heap slice.address = some ⟨allocator, .arguments slice.items⟩)
    (owned : Owned state slice.address slice.items.length) :
    release heap state allocator slice =
      .ok (write heap slice.address none, Compiler.ZigAir.Memory.erase state slice.address) := by
  obtain ⟨cell, found, typed, writable, stack⟩ := owned
  simp [release, releaseSlice, Memory.release, nonempty, stored, valid, found, typed, writable, stack,
    Compiler.ZigAir.Memory.releaseOwned, Except.mapError, bind, Except.bind]

theorem related_erase (heap : Heap) (state : Compiler.ZigAir.Memory.State) (id : Nat)
    (related : Related heap state) :
    Related (write heap id none) (Compiler.ZigAir.Memory.erase state id) := by
  intro allocator query items nonempty stored
  have apart : query ≠ id := by intro same; simp [write, same] at stored
  have original : heap query = some ⟨allocator, .arguments items⟩ := by simpa [write, apart] using stored
  obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ := related allocator query items nonempty original
  refine ⟨⟨cell, ?_, typed, writable, stack⟩, represented.1, ?_⟩
  · simpa only [Compiler.ZigAir.Memory.erase_lookup, if_neg apart] using found
  · intro index inside
    simp only [View.pointer]
    rw [Compiler.ZigAir.Memory.erase_load_other]
    · exact represented.2 index inside
    · exact apart

/-- A release is related at both heap levels, invalidates the exact nonempty
lifetime and frames every other allocation, including uninitialized contents.
Counters are history, so neither free nor its empty case rewinds them. -/
structure ReleasePost (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (slice : ArgumentSlice) (afterHeap : Heap) (after : Compiler.ZigAir.Memory.State) : Prop where
  logical : releaseSlice heap allocator slice = .ok afterHeap
  valid : after.valid = true
  related : Related afterHeap after
  nextId : after.nextId = state.nextId
  nextAddress : after.nextAddress = state.nextAddress
  frame : ∀ id, id ≠ slice.address → afterHeap id = heap id ∧ after.heap.lookup id = state.heap.lookup id
  dead : slice.items ≠ [] → afterHeap slice.address = none ∧ after.heap.lookup slice.address = none

theorem release_refines (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (slice : ArgumentSlice) (valid : state.valid = true) (related : Related heap state)
    (live : SliceValid allocator heap slice) :
    ∃ afterHeap after, release heap state allocator slice = .ok (afterHeap, after) ∧
      ReleasePost heap state allocator slice afterHeap after := by
  by_cases empty : slice.items = []
  · refine ⟨heap, state, ?_, ?_⟩
    · simp [release, empty]
    · exact ⟨by simp [releaseSlice, empty], valid, related, rfl, rfl,
        fun _ _ => ⟨rfl, rfl⟩, fun nonempty => False.elim (nonempty empty)⟩
  · have stored := live.resolve_left empty
    refine ⟨write heap slice.address none, Compiler.ZigAir.Memory.erase state slice.address,
      release_effects heap state allocator slice valid empty stored (related _ _ _ empty stored).1, ?_⟩
    refine ⟨by simp [releaseSlice, Memory.release, empty, stored],
      Compiler.ZigAir.Memory.erase_preserves_valid state slice.address valid,
      related_erase heap state slice.address related, rfl, rfl, ?_, ?_⟩
    · intro id apart
      exact ⟨write_other heap slice.address id none apart,
        by simp only [Compiler.ZigAir.Memory.erase_lookup, if_neg apart]⟩
    · intro _
      exact ⟨write_same heap slice.address none, by simp [Compiler.ZigAir.Memory.erase_lookup]⟩

theorem released_read_rejects (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (slice : ArgumentSlice) (afterHeap : Heap) (after : Compiler.ZigAir.Memory.State)
    (post : ReleasePost heap state allocator slice afterHeap after) (nonempty : slice.items ≠ [])
    (index : Nat) (inside : index < slice.items.length) :
    readArgument afterHeap slice index = .error .unallocated ∧
    Compiler.ZigAir.Memory.load after ((view slice).pointer index) = .error .unallocated := by
  have dead := post.dead nonempty
  refine ⟨by simp [readArgument, inside, dead.1], ?_⟩
  simp [Compiler.ZigAir.Memory.load, Compiler.ZigAir.Memory.access, View.pointer, View.address,
    view, word, Compiler.ZigAir.Memory.Ty.layout, dead.2, bind, Except.bind]

end Compiler.Extraction.Memory.Arguments
