/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemFieldLayout
import Compiler.Extraction.AssemblyItemDeinitProofs

namespace Compiler.Extraction.AssemblyItem
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

/-- An allocation lifetime for the complete captured item declaration. No initialized
native field contents are claimed; the value may already have been invalidated
by AssemblyItem.deinit. The logical item is the existing graph projection. -/
def Owned (allocator id : Nat) (state : Session σ) : Prop :=
  (∃ item, state.heap id = some ⟨allocator, .item item⟩) ∧
  ∃ cell, state.memory.heap.lookup id = some cell ∧ cell.type = viewType ∧
    cell.writable = true ∧ cell.stack = false

/-- Item storage changes preserve session validity and object ownership when
they retain allocation shape and other allocations. Registry types derive the
argument-buffer separation used by both assignment and invalidation. -/
theorem session_frame (allocator id : Nat) (before : Session σ) (after : Compiler.ZigAir.Memory.State)
    (memoryValid : after.valid = true) (shape : before.memory.heap.RetainsShape after.heap)
    (frame : ∀ query, query ≠ id → after.heap.lookup query = before.memory.heap.lookup query)
    (valid : Valid before) (owned : Owned allocator id before) :
    Valid { before with memory := after } ∧ Owned allocator id { before with memory := after } := by
  obtain ⟨⟨item, itemStored⟩, cell, found, typed, writable, stack⟩ := owned
  refine ⟨Valid.memory_frame before after valid memoryValid shape ?_, ⟨item, itemStored⟩, ?_⟩
  · intro owner query contents stored
    have apart : query ≠ id := by intro same; rw [same, itemStored] at stored; cases stored
    exact frame query apart
  · obtain ⟨updated, updatedFound, same⟩ := shape id cell found
    exact ⟨updated, updatedFound, same.2.1.trans typed, same.2.2.1.trans writable, same.2.2.2.trans stack⟩

abbrev Release (σ : Type) := Nat → Session σ → σ

def destroy (external : Release σ) (allocator id : Nat) (before : Session σ) :
    Except Arguments.ReleaseFault Unit × Session σ :=
  let checked : Except Arguments.ReleaseFault (Heap × Compiler.ZigAir.Memory.State) := do
    let heap ← (Memory.release before.heap allocator id).mapError Arguments.ReleaseFault.ownership
    let some allocation := before.heap id | .error (.ownership .unallocated)
    let .item _ := allocation.block | .error (.ownership .wrongType)
    let memory ← (Compiler.ZigAir.Memory.releaseOwned before.memory id viewType).mapError Arguments.ReleaseFault.memory
    .ok (heap, memory)
  match checked with
  | .error fault => (.error fault, before)
  | .ok (heap, memory) => (.ok (), ⟨heap, memory, external id before⟩)

structure Released (id : Nat) (before after : Session σ) : Prop where
  valid : Valid after
  nextId : after.memory.nextId = before.memory.nextId
  nextAddress : after.memory.nextAddress = before.memory.nextAddress
  frame : ∀ query, query ≠ id → after.heap query = before.heap query ∧
    after.memory.heap.lookup query = before.memory.heap.lookup query
  dead : after.heap id = none ∧ after.memory.heap.lookup id = none

theorem destroy_verified (external : Release σ) (allocator id : Nat) (before : Session σ)
    (valid : Valid before) (owned : Owned allocator id before) :
    ∃ after, destroy external allocator id before = (.ok (), after) ∧ Released id before after ∧
      after.effects = external id before := by
  obtain ⟨⟨item, stored⟩, cell, found, typed, writable, stack⟩ := owned
  refine ⟨⟨write before.heap id none, Compiler.ZigAir.Memory.erase before.memory id, external id before⟩, ?_, ?_, rfl⟩
  · simp [destroy, stored, Memory.release, Compiler.ZigAir.Memory.releaseOwned,
      valid.memory, found, typed, writable, stack, Except.mapError, bind, Except.bind]
  · exact ⟨⟨Compiler.ZigAir.Memory.erase_preserves_valid _ _ valid.memory,
      Arguments.related_erase _ _ _ valid.related, valid.injected.erased _⟩, rfl, rfl,
      fun query apart => ⟨by simp [write, apart], by simp [Compiler.ZigAir.Memory.erase_lookup, apart]⟩,
      by simp [write], by simp [Compiler.ZigAir.Memory.erase_lookup]⟩

namespace Released

theorem arguments (id : Nat) (before after : Session σ) (post : Released id before after)
    (allocator : Nat) (owned : Owned allocator id before) (argumentAllocator : Nat) (arguments : ArgumentSlice)
    (live : SliceValid argumentAllocator before.heap arguments) : SliceValid argumentAllocator after.heap arguments := by
  rcases live with empty | stored
  · exact Or.inl empty
  · obtain ⟨item, itemStored⟩ := owned.1
    have apart : arguments.address ≠ id := by
      intro same; rw [same, itemStored] at stored; cases stored
    exact Or.inr ((post.frame arguments.address apart).1.trans stored)

theorem keeps_dead (id : Nat) (before after : Session σ) (post : Released id before after) (query : Nat)
    (dead : before.heap query = none ∧ before.memory.heap.lookup query = none) :
    after.heap query = none ∧ after.memory.heap.lookup query = none := by
  by_cases same : query = id
  · subst query; exact post.dead
  · exact ⟨(post.frame query same).1.trans dead.1, (post.frame query same).2.trans dead.2⟩

end Released

/-- Nominal item and byte blocks cannot own the same allocation lifetime. -/
theorem payload_ne (allocator id : Nat) (slice : AssemblyItemDeinit.Bytes) (state : Session σ)
    (itemOwned : Owned allocator id state) (payloadOwned : AssemblyItemDeinit.Owned allocator slice state)
    (nonempty : slice.length ≠ 0) : slice.address ≠ id := by
  obtain ⟨item, stored⟩ := itemOwned.1
  have bytes := (payloadOwned.resolve_left nonempty).1
  intro same
  rw [same, stored] at bytes
  cases bytes

/-- The live item and its owned nonempty payload occupy distinct registry
lifetimes. Therefore payload cleanup supplies the still-owned object needed by
allocator.destroy; that object lifetime frame is proved, not a new assumption. -/
theorem after_payload (allocator id : Nat) (payload : Option AssemblyItemDeinit.Bytes)
    (before : Session σ) (after : AssemblyItemDeinit.State σ)
    (owned : Owned allocator id before)
    (payloadOwned : ∀ slice, payload = some slice → AssemblyItemDeinit.Owned allocator slice before)
    (post : AssemblyItemDeinit.Post payload before after) : Owned allocator id after.memory := by
  have untouched : ¬AssemblyItemDeinit.Touches payload id := by
    intro touched
    obtain ⟨slice, selected, nonempty, same⟩ := touched
    exact payload_ne allocator id slice before owned (payloadOwned slice selected) nonempty same.symm
  obtain ⟨⟨item, stored⟩, cell, found, typed, writable, stack⟩ := owned
  exact ⟨⟨item, (post.frame id untouched).1.trans stored⟩,
    cell, (post.frame id untouched).2.trans found, typed, writable, stack⟩

end Compiler.Extraction.AssemblyItem
