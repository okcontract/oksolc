/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemAllocation
import Compiler.ZigAir.MemoryRegionAllocationProofs

namespace Compiler.Extraction.AssemblyItem.Creation
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

/-- The captured nominal extent, including alignment, is the external request.
This contract models Allocator.create's undefined persistent storage. It does
not initialize fields or model the allocator implementation. -/
def layout : Compiler.ZigAir.Memory.Layout := allocationType.layout.getD ⟨0, 0⟩
theorem layout_captured : allocationType.layout = some layout := rfl
theorem view_layout_captured : viewType.layout = some layout := by decide
abbrev Allocate (σ : Type) := Compiler.ZigAir.Memory.Layout → Session σ → Option Nat × σ

inductive Fault where
  | outOfMemory
  | memory (reason : Compiler.ZigAir.Memory.Fault)
  | registryCollision
  deriving DecidableEq, Repr

def cell (base : Nat) : Compiler.ZigAir.Memory.Allocation := ⟨base, viewType, [], true, false⟩
def extend (before : Session σ) (base : Nat) : Compiler.ZigAir.Memory.State :=
  ⟨(before.memory.nextId, cell base) :: before.memory.heap, before.memory.nextId + 1,
    max before.memory.nextAddress (base + layout.bytes)⟩

/-- Register only the allocation lifetime. `item` is a provisional logical
projection; Storage.State separately tracks the as-yet-absent initialized value.
A rejected host response retains private effects, with no unchecked typed cell;
a registry collision retains the accepted typed allocation. Neither is OOM. -/
def create (request : Allocate σ) (allocator : Nat) (item : Cache.Item) (before : Session σ) :
    Except Fault Nat × Session σ :=
  if !before.memory.valid then (.error (.memory .malformed), before) else
  let (response, effects) := request layout before
  match response with
  | none => (.error .outOfMemory, { before with effects })
  | some base =>
    let memory := extend before base
    if !memory.valid then (.error (.memory .memoryValidity), { before with effects }) else
    let reached : Session σ := { before with memory, effects }
    match before.heap before.memory.nextId with
    | some _ => (.error .registryCollision, reached)
    | none => (.ok before.memory.nextId,
        { reached with heap := write before.heap before.memory.nextId (some ⟨allocator, .item item⟩) })

structure Created (allocator id : Nat) (before after : Session σ) : Prop where
  valid : Valid after
  owned : Owned allocator id after
  fresh : id = before.memory.nextId
  frame : ∀ query, query ≠ id → after.heap query = before.heap query ∧
    after.memory.heap.lookup query = before.memory.heap.lookup query
  nextId : after.memory.nextId = before.memory.nextId + 1
  nextAddress : before.memory.nextAddress ≤ after.memory.nextAddress

theorem extend_lookup (before : Session σ) (base query : Nat) (apart : query ≠ before.memory.nextId) :
    (extend before base).heap.lookup query = before.memory.heap.lookup query := by
  simp [extend, Compiler.ZigAir.Memory.Heap.lookup_cons, Ne.symm apart]

theorem create_shape (request : Allocate σ) (allocator id : Nat) (item : Cache.Item) (before after : Session σ)
    (executed : create request allocator item before = (.ok id, after)) :
    ∃ base effects, request layout before = (some base, effects) ∧ id = before.memory.nextId ∧
      after = ⟨write before.heap id (some ⟨allocator, .item item⟩), extend before base, effects⟩ ∧
      after.memory.valid = true := by
  dsimp only [create] at executed
  split at executed
  · simp at executed
  · cases requested : request layout before with
    | mk response effects =>
      simp only [requested] at executed
      cases response with
      | none => simp at executed
      | some base =>
        dsimp only at executed
        split at executed
        · simp at executed
        next accepted =>
          split at executed
          · simp at executed
          · cases executed
            exact ⟨base, effects, rfl, rfl, rfl, by simpa using accepted⟩

/-- Creation records this exact provisional key. Initialized native fields
still require the subsequent successful clone and assignment. -/
theorem create_registered (request : Allocate σ) (allocator id : Nat) (item : Cache.Item) (before after : Session σ)
    (executed : create request allocator item before = (.ok id, after)) :
    after.heap id = some ⟨allocator, .item item⟩ := by
  obtain ⟨base, effects, _, _, rfl, _⟩ := create_shape request allocator id item before after executed
  exact Compiler.Extraction.Memory.write_same _ _ _

theorem create_verified (request : Allocate σ) (allocator id : Nat) (item : Cache.Item) (before after : Session σ)
    (initial : Valid before) (executed : create request allocator item before = (.ok id, after)) :
    Created allocator id before after := by
  obtain ⟨base, effects, _, rfl, rfl, valid⟩ := create_shape request allocator id item before after executed
  refine ⟨⟨valid, ?_, ?_⟩, ?_, rfl, ?_, rfl, Nat.le_max_left _ _⟩
  · intro owner query values nonempty stored
    have apart : query ≠ before.memory.nextId := by intro same; simp [write, same] at stored
    obtain ⟨⟨old, found, typed, writable, stack⟩, represented⟩ := initial.related owner query values nonempty
      (by simpa [write, apart] using stored)
    have framed := extend_lookup before base query apart
    exact ⟨⟨old, framed.trans found, typed, writable, stack⟩, represented_frame _ values represented framed⟩
  · intro query block stored
    by_cases same : query = before.memory.nextId
    · subst query; exact ⟨cell base, by simp [extend, Compiler.ZigAir.Memory.Heap.lookup_cons], rfl⟩
    · obtain ⟨old, found, _persistent⟩ := initial.injected query block (by simpa [write, same] using stored)
      exact ⟨old, (extend_lookup before base query same).trans found, _persistent⟩
  · exact ⟨⟨item, by simp [write]⟩, cell base, by simp [extend, Compiler.ZigAir.Memory.Heap.lookup_cons], rfl, rfl, rfl⟩
  · intro query apart
    exact ⟨by simp [write, apart], extend_lookup before base query apart⟩

/-- The actual admitted allocator response derives creation, complete declared
geometry and ownership. Fields remain uninitialized; registry freshness follows
from the initial injection instead of a successful final allocation premise. -/
theorem create_from_response (request : Allocate σ) (allocator base : Nat) (item : Cache.Item)
    (before : Session σ) (effects : σ) (valid : Valid before)
    (response : request layout before = (some base, effects))
    (fits : Compiler.ZigAir.Memory.RegionAllocation.Fits before.memory layout base) :
    let after : Session σ := ⟨write before.heap before.memory.nextId (some ⟨allocator, .item item⟩), extend before base, effects⟩
    create request allocator item before = (.ok before.memory.nextId, after) ∧ Created allocator before.memory.nextId before after := by
  have memoryValid : (extend before base).valid = true :=
    Compiler.ZigAir.Memory.RegionAllocation.extend_valid before.memory viewType layout base valid.memory view_layout_captured fits
  have executed : create request allocator item before =
      (.ok before.memory.nextId, ⟨write before.heap before.memory.nextId (some ⟨allocator, .item item⟩), extend before base, effects⟩) := by
    simp only [create, valid.memory, Bool.not_true, Bool.false_eq_true, ↓reduceIte, response, memoryValid,
      valid.injected.fresh valid.memory]
  exact ⟨executed, create_verified request allocator before.memory.nextId item before _ valid executed⟩

theorem Created.registered {allocator id : Nat} {before after : Session σ}
    (post : Created allocator id before after) (initial : Valid before)
    (query : Nat) (allocation : Memory.Allocation) (stored : before.heap query = some allocation) :
    after.heap query = some allocation := by
  obtain ⟨cell, found, _⟩ := initial.injected query allocation stored
  have older := (Compiler.ZigAir.Memory.valid_lookup before.memory query cell initial.memory found).1
  exact (post.frame query (by rw [post.fresh]; omega)).1.trans stored

theorem Created.arguments (allocator id : Nat) (before after : Session σ)
    (post : Created allocator id before after) (initial : Valid before)
    (slice : ArgumentSlice) (live : SliceValid allocator before.heap slice) : SliceValid allocator after.heap slice := by
  rcases live with empty | stored
  · exact Or.inl empty
  · exact Or.inr (post.registered initial slice.address _ stored)

theorem create_oom (request : Allocate σ) (allocator : Nat) (item : Cache.Item) (before after : Session σ)
    (executed : create request allocator item before = (.error .outOfMemory, after)) :
    ∃ effects, request layout before = (none, effects) ∧ after = { before with effects } := by
  dsimp only [create] at executed
  split at executed
  · simp at executed
  · cases requested : request layout before with
    | mk response effects =>
      simp only [requested] at executed
      cases response with
      | none => cases executed; exact ⟨effects, rfl, rfl⟩
      | some base =>
        dsimp only at executed
        split at executed
        · simp at executed
        · split at executed <;> simp at executed

end Compiler.Extraction.AssemblyItem.Creation
