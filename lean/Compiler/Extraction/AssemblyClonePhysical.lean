/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyCloneMemory

namespace Compiler.Extraction.AssemblyClone.Physical
open Compiler.Extraction.Memory Compiler.Extraction.Storage
open Compiler.Extraction.Memory.Arguments.Normalization

def payload (value : Value Metadata) : Option AssemblyItemDeinit.Bytes :=
  value.verbatim.map fun verbatim => descriptor verbatim.data

def run (request : Allocate σ) (allocator : Nat) (input : Value Metadata) (before : Session σ) :=
  cloneCode.run (duplicate request allocator) input before

theorem run_duplicate (request : Allocate σ) (allocator : Nat) (input : Value Metadata)
    (source : Verbatim) (bytes : Bytes) (before after : Session σ)
    (present : input.verbatim = some source)
    (duplicated : duplicate request allocator source.data before = (.ok bytes, after)) :
    run request allocator input before = (.ok { input with verbatim := some { source with data := bytes } }, after) := by
  simp only [run, CloneCode.run, cloneCode, present, Cache.Scalar.run, duplicated, ↓reduceIte]

structure Cloned (allocator : Nat) (input copied : Value Metadata) (before after : Session σ) : Prop where
  same : SameValue input copied
  valid : Valid after
  owned : ∀ slice, payload copied = some slice → AssemblyItemDeinit.Owned allocator slice after
  reads : ∀ verbatim, copied.verbatim = some verbatim → Reads after.memory verbatim.data
  fresh : ∀ slice, payload copied = some slice → slice.length ≠ 0 → slice.address = before.memory.nextId
  frame : ∀ id, id ≠ before.memory.nextId → after.heap id = before.heap id ∧
    after.memory.heap.lookup id = before.memory.heap.lookup id
  offset : ∀ verbatim, copied.verbatim = some verbatim → verbatim.data.offset = 0

theorem run_valid (request : Allocate σ) (allocator : Nat) (input copied : Value Metadata) (before after : Session σ)
    (initial : Valid before) (executed : run request allocator input before = (.ok copied, after)) :
    Cloned allocator input copied before after := by
  dsimp only [run, CloneCode.run, cloneCode] at executed
  cases present : input.verbatim with
  | none =>
    simp only [present] at executed
    cases executed
    exact ⟨⟨rfl, rfl, rfl⟩, initial,
      by intro slice selected; simp [payload, present] at selected,
      by intro verbatim selected; simp [present] at selected,
      by intro slice selected; simp [payload, present] at selected,
      fun _ _ => ⟨rfl, rfl⟩,
      by intro verbatim selected; simp [present] at selected⟩
  | some source =>
    simp only [present, ↓reduceIte, Cache.Scalar.run] at executed
    cases duplicated : duplicate request allocator source.data before with
    | mk result middle =>
      simp only [duplicated] at executed
      cases result with
      | error fault => simp at executed
      | ok bytes =>
        have checked := duplicate_valid request allocator source.data bytes before middle initial duplicated
        cases executed
        refine ⟨⟨rfl, rfl, ?_⟩, checked.valid, ?_, ?_, ?_, checked.frame, ?_⟩
        · simp [present, checked.contents]
        · intro slice selected
          have same : descriptor bytes = slice := by simpa [payload] using selected
          subst slice; exact checked.owned
        · intro verbatim selected
          cases Option.some.inj selected
          exact checked.reads
        · intro slice selected _
          have same : descriptor bytes = slice := by simpa [payload] using selected
          subst slice; exact checked.address
        · intro verbatim selected
          cases Option.some.inj selected
          exact checked.offset

theorem run_oom (request : Allocate σ) (allocator : Nat) (input : Value Metadata) (before after : Session σ)
    (executed : run request allocator input before = (.error .outOfMemory, after)) :
    after.heap = before.heap ∧ after.memory = before.memory := by
  dsimp only [run, CloneCode.run, cloneCode] at executed
  cases present : input.verbatim with
  | none => simp [present] at executed
  | some source =>
    simp only [present, ↓reduceIte, Cache.Scalar.run] at executed
    cases duplicated : duplicate request allocator source.data before with
    | mk result middle =>
      simp only [duplicated] at executed
      cases result with
      | ok bytes => simp at executed
      | error fault =>
        cases executed
        obtain ⟨effects, _, rfl⟩ := duplicate_oom request allocator source.data before _ duplicated
        exact ⟨rfl, rfl⟩

theorem Cloned.item (checked : Cloned allocator input copied before after) (initial : Valid before)
    (id : Nat) (owned : AssemblyItem.Owned allocator id before) : AssemblyItem.Owned allocator id after := by
  obtain ⟨⟨item, stored⟩, cell, found, typed, writable, stack⟩ := owned
  have older := (Compiler.ZigAir.Memory.valid_lookup before.memory id cell initial.memory found).1
  obtain ⟨logical, physical⟩ := checked.frame id (by omega)
  exact ⟨⟨item, logical.trans stored⟩, cell, physical.trans found, typed, writable, stack⟩

/-- Every existing registered allocation precedes the clone's fresh lifetime.
Retain its exact value, not only its allocator or allocation kind. -/
theorem Cloned.registered (checked : Cloned allocator input copied before after) (initial : Valid before)
    (id : Nat) (allocation : Compiler.Extraction.Memory.Allocation) (stored : before.heap id = some allocation) :
    after.heap id = some allocation := by
  obtain ⟨cell, found, _⟩ := initial.injected id allocation stored
  have older := (Compiler.ZigAir.Memory.valid_lookup before.memory id cell initial.memory found).1
  exact (checked.frame id (by omega)).1.trans stored

theorem Cloned.arguments (checked : Cloned allocator input copied before after) (initial : Valid before)
    (slice : ArgumentSlice) (live : SliceValid allocator before.heap slice) : SliceValid allocator after.heap slice := by
  rcases live with empty | stored
  · exact Or.inl empty
  · exact Or.inr (checked.registered initial slice.address _ stored)

/-- Clone then execute the same complete expression destructor used for late
insertion rollback. The caller supplies the already allocated object/arguments;
clone execution, rather than an initial payload-ownership premise, supplies the
new payload. Assigning the returned value to native object fields remains a
separate caller projection obligation. -/
def rollback (request : Allocate σ) (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ)
    (external : External σ) (allocator : Nat) (input : Value Metadata) (target : ExpressionDeinit.Descriptor)
    (before : Session σ) : Except (Sum Fault (ExpressionDeinit.Fault ExpressionDeinit.Lifetime.ItemFault)) Unit × ExpressionDeinit.State σ :=
  let (result, middle) := run request allocator input before
  match result with
  | .error fault => (.error (.inl fault), ⟨middle, false⟩)
  | .ok copied =>
    let (result, after) := ExpressionDeinit.Lifetime.run bytes objects external allocator (fun _ => payload copied) target middle
    (result.mapError Sum.inr, after)

theorem rollback_verified (request : Allocate σ) (bytes : AssemblyItemDeinit.Release σ) (objects : AssemblyItem.Release σ)
    (external : External σ) (allocator : Nat) (input copied : Value Metadata) (target : ExpressionDeinit.Descriptor)
    (before middle : Session σ) (initial : Valid before) (item : AssemblyItem.Owned allocator target.item before)
    (arguments : SliceValid allocator before.heap target.arguments)
    (cloned : run request allocator input before = (.ok copied, middle)) :
    Cloned allocator input copied before middle ∧ ∃ after,
      rollback request bytes objects external allocator input target before = (.ok (), after) ∧
      ExpressionDeinit.Lifetime.Post (payload copied) target middle after := by
  have checked := run_valid request allocator input copied before middle initial cloned
  obtain ⟨after, destroyed, post⟩ := ExpressionDeinit.Lifetime.run_verified bytes objects external allocator
    (fun _ => payload copied) target middle checked.valid (checked.item initial target.item item)
    (checked.arguments initial target.arguments arguments) checked.owned
  exact ⟨checked, after, by simp [rollback, cloned, destroyed, Except.mapError], post⟩

end Compiler.Extraction.AssemblyClone.Physical
