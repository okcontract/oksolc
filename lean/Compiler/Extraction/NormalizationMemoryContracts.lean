/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemory
import Compiler.Extraction.ArgumentMemoryDuplicationProofs

namespace Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.InsertionSort
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache

/-- Existence of backing alone does not establish allocator ownership: a stack
cell could disappear at caller return. Retained as a distinct diagnostic predicate. -/
def Backed (heap : Memory.Heap) (memory : Compiler.ZigAir.Memory.State) : Prop :=
  ∀ id block, heap id = some block → ∃ cell, memory.heap.lookup id = some cell

/-- Every registry lifetime is allocator-owned and survives stack unwinding.
Borrowed source views and caller scratch are not registry entries. Payload
correspondence for non-argument blocks remains a separate graph obligation. -/
def Injected (heap : Memory.Heap) (memory : Compiler.ZigAir.Memory.State) : Prop :=
  ∀ id block, heap id = some block → ∃ cell, memory.heap.lookup id = some cell ∧ cell.stack = false

structure Valid (state : Session σ) : Prop where
  memory : state.memory.valid = true
  related : Related state.heap state.memory
  injected : Injected state.heap state.memory

theorem Injected.fresh (injected : Injected heap memory) (valid : memory.valid = true) : heap memory.nextId = none := by
  cases found : heap memory.nextId with
  | none => rfl
  | some block =>
    obtain ⟨cell, physical, _⟩ := injected _ _ found
    have older := (Compiler.ZigAir.Memory.valid_lookup memory memory.nextId cell valid physical).1
    omega

theorem Injected.retained (injected : Injected heap before)
    (shape : before.heap.RetainsShape after.heap) : Injected heap after := by
  intro id block stored
  obtain ⟨cell, found, persistent⟩ := injected id block stored
  obtain ⟨updated, lookup, same⟩ := shape id cell found
  exact ⟨updated, lookup, same.2.2.2.trans persistent⟩

theorem Injected.extended (injected : Injected heap before) (allocator base : Nat) (values : List NodeId) :
    Injected (write heap before.nextId (some ⟨allocator, .arguments values⟩))
      (Compiler.ZigAir.Memory.WordAllocation.extend before values.length base) := by
  intro id block stored
  by_cases same : id = before.nextId
  · subst id
    exact ⟨Compiler.ZigAir.Memory.WordAllocation.cell values.length base,
      by simp [Compiler.ZigAir.Memory.WordAllocation.extend_lookup], rfl⟩
  · obtain ⟨cell, found, persistent⟩ := injected id block (by simpa [write, same] using stored)
    exact ⟨cell, by simpa [Compiler.ZigAir.Memory.WordAllocation.extend_lookup, Ne.symm same] using found, persistent⟩

theorem Injected.published (injected : Injected heap memory) (id allocator : Nat) (old values : List NodeId)
    (stored : heap id = some ⟨allocator, .arguments old⟩) :
    Injected (write heap id (some ⟨allocator, .arguments values⟩)) memory := by
  intro query block present
  by_cases same : query = id
  · subst query; exact injected id _ stored
  · exact injected query block (by simpa [write, same] using present)

theorem Injected.erased (injected : Injected heap memory) (id : Nat) :
    Injected (write heap id none) (Compiler.ZigAir.Memory.erase memory id) := by
  intro query block stored
  have apart : query ≠ id := by intro same; simp [write, same] at stored
  obtain ⟨cell, found, persistent⟩ := injected query block (by simpa [write, apart] using stored)
  exact ⟨cell, by simpa [Compiler.ZigAir.Memory.erase_lookup, apart] using found, persistent⟩

theorem persistent_cleanup (state : Compiler.ZigAir.Memory.State) (mark id : Nat)
    (cell : Compiler.ZigAir.Memory.Allocation) (found : state.heap.lookup id = some cell) (persistent : cell.stack = false) :
    (Compiler.ZigAir.Memory.cleanup mark state).heap.lookup id = some cell := by
  rcases state with ⟨heap, nextId, nextAddress⟩
  change Compiler.ZigAir.Memory.Heap.lookup (heap.filter (fun entry => !entry.2.stack || entry.1 < mark)) id = some cell
  induction heap with
  | nil => cases found
  | cons entry tail ih =>
    rcases entry with ⟨key, old⟩
    by_cases same : key = id
    · subst key
      have equal : old = cell := Option.some.inj (by simpa [Compiler.ZigAir.Memory.Heap.lookup_cons] using found)
      subst old
      simp [persistent, Compiler.ZigAir.Memory.Heap.lookup_cons]
    · have rest : Compiler.ZigAir.Memory.Heap.lookup tail id = some cell := by
        simpa [Compiler.ZigAir.Memory.Heap.lookup_cons, same] using found
      simp only [List.filter_cons]
      split <;> simp only [Compiler.ZigAir.Memory.Heap.lookup_cons, if_neg same, ih rest]

theorem Injected.cleanup (injected : Injected heap memory) (mark : Nat) :
    Injected heap (Compiler.ZigAir.Memory.cleanup mark memory) := by
  intro id block stored
  obtain ⟨cell, found, persistent⟩ := injected id block stored
  exact ⟨cell, persistent_cleanup memory mark id cell found persistent, persistent⟩

theorem related_cleanup (heap : Memory.Heap) (memory : Compiler.ZigAir.Memory.State) (mark : Nat)
    (related : Related heap memory) : Related heap (Compiler.ZigAir.Memory.cleanup mark memory) := by
  intro allocator id values nonempty stored
  obtain ⟨⟨cell, found, typed, writable, persistent⟩, represented⟩ := related allocator id values nonempty stored
  have kept := persistent_cleanup memory mark id cell found persistent
  refine ⟨⟨cell, kept, typed, writable, persistent⟩, ?_⟩
  refine ⟨represented.1, ?_⟩
  intro index inside
  exact (Compiler.ZigAir.Memory.load_eq_of_lookup memory (Compiler.ZigAir.Memory.cleanup mark memory)
    true false word _ (kept.trans found.symm)).trans (represented.2 index inside)

theorem Valid.cleanup (state : Session σ) (valid : Valid state) (mark : Nat) :
    Valid ({ state with memory := Compiler.ZigAir.Memory.cleanup mark state.memory } : Session σ) :=
  ⟨Compiler.ZigAir.Memory.cleanup_preserves_valid _ _ valid.memory,
    related_cleanup _ _ mark valid.related, valid.injected.cleanup mark⟩

/-- The external allocator's region contract is checked at the reached state,
not at the state before normalization or before sorting. Ordinary OOM imposes
no region obligation. No normalization postcondition is an assumption. -/
def Admitted (external : External σ) : Prop :=
  ∀ site state (values : List NodeId) base reached, state.memory.valid = true → values ≠ [] →
    external.allocate site state (values.length * 4) state.effects = (some base, reached) →
    Compiler.ZigAir.Memory.WordAllocation.Fits state.memory values.length base

structure Ready (allocator : Nat) (sourceView : View) (original : List NodeId) (handle : Handle) (state : Session σ) : Prop where
  valid : Valid state
  contents : Represents state.memory handle.items handle.values
  source : Represents state.memory sourceView original
  owned : ∀ slice, handle.owned = some slice → slice.items = handle.values ∧ view slice = handle.items ∧ SliceValid allocator state.heap slice
  separate : original ≠ [] → ∀ slice, handle.owned = some slice → sourceView.allocation ≠ slice.address

theorem represented_frame (source : View) (values : List NodeId)
    (represented : Represents before source values)
    (framed : after.heap.lookup source.allocation = before.heap.lookup source.allocation) :
    Represents after source values := by
  refine ⟨represented.1, ?_⟩
  intro index inside
  exact (Compiler.ZigAir.Memory.load_eq_of_lookup before after true false word _ framed).trans (represented.2 index inside)

/-- Private non-word storage needs only the exact other-allocation frame.
Requiring word observations outside a target slice would supply no additional
registry fact: the mutated lifetime is absent from this registry. -/
theorem related_allocation_frame (heap : Memory.Heap) (before after : Compiler.ZigAir.Memory.State) (target : Nat)
    (related : Related heap before) (unregistered : heap target = none)
    (frame : ∀ id, id ≠ target → after.heap.lookup id = before.heap.lookup id) :
    Related heap after := by
  intro allocator id values nonempty stored
  have apart : id ≠ target := by intro same; subst id; rw [unregistered] at stored; contradiction
  obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ := related allocator id values nonempty stored
  exact ⟨⟨cell, (frame id apart).trans found, typed, writable, stack⟩,
    represented_frame _ values represented (frame id apart)⟩

theorem related_frame (heap : Memory.Heap) (before after : Compiler.ZigAir.Memory.State) (target : View)
    (related : Related heap before) (unregistered : heap target.allocation = none) (frame : HeapFrame target before after) :
    Related heap after :=
  related_allocation_frame heap before after target.allocation related unregistered frame.allocations

/-- A represented stack allocation cannot be an allocator-owned registry
lifetime. Separation is derived from injection, not supplied by the caller. -/
theorem Injected.stack_unregistered (heap : Memory.Heap) (memory : Compiler.ZigAir.Memory.State)
    (id : Nat) (cell : Compiler.ZigAir.Memory.Allocation) (injected : Injected heap memory)
    (found : memory.heap.lookup id = some cell) (stack : cell.stack = true) : heap id = none := by
  cases stored : heap id with
  | none => rfl
  | some block =>
    obtain ⟨registered, physical, persistent⟩ := injected id block stored
    have same : registered = cell := Option.some.inj (physical.symm.trans found)
    simp only [same, stack, Bool.true_eq_false] at persistent

/-- Typed writes preserve the session when they retain every registered
argument allocation and allocation shape. Ownership tags or native geometry
must derive this frame; shape alone does not retain initialized contents. -/
theorem Valid.memory_frame (before : Session σ) (after : Compiler.ZigAir.Memory.State)
    (valid : Valid before) (afterValid : after.valid = true)
    (shape : before.memory.heap.RetainsShape after.heap)
    (frame : ∀ allocator id values, before.heap id = some ⟨allocator, .arguments values⟩ →
      after.heap.lookup id = before.memory.heap.lookup id) :
    Valid ({ before with memory := after } : Session σ) := by
  refine ⟨afterValid, ?_, valid.injected.retained shape⟩
  intro allocator id values nonempty stored
  obtain ⟨⟨cell, found, typed, writable, stack⟩, represented⟩ := valid.related allocator id values nonempty stored
  exact ⟨⟨cell, (frame allocator id values stored).trans found, typed, writable, stack⟩,
    represented_frame _ values represented (frame allocator id values stored)⟩

/-- Preserve the existing session through private typed writes, using the
actual validity, shape and allocation frames of those writes. -/
theorem Valid.private_memory_frame (before : Session σ) (after : Compiler.ZigAir.Memory.State) (target : Nat)
    (valid : Valid before) (unregistered : before.heap target = none) (afterValid : after.valid = true)
    (shape : before.memory.heap.RetainsShape after.heap)
    (frame : ∀ id, id ≠ target → after.heap.lookup id = before.memory.heap.lookup id) :
    Valid ({ before with memory := after } : Session σ) := by
  apply Valid.memory_frame before after valid afterValid shape
  intro allocator id values stored
  apply frame id
  intro same
  subst id
  rw [unregistered] at stored
  contradiction

/-- Checked free preserves the same registry injection, and carries the native
free callback's actual private effects. This is the cleanup obligation of the
complete normalization operation. -/
theorem free_valid (external : External σ) (allocator : Nat) (slice : ArgumentSlice) (before : Session σ)
    (valid : Valid before) (live : SliceValid allocator before.heap slice) :
    ∃ after, free external allocator slice before = (.ok (), after) ∧ Valid after ∧
      ReleasePost before.heap before.memory allocator slice after.heap after.memory ∧
      after.effects = if slice.items.isEmpty then before.effects else external.free slice before := by
  obtain ⟨heap, memory, released, post⟩ := release_refines before.heap before.memory allocator slice valid.memory valid.related live
  refine ⟨⟨heap, memory, if slice.items.isEmpty then before.effects else external.free slice before⟩, ?_,
    ⟨post.valid, post.related, ?_⟩, post, rfl⟩
  · simp only [free, released]
  · by_cases empty : slice.items = []
    · have same := released
      simp only [release, empty, List.isEmpty_nil, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq] at same
      rcases same with ⟨rfl, rfl⟩
      exact valid.injected
    · have exactRelease := release_effects before.heap before.memory allocator slice valid.memory empty
        (live.resolve_left empty) (valid.related _ _ _ empty (live.resolve_left empty)).1
      rw [exactRelease] at released
      cases released
      exact valid.injected.erased slice.address

theorem duplication_valid (before : Session σ) (allocator : Nat) (source : View) (values : List NodeId)
    (slice : ArgumentSlice) (heap : Memory.Heap) (memory : Compiler.ZigAir.Memory.State) (effects : σ)
    (valid : Valid before) (post : Duplication.Post before.heap before.memory allocator source values slice heap memory) :
    Valid (⟨heap, memory, effects⟩ : Session σ) := by
  refine ⟨post.valid, post.related, ?_⟩
  by_cases empty : values = []
  · rw [post.empty empty, post.registration, empty]
    exact valid.injected
  · intro id block stored
    by_cases same : id = before.memory.nextId
    · subst id
      obtain ⟨cell, found, _, _, persistent⟩ := post.owned empty
      rw [post.descriptor] at found
      exact ⟨cell, found, persistent⟩
    · rw [post.registration, if_neg (by simpa using empty)] at stored
      obtain ⟨cell, found, persistent⟩ := valid.injected id block (by simpa [write, same] using stored)
      exact ⟨cell, (post.frame id same).trans found, persistent⟩

end Compiler.Extraction.Memory.Arguments.Normalization
