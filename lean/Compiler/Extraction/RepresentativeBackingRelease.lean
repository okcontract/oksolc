/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeArrayAllocation
import Compiler.Extraction.RepresentativeArrayAllocationView
import Compiler.Extraction.NormalizationMemoryContracts

namespace Compiler.Extraction.RepresentativeArray.Backing.Release
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

abbrev Registry := Compiler.Extraction.Memory.Heap
abbrev Fault := Compiler.Extraction.Memory.Arguments.ReleaseFault

/-- The fixed host.release contract receives the logical allocator brand and
the actual native base, byte extent and alignment. It returns reached private
effects. Brands are not native Allocator.ptr values, which may be undefined. -/
abbrev External (σ : Type) := Nat → Nat → Nat → Nat → σ → σ

/-- Complete representative storage, including uninitialized spare capacity.
The registry uses its existing vector block; initialized descriptor/payload
correspondence remains separate from this permission to release storage. -/
def Owned (allocator : Nat) (data : Address) (capacity : Nat) (before : Session σ) : Prop :=
  data.offset = 0 ∧ (∃ cells, Compiler.Extraction.Memory.Vector allocator before.heap data.allocation cells) ∧
    ∃ cell, before.memory.heap.lookup data.allocation = some cell ∧ cell.type = Backing.type capacity ∧
      cell.writable = true ∧ cell.stack = false

/-- Validate ownership and the full physical extent before the external free.
These faults reject invalid compiler preconditions; they are not native OOM or
a claim that an invalid native free rolls back. No descriptor leaf is read. -/
def check (allocator : Nat) (data : Address) (capacity : Nat) (before : Session σ) :
    Except Fault (Registry × State × Nat) := do
  if data.offset ≠ 0 then .error (.memory .memoryValidity) else
  let heap ← (Compiler.Extraction.Memory.release before.heap allocator data.allocation).mapError Compiler.Extraction.Memory.Arguments.ReleaseFault.ownership
  let some allocation := before.heap data.allocation | .error (.ownership .unallocated)
  let .representatives _ := allocation.block | .error (.ownership .wrongType)
  let some cell := before.memory.heap.lookup data.allocation | .error (.memory .unallocated)
  let memory ← (releaseOwned before.memory data.allocation (Backing.type capacity)).mapError Compiler.Extraction.Memory.Arguments.ReleaseFault.memory
  .ok (heap, memory, cell.base)

/-- Execute free of an already evaluated allocatedSlice. The source wrapper
skips empty extents before dereferencing the sentinel or calling rawFree.
Nonempty release consumes capacity * sizeof(Expression), never items.len. -/
def run (external : External σ) (allocator : Nat) (data : Address) (capacity : Nat) (before : Session σ) :
    Except Fault Unit × Session σ :=
  if capacity = 0 then (.ok (), before) else
  match check allocator data capacity before with
  | .error fault => (.error fault, before)
  | .ok (heap, memory, base) =>
    (.ok (), ⟨heap, memory, external allocator base (capacity * 32) 8 before.effects⟩)

/-- Derive the free view from the captured header. Length and spare descriptor
contents are not inspected. A growth caller must retain its previously evaluated
old_memory across intervening copy; this entry is also useful for that view's
source-bound acquisition/release check, not a complete growth implementation. -/
def fromHeader (external : External σ) (allocator : Nat) (header : Address) (before : Session σ) :
    Except Fault Unit × Session σ :=
  match allocatedSlice before.memory header with
  | .error fault => (.error (.memory fault), before)
  | .ok (.slice declared data capacity) =>
    if declared ≠ itemsType then (.error (.memory .malformed), before) else
    run external allocator data capacity before
  | .ok _ => (.error (.memory .malformed), before)

theorem empty (external : External σ) (allocator : Nat) (data : Address) (before : Session σ) :
    run external allocator data 0 before = (.ok (), before) := by
  simp only [run, ↓reduceIte]

theorem checked_of_owned (allocator : Nat) (data : Address) (capacity : Nat) (before : Session σ)
    (valid : Valid before) (owned : Owned allocator data capacity before) :
    ∃ base, check allocator data capacity before =
      .ok (Compiler.Extraction.Memory.write before.heap data.allocation none, erase before.memory data.allocation, base) := by
  obtain ⟨offset, ⟨cells, registered⟩, cell, found, typed, writable, persistent⟩ := owned
  refine ⟨cell.base, ?_⟩
  simp only [Compiler.Extraction.Memory.Vector] at registered
  simp [check, offset, registered, Compiler.Extraction.Memory.release, releaseOwned,
    valid.memory, found, typed, writable, persistent, Except.mapError, bind, Except.bind]

/-- The checker derives permission from both registries, before any callback.
In particular an accepted extent cannot be a shorter initialized prefix. -/
theorem check_shape (allocator : Nat) (data : Address) (capacity : Nat) (before : Session σ)
    (heap : Registry) (memory : State) (base : Nat)
    (checked : check allocator data capacity before = .ok (heap, memory, base)) :
    Owned allocator data capacity before ∧ before.memory.valid = true ∧
      heap = Compiler.Extraction.Memory.write before.heap data.allocation none ∧
      memory = erase before.memory data.allocation ∧
      ∃ cell, before.memory.heap.lookup data.allocation = some cell ∧ base = cell.base := by
  unfold check at checked
  split at checked
  · contradiction
  · rename_i offset
    have root : data.offset = 0 := Decidable.of_not_not offset
    cases released : Compiler.Extraction.Memory.release before.heap allocator data.allocation with
    | error fault => simp [released, Except.mapError, bind, Except.bind] at checked
    | ok registry =>
      simp only [released, Except.mapError, bind, Except.bind] at checked
      cases stored : before.heap data.allocation with
      | none => simp [stored] at checked
      | some allocation =>
        rcases allocation with ⟨brand, block⟩
        have branded : brand = allocator := by
          by_cases same : brand = allocator
          · exact same
          · simp [Compiler.Extraction.Memory.release, stored, same] at released
        subst brand
        cases block with
        | item value => simp [stored] at checked
        | arguments values => simp [stored] at checked
        | bytes length => simp [stored] at checked
        | representatives cells =>
          simp only [stored] at checked
          cases found : before.memory.heap.lookup data.allocation with
          | none => simp [found] at checked
          | some cell =>
            simp only [found] at checked
            cases physical : releaseOwned before.memory data.allocation (Backing.type capacity) with
            | error fault => simp [physical] at checked
            | ok after =>
              simp only [physical] at checked
              obtain ⟨valid, owner, ownerFound, typed, writable, persistent, erased⟩ :=
                releaseOwned_shape before.memory after data.allocation (Backing.type capacity) physical
              have same := Option.some.inj (found.symm.trans ownerFound)
              subst owner
              cases Except.ok.inj checked
              exact ⟨⟨root, ⟨cells, stored⟩, cell, found, typed, writable, persistent⟩, valid,
                Compiler.Extraction.Memory.release_success _ _ _ _ released, erased, cell, rfl, rfl⟩

structure Post (id : Nat) (before after : Session σ) : Prop where
  valid : Valid after
  nextId : after.memory.nextId = before.memory.nextId
  nextAddress : after.memory.nextAddress = before.memory.nextAddress
  registry : after.heap = Compiler.Extraction.Memory.write before.heap id none
  memory : after.memory = erase before.memory id

theorem erased_post (before : Session σ) (id : Nat) (effects : σ) (valid : Valid before) :
    Post id before ⟨Compiler.Extraction.Memory.write before.heap id none, erase before.memory id, effects⟩ :=
  ⟨⟨erase_preserves_valid _ _ valid.memory, Compiler.Extraction.Memory.Arguments.related_erase _ _ _ valid.related,
    valid.injected.erased _⟩, rfl, rfl, rfl, rfl⟩

/-- Initial ownership, not a successful-free or final-state premise, supplies
the exact release, full capacity byte extent and reached allocator effects. -/
theorem verified (external : External σ) (allocator : Nat) (data : Address) (capacity : Nat)
    (before : Session σ) (valid : Valid before) (owned : Owned allocator data capacity before) (nonempty : capacity ≠ 0) :
    ∃ cell after, before.memory.heap.lookup data.allocation = some cell ∧
      run external allocator data capacity before = (.ok (), after) ∧ Post data.allocation before after ∧
      after.effects = external allocator cell.base (capacity * 32) 8 before.effects ∧
      0 < cell.base ∧ cell.base % 8 = 0 ∧ cell.base + capacity * 32 ≤ addressLimit := by
  obtain ⟨base, checked⟩ := checked_of_owned allocator data capacity before valid owned
  obtain ⟨_, _, _, _, cell, found, same⟩ := check_shape allocator data capacity before _ _ base checked
  subst base
  obtain ⟨_, _, owner, ownerFound, typed, _, _⟩ := owned
  have equal := Option.some.inj (found.symm.trans ownerFound)
  subst owner
  obtain ⟨_, positive, layout, shaped, aligned, bounded, limit⟩ := valid_lookup before.memory data.allocation cell valid.memory found
  rw [typed, layout_checked] at shaped
  cases Option.some.inj shaped
  dsimp only at aligned bounded
  refine ⟨cell, ⟨_, _, external allocator cell.base (capacity * 32) 8 before.effects⟩, found, ?_,
    erased_post before data.allocation _ valid, rfl, positive, aligned, by omega⟩
  simp only [run, if_neg nonempty, checked]

theorem rejected (external : External σ) (allocator : Nat) (data : Address) (capacity : Nat) (before : Session σ)
    (fault : Fault) (nonempty : capacity ≠ 0) (rejection : check allocator data capacity before = .error fault) :
    run external allocator data capacity before = (.error fault, before) := by
  simp only [run, if_neg nonempty, rejection]

end Compiler.Extraction.RepresentativeArray.Backing.Release
