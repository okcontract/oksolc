/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingRegistryFrame
import Compiler.Extraction.RepresentativeArrayCopyProofs

namespace Compiler.Extraction.RepresentativeArray.Backing.RegisteredCopy
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Thread the existing checked descriptor copy through the shared session.
The registry and allocator effects stay at their reached values, including on
partial-copy rejection. Copying does not publish a logical vector or header. -/
def run (source target length : Nat) (before : Session σ) : Except Fault Unit × Session σ :=
  let (result, memory) := RepresentativeArray.Copy.run before.memory source target length
  (result, { before with memory })

/-- A representative registry tag separates the destination from every
registered argument allocation. No unregistered-destination premise is needed. -/
theorem storage (source target length allocator : Nat) (cells : List Storage.Cell)
    (before : Session σ) (valid : Valid before)
    (registered : Compiler.Extraction.Memory.Vector allocator before.heap target cells) :
    let after := (run source target length before).2
    Valid after ∧ after.heap = before.heap ∧ after.effects = before.effects ∧
      before.memory.heap.RetainsShape after.memory.heap ∧
      after.memory.nextId = before.memory.nextId ∧ after.memory.nextAddress = before.memory.nextAddress ∧
      ∀ query, query ≠ target → after.memory.heap.lookup query = before.memory.heap.lookup query := by
  have copied := RepresentativeArray.Copy.run_storage before.memory source target length valid.memory
  refine ⟨⟨copied.1, ?_, valid.injected.retained copied.2.1⟩, rfl, rfl, copied.2.1,
    copied.2.2.1, copied.2.2.2.1, copied.2.2.2.2⟩
  intro owner query values nonempty present
  change before.heap query = some ⟨owner, .arguments values⟩ at present
  have apart : query ≠ target := by
    intro same
    subst query
    rw [registered] at present
    cases present
  obtain ⟨⟨cell, found, typed, writable, persistent⟩, represented⟩ := valid.related owner query values nonempty present
  have frame := copied.2.2.2.2 query apart
  exact ⟨⟨cell, frame.trans found, typed, writable, persistent⟩, represented_frame _ values represented frame⟩

/-- Both old and new full-capacity release permissions survive all copy
outcomes. In particular a partially written destination is still owned. -/
theorem owned (source target length allocator capacity : Nat) (data : Address) (before : Session σ)
    (valid : before.memory.valid = true) (initial : Release.Owned allocator data capacity before) :
    Release.Owned allocator data capacity (run source target length before).2 := by
  obtain ⟨root, registered, cell, found, typed, writable, persistent⟩ := initial
  obtain ⟨updated, lookup, shape⟩ := (RepresentativeArray.Copy.run_storage before.memory source target length valid).2.1
    data.allocation cell found
  exact ⟨root, registered, updated, lookup, shape.2.1.trans typed, shape.2.2.1.trans writable,
    shape.2.2.2.trans persistent⟩

theorem parent_borrow (source target length capacity : Nat) (before : Session σ) (targetCell : Allocation)
    (parent : WordArray.View) (values : List (BitVec 32)) (extent : Nat) (parentCell : Allocation)
    (initial : before.memory.valid = true) (targetFound : before.memory.heap.lookup target = some targetCell)
    (targetType : targetCell.type = Backing.type capacity)
    (parentFound : before.memory.heap.lookup parent.allocation = some parentCell)
    (parentType : parentCell.type = .array extent WordArray.word)
    (represented : WordArray.Represents before.memory parent values) :
    (run source target length before).2.memory.heap.lookup parent.allocation = some parentCell ∧
      WordArray.Represents (run source target length before).2.memory parent values :=
  RepresentativeArray.Copy.run_parent_borrow before.memory source target capacity length targetCell parent values extent parentCell
    initial targetFound targetType parentFound parentType represented

/-- Exact copied fields and session validity follow from initialized source
reads and owned destination capacity. Neither successful copying nor final
descriptor, graph or payload correspondence is supplied as a premise. -/
theorem verified (source target length allocator capacity : Nat) (before : Session σ)
    (valid : Valid before) (destination : Release.Owned allocator ⟨target, 0⟩ capacity before)
    (extent : length ≤ capacity) (separate : length = 0 ∨ source ≠ target)
    (ready : ∀ index, index < length → ∀ slot ∈ expressionSlots,
      ∃ value, Expression.readField before.memory false ⟨source, index * 32⟩ slot.1 = .ok value) :
    ∃ after, run source target length before = (.ok (), after) ∧ Valid after ∧
      Release.Owned allocator ⟨target, 0⟩ capacity after ∧ after.heap = before.heap ∧ after.effects = before.effects ∧
      after.memory.nextId = before.memory.nextId ∧ after.memory.nextAddress = before.memory.nextAddress ∧
      (∀ query, query ≠ target → after.memory.heap.lookup query = before.memory.heap.lookup query) ∧
      (∀ index, index < length → Expression.readFields after.memory false ⟨target, index * 32⟩ =
        Expression.readFields before.memory false ⟨source, index * 32⟩) := by
  have retained := owned source target length allocator capacity ⟨target, 0⟩ before valid.memory destination
  obtain ⟨_, ⟨cells, registered⟩, cell, found, typed, writable, _⟩ := destination
  obtain ⟨memory, executed, _, _, _, _, _, fields⟩ := RepresentativeArray.Copy.run_verified before.memory source target
    capacity length cell valid.memory found typed writable extent separate ready
  have post := storage source target length allocator cells before valid registered
  have lifted : run source target length before = (.ok (), { before with memory }) := by simp only [run, executed]
  rw [lifted] at post retained
  exact ⟨_, lifted, post.1, retained, post.2.1, post.2.2.1, post.2.2.2.2.1, post.2.2.2.2.2.1,
    post.2.2.2.2.2.2, fun index inside => RepresentativeArray.Copy.readFields_eq_of_slots _ _ _ _ (fields index inside)⟩

/-- Preserve the actual descriptor read, including any rejection, when its
complete allocation is framed. This also retains interior slice pointers. -/
theorem read_field_frame (before after : State) (address : Address) (offset : Nat)
    (frame : after.heap.lookup address.allocation = before.heap.lookup address.allocation) :
    Expression.readField after false address offset = Expression.readField before false address offset := by
  unfold Expression.readField
  rw [fieldPointer_eq_of_lookup before after false false Expression.allocationType address offset frame]
  cases selected : fieldPointer before (.pointer (.pointer false false Expression.allocationType) address) offset with
  | error fault => rfl
  | ok pointer =>
    obtain ⟨field, _, rfl⟩ := fieldPointer_address before false false Expression.allocationType address offset pointer selected
    exact load_eq_of_lookup before after false false field ⟨address.allocation, address.offset + offset⟩ frame

/-- Compose the actual registered reservation with copying from the original
initialized source. Freshness, separation and destination ownership come from
reservation, rather than final-state or successful-copy assumptions. The
empty provisional registry vector is deliberately not published as graph data. -/
theorem reserve_verified (allocate : Registry.Allocate σ) (allocator capacity base source length : Nat)
    (before : Session σ) (effects : σ) (sourceCell : Allocation) (valid : Valid before)
    (nonempty : capacity ≠ 0) (size : capacity * 32 < addressLimit) (extent : length ≤ capacity)
    (response : allocate allocator (capacity * 32) 8 before.effects = (some base, effects))
    (fits : RegionAllocation.Fits before.memory ⟨capacity * 32, 8⟩ base)
    (sourceFound : before.memory.heap.lookup source = some sourceCell)
    (ready : ∀ index, index < length → ∀ slot ∈ expressionSlots,
      ∃ value, Expression.readField before.memory false ⟨source, index * 32⟩ slot.1 = .ok value) :
    ∃ reserved after, Registry.run allocate allocator capacity before =
        (.ok (some ⟨before.memory.nextId, 0⟩), reserved) ∧
      run source before.memory.nextId length reserved = (.ok (), after) ∧ Valid after ∧
      Release.Owned allocator ⟨before.memory.nextId, 0⟩ capacity after ∧
      after.heap = Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩) ∧
      after.effects = effects ∧ after.memory.nextId = before.memory.nextId + 1 ∧
      after.memory.nextAddress = max before.memory.nextAddress (base + capacity * 32) ∧
      (∀ query, query ≠ before.memory.nextId → after.memory.heap.lookup query = before.memory.heap.lookup query) ∧
      (∀ index, index < length → Expression.readFields after.memory false ⟨before.memory.nextId, index * 32⟩ =
        Expression.readFields before.memory false ⟨source, index * 32⟩) := by
  obtain ⟨reserved, allocated, validReserved, destination, memory, heap, reached⟩ :=
    Registry.verified allocate allocator capacity base before effects valid nonempty size response fits
  have older := (valid_lookup before.memory source sourceCell valid.memory sourceFound).1
  have frame (query : Nat) (apart : query ≠ before.memory.nextId) :
      reserved.memory.heap.lookup query = before.memory.heap.lookup query := by
    rw [memory, RegionAllocation.extend_lookup, if_neg (Ne.symm apart)]
  have reads (index offset : Nat) := read_field_frame before.memory reserved.memory ⟨source, index * 32⟩ offset (frame source (by omega))
  obtain ⟨after, copied, validAfter, ownedAfter, heapAfter, effectsAfter, nextId, nextAddress, kept, fields⟩ :=
    verified source before.memory.nextId length allocator capacity reserved validReserved destination extent
      (Or.inr (by omega)) (fun index inside slot member => by
        obtain ⟨value, loaded⟩ := ready index inside slot member
        exact ⟨value, (reads index slot.1).trans loaded⟩)
  refine ⟨reserved, after, allocated, copied, validAfter, ownedAfter, heapAfter.trans heap, effectsAfter.trans reached,
    ?_, ?_, fun query apart => (kept query apart).trans (frame query apart), ?_⟩
  · rw [nextId, memory]; rfl
  · rw [nextAddress, memory]; rfl
  · intro index inside
    exact (fields index inside).trans (RepresentativeArray.Copy.readFields_eq_of_slots _ _ _ _ (fun slot _ => reads index slot.1))

end Compiler.Extraction.RepresentativeArray.Backing.RegisteredCopy
