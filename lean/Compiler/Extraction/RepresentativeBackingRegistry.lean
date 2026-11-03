/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingReleaseFrame
import Compiler.Extraction.ArgumentMemoryAllocation

namespace Compiler.Extraction.RepresentativeArray.Backing.Registry
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Reuse the existing checked allocation outcomes and region allocator. The
logical brand selects the same external allocator used for later release; the
native ExpressionClasses allocator-field correspondence remains a caller task. -/
abbrev Fault := Compiler.Extraction.Memory.Arguments.Allocation.Fault
abbrev Allocate (σ : Type) := Nat → RegionAllocation.Allocator σ

/-- Register fresh backing only after the existing typed reservation succeeds.
The empty representative vector records no initialized descriptors. A collision
retains the already reached typed allocation and private effects; zero capacity
creates no allocation or registry entry, and ordinary OOM remains `ok none`. -/
def run (allocate : Allocate σ) (allocator capacity : Nat) (before : Session σ) :
    Except Fault (Option Address) × Session σ :=
  let ((result, memory), effects) := Backing.reserve before.memory capacity (allocate allocator) before.effects
  let reached : Session σ := { before with memory, effects }
  match result with
  | .error fault => (.error (.memory fault), reached)
  | .ok none => (.ok none, reached)
  | .ok (some data) =>
    if capacity = 0 then (.ok (some data), reached) else
    match Compiler.Extraction.Memory.allocate before.heap allocator data.allocation (.representatives []) true with
    | .error fault => (.error (.registry fault), reached)
    | .ok heap => (.ok (some data), { reached with heap })

theorem empty (allocate : Allocate σ) (allocator : Nat) (before : Session σ) :
    run allocate allocator 0 before = (.ok (some ⟨before.memory.nextId, 0⟩), before) := by
  simp only [run, Backing.reserve, if_neg (by decide : ¬0 ≥ addressLimit)]
  rw [RegionAllocation.reserve_empty before.memory (Backing.type 0) ⟨0, 8⟩ (allocate allocator) before.effects (layout_checked 0) rfl]
  rfl

/-- A real allocator OOM retains its private effects without registering or
materializing backing. This derives the outcome from the initial state. -/
theorem failed (allocate : Allocate σ) (allocator capacity : Nat) (before : Session σ) (effects : σ)
    (valid : before.memory.valid = true) (nonempty : capacity ≠ 0) (size : capacity * 32 < addressLimit)
    (response : allocate allocator (capacity * 32) 8 before.effects = (none, effects)) :
    run allocate allocator capacity before = (.ok none, {before with effects}) := by
  have width : capacity < addressLimit := by omega
  have reserved : Backing.reserve before.memory capacity (allocate allocator) before.effects = ((.ok none, before.memory), effects) := by
    simp only [Backing.reserve, if_neg (Nat.not_le.mpr width)]
    exact RegionAllocation.reserve_failed before.memory (Backing.type capacity) ⟨capacity * 32, 8⟩ (allocate allocator)
      before.effects effects valid (layout_checked capacity) (by dsimp only; omega) size response
  simp only [run, reserved]

/-- Recover the actual region response and lifetime from the shared allocator,
without assuming either final memory or registration. -/
theorem reservation_shape (before : Session σ) (memory : State) (capacity : Nat)
    (allocate : RegionAllocation.Allocator σ) (effects : σ) (data : Address) (nonempty : capacity ≠ 0)
    (reserved : Backing.reserve before.memory capacity allocate before.effects = ((.ok (some data), memory), effects)) :
    ∃ base, data = ⟨before.memory.nextId, 0⟩ ∧ memory = RegionAllocation.extend before.memory (Backing.type capacity) (capacity * 32) base ∧
      allocate (capacity * 32) 8 before.effects = (some base, effects) ∧ memory.valid = true := by
  unfold Backing.reserve at reserved
  split at reserved
  · simp at reserved
  · exact RegionAllocation.reserve_nonempty_success before.memory memory (Backing.type capacity) ⟨capacity * 32, 8⟩
      allocate before.effects effects data (layout_checked capacity) (by dsimp only; omega) reserved

theorem reservation_frame (before : Session σ) (capacity : Nat) (allocate : RegionAllocation.Allocator σ)
    (id : Nat) (apart : id ≠ before.memory.nextId) :
    (Backing.reserve before.memory capacity allocate before.effects).1.2.heap.lookup id = before.memory.heap.lookup id := by
  unfold Backing.reserve
  split
  · rfl
  · exact RegionAllocation.reserve_heap_other before.memory (Backing.type capacity) allocate before.effects id apart

/-- Even a rejected response or an accepted allocation awaiting registration
preserves the original registry injection and argument contents. -/
theorem reservation_valid (before : Session σ) (capacity : Nat) (allocate : RegionAllocation.Allocator σ) (valid : Valid before) :
    let reserved := Backing.reserve before.memory capacity allocate before.effects
    Valid ({ before with memory := reserved.1.2, effects := reserved.2 } : Session σ) := by
  have frame := reservation_frame before capacity allocate
  have fresh := valid.injected.fresh valid.memory
  have shape : before.memory.heap.RetainsShape (Backing.reserve before.memory capacity allocate before.effects).1.2.heap := by
    intro id cell found
    have older := (valid_lookup before.memory id cell valid.memory found).1
    exact ⟨cell, (frame id (by omega)).trans found, Allocation.SameShape.refl _⟩
  have afterValid := Backing.reserve_preserves_valid before.memory capacity allocate before.effects valid.memory
  exact ⟨afterValid, related_allocation_frame before.heap before.memory _ before.memory.nextId valid.related fresh frame,
    valid.injected.retained shape⟩

/-- Registration uses the existing vector tag. It cannot manufacture an
argument payload relation; only the new persistent allocation is injected. -/
theorem vector_write_valid (before : Session σ) (allocator id : Nat) (cell : Allocation) (cells : List Storage.Cell)
    (valid : Valid before) (found : before.memory.heap.lookup id = some cell) (persistent : cell.stack = false) :
    Valid ({ before with heap := Compiler.Extraction.Memory.write before.heap id (some ⟨allocator, .representatives cells⟩) } : Session σ) := by
  refine ⟨valid.memory, ?_, ?_⟩
  · intro owner query values nonempty stored
    have apart : query ≠ id := by intro same; simp [Compiler.Extraction.Memory.write, same] at stored
    exact valid.related owner query values nonempty (by simpa [Compiler.Extraction.Memory.write, apart] using stored)
  · intro query block stored
    by_cases same : query = id
    · subst query; exact ⟨cell, found, persistent⟩
    · exact valid.injected query block (by simpa [Compiler.Extraction.Memory.write, same] using stored)

theorem register_valid (before : Session σ) (allocator id : Nat) (cell : Allocation)
    (valid : Valid before) (found : before.memory.heap.lookup id = some cell) (persistent : cell.stack = false) :
    Valid ({ before with heap := Compiler.Extraction.Memory.write before.heap id (some ⟨allocator, .representatives []⟩) } : Session σ) :=
  vector_write_valid before allocator id cell [] valid found persistent

/-- Initial session validity discharges registry freshness. A real successful
allocation derives exact registered, uninitialized, releasable backing. -/
theorem verified (allocate : Allocate σ) (allocator capacity base : Nat) (before : Session σ) (effects : σ)
    (valid : Valid before) (nonempty : capacity ≠ 0) (size : capacity * 32 < addressLimit)
    (response : allocate allocator (capacity * 32) 8 before.effects = (some base, effects))
    (fits : RegionAllocation.Fits before.memory ⟨capacity * 32, 8⟩ base) :
    ∃ after, run allocate allocator capacity before = (.ok (some ⟨before.memory.nextId, 0⟩), after) ∧
      Valid after ∧ Release.Owned allocator ⟨before.memory.nextId, 0⟩ capacity after ∧
      after.memory = RegionAllocation.extend before.memory (Backing.type capacity) (capacity * 32) base ∧
      after.heap = Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩) ∧
      after.effects = effects := by
  have width : capacity < addressLimit := by omega
  have reserved : Backing.reserve before.memory capacity (allocate allocator) before.effects =
      ((.ok (some ⟨before.memory.nextId, 0⟩), RegionAllocation.extend before.memory (Backing.type capacity) (capacity * 32) base), effects) := by
    simp only [Backing.reserve, if_neg (Nat.not_le.mpr width)]
    exact RegionAllocation.reserve_admitted before.memory (Backing.type capacity) ⟨capacity * 32, 8⟩ base
      (allocate allocator) before.effects effects valid.memory (layout_checked capacity) (by dsimp only; omega) size response fits
  let ready : Session σ := { before with memory := RegionAllocation.extend before.memory (Backing.type capacity) (capacity * 32) base, effects }
  have readyValid : Valid ready := by
    have preserved := reservation_valid before capacity (allocate allocator) valid
    simpa only [reserved] using preserved
  have found : ready.memory.heap.lookup before.memory.nextId = some (RegionAllocation.cell (Backing.type capacity) base) := by
    simp [ready, RegionAllocation.extend_lookup]
  have fresh := valid.injected.fresh valid.memory
  refine ⟨{ ready with heap := Compiler.Extraction.Memory.write before.heap before.memory.nextId (some ⟨allocator, .representatives []⟩) },
    ?_, register_valid ready allocator before.memory.nextId _ readyValid found rfl, ?_, rfl, rfl, rfl⟩
  · simp [run, reserved, nonempty, Compiler.Extraction.Memory.allocate, fresh, ready]
  · exact ⟨rfl, ⟨[], by simp [Compiler.Extraction.Memory.Vector, Compiler.Extraction.Memory.write]⟩,
      RegionAllocation.cell (Backing.type capacity) base, found, rfl, rfl, rfl⟩

end Compiler.Extraction.RepresentativeArray.Backing.Registry
