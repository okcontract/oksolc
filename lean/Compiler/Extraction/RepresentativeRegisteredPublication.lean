/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeBackingCopy
import Compiler.Extraction.RepresentativePublicationProofs

namespace Compiler.Extraction.RepresentativeArray.Publication.Registered
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Lift the existing ordered pointer/capacity stores into the shared session.
No logical vector contents or ownership transfer is invented by these stores. -/
def run (header data : Address) (capacity : Nat) (before : Session σ) : Except Fault Unit × Session σ :=
  let (published, memory) := Publication.run before.memory header data capacity
  (published, { before with memory })

theorem storage (runtimeSafety : Bool) (lifetime : Nat) (cell : Allocation) (data : Address) (capacity : Nat)
    (before : Session σ) (valid : Valid before) (found : before.memory.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) :
    let after := (run (Owner.headerAddress ⟨lifetime, 0⟩) data capacity before).2
    Valid after ∧ after.heap = before.heap ∧ after.effects = before.effects ∧
      before.memory.heap.RetainsShape after.memory.heap ∧
      after.memory.nextId = before.memory.nextId ∧ after.memory.nextAddress = before.memory.nextAddress ∧
      ∀ query, query ≠ lifetime → after.memory.heap.lookup query = before.memory.heap.lookup query := by
  have post := Publication.run_storage before.memory (Owner.headerAddress ⟨lifetime, 0⟩) data capacity valid.memory
  refine ⟨⟨post.1, ?_, valid.injected.retained post.2.1⟩, rfl, rfl, post.2.1, post.2.2.1, post.2.2.2.1, post.2.2.2.2⟩
  intro allocator query values nonempty registered
  obtain ⟨⟨parent, parentFound, parentType, writable, persistent⟩, represented⟩ := valid.related allocator query values nonempty registered
  have apart := before.memory.heap.lookup_ne_of_type_ne query lifetime parent cell parentFound found
    (by simp [parentType, typed, Owner.viewType])
  have frame := post.2.2.2.2 query apart
  exact ⟨⟨parent, frame.trans parentFound, parentType, writable, persistent⟩, represented_frame _ values represented frame⟩

theorem owned (header data : Address) (capacity allocator extent : Nat) (backing : Address) (before : Session σ)
    (valid : before.memory.valid = true) (initial : Backing.Release.Owned allocator backing extent before) :
    Backing.Release.Owned allocator backing extent (run header data capacity before).2 := by
  obtain ⟨root, registered, cell, found, typed, writable, persistent⟩ := initial
  obtain ⟨updated, lookup, shape⟩ := (Publication.run_storage before.memory header data capacity valid).2.1 backing.allocation cell found
  exact ⟨root, registered, updated, lookup, shape.2.1.trans typed, shape.2.2.1.trans writable, shape.2.2.2.trans persistent⟩

theorem verified (runtimeSafety : Bool) (lifetime : Nat) (cell : Allocation) (oldData data : Address) (length capacity : Nat)
    (before : Session σ) (valid : Valid before) (found : before.memory.heap.lookup lifetime = some cell)
    (typed : cell.type = Owner.viewType runtimeSafety) (writable : cell.writable = true)
    (loaded : readItems before.memory (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType oldData length))
    (bounded : capacity < addressLimit) :
    ∃ after, run (Owner.headerAddress ⟨lifetime, 0⟩) data capacity before = (.ok (), after) ∧ Valid after ∧
      after.heap = before.heap ∧ after.effects = before.effects ∧ before.memory.heap.RetainsShape after.memory.heap ∧
      after.memory.nextId = before.memory.nextId ∧ after.memory.nextAddress = before.memory.nextAddress ∧
      readHeader after.memory (Owner.headerAddress ⟨lifetime, 0⟩) =
        .ok (.slice itemsType data length, .scalar (.int false 64 capacity)) ∧
      (∀ query, query ≠ lifetime → after.memory.heap.lookup query = before.memory.heap.lookup query) := by
  obtain ⟨memory, executed, _, _, header, _, _, _⟩ :=
    Publication.run_verified runtimeSafety before.memory lifetime cell oldData data length capacity valid.memory found typed writable loaded bounded
  have lifted : run (Owner.headerAddress ⟨lifetime, 0⟩) data capacity before = (.ok (), { before with memory }) := by
    simp only [run, executed]
  have post := storage runtimeSafety lifetime cell data capacity before valid found typed
  rw [lifted] at post
  exact ⟨_, lifted, post.1, post.2.1, post.2.2.1, post.2.2.2.1, post.2.2.2.2.1, post.2.2.2.2.2.1, header, post.2.2.2.2.2.2⟩

end Compiler.Extraction.RepresentativeArray.Publication.Registered
