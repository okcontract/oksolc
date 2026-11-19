/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeFallbackProofs

namespace Compiler.Extraction.RepresentativeArray.Backing.Fallback
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- Every outcome preserves validity and unrelated allocations. This includes
OOM, malformed allocator responses, unreadable items and partial copying or
publication. No successful relocation is supplied as a premise. -/
theorem storage (runtimeSafety : Bool) (allocate : Registry.Allocate σ) (release : Release.External σ)
    (allocator lifetime oldCapacity capacity : Nat) (oldData : Address) (before : Session σ) (owner : Allocation)
    (valid : Valid before) (nonempty : capacity ≠ 0)
    (ownerFound : before.memory.heap.lookup lifetime = some owner) (ownerType : owner.type = Owner.viewType runtimeSafety) :
    let after := (run allocate release allocator (Owner.headerAddress ⟨lifetime, 0⟩) oldData oldCapacity capacity before).2
    Valid after ∧
      (∀ query, query ≠ oldData.allocation → query ≠ before.memory.nextId → after.heap query = before.heap query) ∧
      (∀ query, query ≠ oldData.allocation → query ≠ before.memory.nextId → query ≠ lifetime →
        after.memory.heap.lookup query = before.memory.heap.lookup query) := by
  have reserved := Registry.storage allocate allocator capacity before valid
  have frame := Registry.frame allocate allocator capacity before valid
  have older := (valid_lookup before.memory lifetime owner valid.memory ownerFound).1
  unfold run
  generalize allocated : Registry.run allocate allocator capacity before = result at reserved frame ⊢
  rcases result with ⟨outcome, reached⟩
  cases outcome with
  | error fault =>
    cases fault <;> exact ⟨reserved.1, fun query _ apart => (frame query apart).1,
      fun query _ apart _ => (frame query apart).2⟩
  | ok target =>
    cases target with
    | none => exact ⟨reserved.1, fun query _ apart => (frame query apart).1,
        fun query _ apart _ => (frame query apart).2⟩
    | some data =>
      obtain ⟨rfl, _, ⟨cells, registered⟩, _⟩ := Registry.success_owned allocate allocator capacity before reached data valid nonempty allocated
      have relocated := Relocation.storage runtimeSafety release allocator lifetime oldCapacity capacity allocator oldData
        ⟨before.memory.nextId, 0⟩ reached owner reserved.1 ((frame lifetime (by omega)).2.trans ownerFound) ownerType cells registered
      exact ⟨relocated.1, fun query oldApart newApart => (relocated.2.2.2.1 query oldApart).trans (frame query newApart).1,
        fun query oldApart newApart ownerApart => (relocated.2.2.2.2 query oldApart newApart ownerApart).trans (frame query newApart).2⟩

/-- The independent parent's complete allocation and offset view survive all
allocation-branch outcomes, even when a bad saved release view aliases it. -/
theorem parent_borrow (runtimeSafety : Bool) (allocate : Registry.Allocate σ) (release : Release.External σ)
    (allocator lifetime oldCapacity capacity : Nat) (oldData : Address) (before : Session σ) (owner : Allocation)
    (valid : Valid before) (nonempty : capacity ≠ 0)
    (ownerFound : before.memory.heap.lookup lifetime = some owner) (ownerType : owner.type = Owner.viewType runtimeSafety)
    (parent : WordArray.View) (values : List (BitVec 32)) (extent : Nat) (cell : Allocation)
    (found : before.memory.heap.lookup parent.allocation = some cell) (typed : cell.type = .array extent WordArray.word)
    (represented : WordArray.Represents before.memory parent values) :
    let after := (run allocate release allocator (Owner.headerAddress ⟨lifetime, 0⟩) oldData oldCapacity capacity before).2.memory
    after.heap.lookup parent.allocation = some cell ∧ WordArray.Represents after parent values := by
  have reserved := Registry.storage allocate allocator capacity before valid
  have frame := Registry.frame allocate allocator capacity before valid
  have kept := Registry.parent_borrow allocate allocator capacity before valid parent values cell found represented
  have older := (valid_lookup before.memory lifetime owner valid.memory ownerFound).1
  unfold run
  generalize allocated : Registry.run allocate allocator capacity before = result at reserved frame kept ⊢
  rcases result with ⟨outcome, reached⟩
  cases outcome with
  | error fault => cases fault <;> exact ⟨kept.1, kept.2.1⟩
  | ok target =>
    cases target with
    | none => exact ⟨kept.1, kept.2.1⟩
    | some data =>
      obtain ⟨_, _, ⟨cells, registered⟩, targetCell, targetFound, targetType, _, _⟩ :=
        Registry.success_owned allocate allocator capacity before reached data valid nonempty allocated
      exact Relocation.parent_borrow runtimeSafety release allocator lifetime oldCapacity capacity allocator capacity oldData data
        reached owner targetCell reserved.1 ((frame lifetime (by omega)).2.trans ownerFound) ownerType targetFound targetType cells registered
        parent values extent cell kept.1 typed kept.2.1

/-- The fresh reservation and actual relocation retain the containing owner
shape, including partial failures. No final owner is a premise. -/
theorem owner_shape (runtimeSafety : Bool) (allocate : Registry.Allocate σ) (release : Release.External σ)
    (allocator lifetime oldCapacity capacity : Nat) (oldData : Address) (before : Session σ) (owner : Allocation)
    (valid : Valid before) (nonempty : capacity ≠ 0)
    (ownerFound : before.memory.heap.lookup lifetime = some owner) (ownerType : owner.type = Owner.viewType runtimeSafety) :
    ∃ updated, (run allocate release allocator (Owner.headerAddress ⟨lifetime, 0⟩) oldData oldCapacity capacity before).2.memory.heap.lookup lifetime = some updated ∧
      owner.SameShape updated := by
  have reserved := Registry.storage allocate allocator capacity before valid
  have frame := Registry.frame allocate allocator capacity before valid
  have older := (valid_lookup before.memory lifetime owner valid.memory ownerFound).1
  unfold run
  generalize allocated : Registry.run allocate allocator capacity before = result at reserved frame ⊢
  rcases result with ⟨outcome, reached⟩
  have found := (frame lifetime (by omega)).2.trans ownerFound
  cases outcome with
  | error fault => cases fault <;> exact ⟨owner, found, Allocation.SameShape.refl owner⟩
  | ok target => cases target with
    | none => exact ⟨owner, found, Allocation.SameShape.refl owner⟩
    | some data =>
      obtain ⟨rfl, _, ⟨cells, registered⟩, _⟩ := Registry.success_owned allocate allocator capacity before reached data valid nonempty allocated
      exact Relocation.owner_shape runtimeSafety release allocator lifetime oldCapacity capacity allocator oldData
        ⟨before.memory.nextId, 0⟩ reached owner reserved.1 found ownerType cells registered

end Compiler.Extraction.RepresentativeArray.Backing.Fallback
