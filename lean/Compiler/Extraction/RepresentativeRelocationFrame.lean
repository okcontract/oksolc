/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRelocationProofs

namespace Compiler.Extraction.RepresentativeArray.Backing.Relocation
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

theorem finish_parent_borrow (runtimeSafety : Bool) (release : Release.External σ) (allocator lifetime oldCapacity capacity : Nat)
    (oldData data : Address) (before : Session σ) (owner : Allocation) (valid : Valid before)
    (ownerFound : before.memory.heap.lookup lifetime = some owner) (ownerType : owner.type = Owner.viewType runtimeSafety)
    (parent : WordArray.View) (values : List (BitVec 32)) (extent : Nat) (cell : Allocation)
    (found : before.memory.heap.lookup parent.allocation = some cell) (typed : cell.type = .array extent WordArray.word)
    (represented : WordArray.Represents before.memory parent values) :
    let after := (finish release allocator (Owner.headerAddress ⟨lifetime, 0⟩) oldData data oldCapacity capacity before).2.memory
    after.heap.lookup parent.allocation = some cell ∧ WordArray.Represents after parent values := by
  have released := Release.parent_borrow release allocator oldData oldCapacity before parent values extent cell found typed represented
  have post := Release.run_storage release allocator oldData oldCapacity before valid
  have keptOwner := release_owner_frame runtimeSafety release allocator oldCapacity lifetime oldData before owner ownerFound ownerType
  unfold finish
  generalize executed : Release.run release allocator oldData oldCapacity before = result at released post keptOwner ⊢
  rcases result with ⟨outcome, afterRelease⟩
  cases outcome with
  | error fault => exact ⟨released.1, released.2.1⟩
  | ok value =>
    cases value
    exact Publication.run_parent_borrow runtimeSafety afterRelease.memory lifetime owner data capacity parent values extent cell
      post.1.memory keptOwner ownerType released.1 typed released.2.1

/-- Every reached prefix preserves the complete independent parent allocation,
including offset views and surrounding words. Release rejection needs no
matching-brand premise, and a later publication rejection cannot erase this
frame. No assertion about final graph correspondence is used. -/
theorem parent_borrow (runtimeSafety : Bool) (release : Release.External σ)
    (allocator lifetime oldCapacity capacity targetAllocator targetExtent : Nat) (oldData data : Address)
    (before : Session σ) (owner targetCell : Allocation) (valid : Valid before)
    (ownerFound : before.memory.heap.lookup lifetime = some owner) (ownerType : owner.type = Owner.viewType runtimeSafety)
    (targetFound : before.memory.heap.lookup data.allocation = some targetCell) (targetType : targetCell.type = Backing.type targetExtent)
    (cells : List Storage.Cell) (registered : Compiler.Extraction.Memory.Vector targetAllocator before.heap data.allocation cells)
    (parent : WordArray.View) (values : List (BitVec 32)) (extent : Nat) (cell : Allocation)
    (found : before.memory.heap.lookup parent.allocation = some cell) (typed : cell.type = .array extent WordArray.word)
    (represented : WordArray.Represents before.memory parent values) :
    let after := (run release allocator (Owner.headerAddress ⟨lifetime, 0⟩) oldData data oldCapacity capacity before).2.memory
    after.heap.lookup parent.allocation = some cell ∧ WordArray.Represents after parent values := by
  unfold run
  cases loaded : readItems before.memory (Owner.headerAddress ⟨lifetime, 0⟩) with
  | error fault => exact ⟨found, represented⟩
  | ok value =>
    cases value with
    | slice declared source length =>
      dsimp only
      split
      · exact ⟨found, represented⟩
      · split
        · exact ⟨found, represented⟩
        · have copied := RegisteredCopy.storage source.allocation data.allocation length targetAllocator cells before valid registered
          have keptParent := RegisteredCopy.parent_borrow source.allocation data.allocation length targetExtent before targetCell
            parent values extent cell valid.memory targetFound targetType found typed represented
          generalize executed : RegisteredCopy.run source.allocation data.allocation length before = result at copied keptParent ⊢
          rcases result with ⟨outcome, afterCopy⟩
          cases outcome with
          | error fault => exact keptParent
          | ok value =>
            cases value
            obtain ⟨updated, updatedFound, shape⟩ := copied.2.2.2.1 lifetime owner ownerFound
            exact finish_parent_borrow runtimeSafety release allocator lifetime oldCapacity capacity oldData data afterCopy updated copied.1
              updatedFound (shape.2.1.trans ownerType) parent values extent cell keptParent.1 typed keptParent.2
    | _ => exact ⟨found, represented⟩

/-- Copy, release and publication retain the containing owner's allocation
shape on every reached outcome. Its mutable fields are not asserted unchanged. -/
theorem owner_shape (runtimeSafety : Bool) (release : Release.External σ)
    (allocator lifetime oldCapacity capacity targetAllocator : Nat) (oldData data : Address)
    (before : Session σ) (cell : Allocation) (valid : Valid before)
    (found : before.memory.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (cells : List Storage.Cell) (registered : Compiler.Extraction.Memory.Vector targetAllocator before.heap data.allocation cells) :
    ∃ updated, (run release allocator (Owner.headerAddress ⟨lifetime, 0⟩) oldData data oldCapacity capacity before).2.memory.heap.lookup lifetime = some updated ∧
      cell.SameShape updated := by
  have initial : ∃ updated, before.memory.heap.lookup lifetime = some updated ∧ cell.SameShape updated :=
    ⟨cell, found, Allocation.SameShape.refl cell⟩
  unfold run
  cases loaded : readItems before.memory (Owner.headerAddress ⟨lifetime, 0⟩) with
  | error fault => exact initial
  | ok value => cases value with
    | slice declared source length =>
      dsimp only
      split
      · exact initial
      · split
        · exact initial
        · have copied := RegisteredCopy.storage source.allocation data.allocation length targetAllocator cells before valid registered
          generalize executed : RegisteredCopy.run source.allocation data.allocation length before = result at copied ⊢
          rcases result with ⟨outcome, afterCopy⟩
          obtain ⟨owner, ownerFound, shape⟩ := copied.2.2.2.1 lifetime cell found
          cases outcome with
          | error fault => exact ⟨owner, ownerFound, shape⟩
          | ok value =>
            cases value
            have ownerType := shape.2.1.trans typed
            have kept := release_owner_frame runtimeSafety release allocator oldCapacity lifetime oldData afterCopy owner ownerFound ownerType
            have post := Release.run_storage release allocator oldData oldCapacity afterCopy copied.1
            unfold finish
            generalize released : Release.run release allocator oldData oldCapacity afterCopy = result at kept post ⊢
            rcases result with ⟨outcome, afterRelease⟩
            cases outcome with
            | error fault => exact ⟨owner, kept, shape⟩
            | ok value =>
              cases value
              have published := Publication.Registered.storage runtimeSafety lifetime owner data capacity afterRelease post.1 kept ownerType
              obtain ⟨updated, finalFound, finalShape⟩ := published.2.2.2.1 lifetime owner kept
              exact ⟨updated, finalFound, shape.trans finalShape⟩
    | _ => exact initial

end Compiler.Extraction.RepresentativeArray.Backing.Relocation
