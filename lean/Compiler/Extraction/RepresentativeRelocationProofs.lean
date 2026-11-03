/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRelocation

namespace Compiler.Extraction.RepresentativeArray.Backing.Relocation
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- The same reached execution copies initialized fields, frees the saved full
old extent and publishes the new header. Source/target ownership and initialized
source reads are initial conditions; all intermediate and final states, release
permission at the use site, readback and stale-lifetime rejection are derived. -/
theorem verified (runtimeSafety : Bool) (release : Release.External σ)
    (allocator lifetime source target oldCapacity capacity length : Nat) (before : Session σ) (owner : Allocation)
    (valid : Valid before) (ownerFound : before.memory.heap.lookup lifetime = some owner)
    (ownerType : owner.type = Owner.viewType runtimeSafety) (ownerWritable : owner.writable = true)
    (sourceOwned : Release.Owned allocator ⟨source, 0⟩ oldCapacity before)
    (targetOwned : Release.Owned allocator ⟨target, 0⟩ capacity before)
    (nonempty : oldCapacity ≠ 0) (separate : source ≠ target) (extent : length ≤ capacity)
    (loaded : readItems before.memory (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType ⟨source, 0⟩ length))
    (ready : ∀ index, index < length → ∀ slot ∈ expressionSlots,
      ∃ value, Expression.readField before.memory false ⟨source, index * 32⟩ slot.1 = .ok value) :
    ∃ oldCell after, before.memory.heap.lookup source = some oldCell ∧
      run release allocator (Owner.headerAddress ⟨lifetime, 0⟩) ⟨source, 0⟩ ⟨target, 0⟩ oldCapacity capacity before = (.ok (), after) ∧
      Valid after ∧ Release.Owned allocator ⟨target, 0⟩ capacity after ∧
      after.heap = Compiler.Extraction.Memory.write before.heap source none ∧
      after.effects = release allocator oldCell.base (oldCapacity * 32) 8 before.effects ∧
      after.memory.nextId = before.memory.nextId ∧ after.memory.nextAddress = before.memory.nextAddress ∧
      after.memory.heap.lookup source = none ∧
      readHeader after.memory (Owner.headerAddress ⟨lifetime, 0⟩) =
        .ok (.slice itemsType ⟨target, 0⟩ length, .scalar (.int false 64 capacity)) ∧
      (∀ index, index < length → Expression.readFields after.memory false ⟨target, index * 32⟩ =
        Expression.readFields before.memory false ⟨source, index * 32⟩) ∧
      (∀ query, query ≠ source → query ≠ target → query ≠ lifetime → after.memory.heap.lookup query = before.memory.heap.lookup query) := by
  obtain ⟨copied, copy, copyValid, destination, copyHeap, copyEffects, copyId, copyAddress, copyFrame, fields⟩ :=
    RegisteredCopy.verified source target length allocator capacity before valid targetOwned extent (Or.inr separate) ready
  have sourceAtCopy := RegisteredCopy.owned source target length allocator oldCapacity ⟨source, 0⟩ before valid.memory sourceOwned
  rw [copy] at sourceAtCopy
  obtain ⟨_, _, oldCell, oldFound, oldType, _, _⟩ := sourceOwned
  obtain ⟨_, _, targetCell, targetFound, targetType, _, _⟩ := targetOwned
  have ownerSource := before.memory.heap.lookup_ne_of_type_ne lifetime source owner oldCell ownerFound oldFound
    (by simp [ownerType, oldType, Owner.viewType, Backing.type])
  have ownerTarget := before.memory.heap.lookup_ne_of_type_ne lifetime target owner targetCell ownerFound targetFound
    (by simp [ownerType, targetType, Owner.viewType, Backing.type])
  have bounded : capacity < addressLimit := by
    obtain ⟨_, positive, layout, shaped, _, size, _⟩ := valid_lookup before.memory target targetCell valid.memory targetFound
    rw [targetType, layout_checked] at shaped
    cases Option.some.inj shaped
    dsimp only at size
    omega
  obtain ⟨freedCell, released, releasedFound, free, releasePost, releaseEffects, _⟩ :=
    Release.verified release allocator ⟨source, 0⟩ oldCapacity copied copyValid sourceAtCopy nonempty
  have sameOld : freedCell = oldCell := Option.some.inj (releasedFound.symm.trans ((copyFrame source separate).trans oldFound))
  subst freedCell
  have headerFrame := (releasePost.frame lifetime ownerSource).2.trans (copyFrame lifetime ownerTarget)
  have releasedOwner : released.memory.heap.lookup lifetime = some owner := headerFrame.trans ownerFound
  have releasedItems : readItems released.memory (Owner.headerAddress ⟨lifetime, 0⟩) = .ok (.slice itemsType ⟨source, 0⟩ length) :=
    (readField_eq_of_lookup before.memory released.memory (Owner.headerAddress ⟨lifetime, 0⟩) itemsOffset headerFrame).trans loaded
  obtain ⟨after, publish, finalValid, finalHeap, finalEffects, _, finalId, finalAddress, header, finalFrame⟩ :=
    Publication.Registered.verified runtimeSafety lifetime owner ⟨source, 0⟩ ⟨target, 0⟩ length capacity released
      releasePost.valid releasedOwner ownerType ownerWritable releasedItems bounded
  have targetAtRelease : Release.Owned allocator ⟨target, 0⟩ capacity released := by
    obtain ⟨root, ⟨cells, vector⟩, cell, found, typed, writable, persistent⟩ := destination
    have frame := releasePost.frame target (Ne.symm separate)
    exact ⟨root, ⟨cells, frame.1.trans vector⟩, cell, frame.2.trans found, typed, writable, persistent⟩
  have targetAfter := Publication.Registered.owned (Owner.headerAddress ⟨lifetime, 0⟩) ⟨target, 0⟩ capacity allocator capacity
    ⟨target, 0⟩ released releasePost.valid.memory targetAtRelease
  rw [publish] at targetAfter
  have targetFrame := (finalFrame target (Ne.symm ownerTarget)).trans (releasePost.frame target (Ne.symm separate)).2
  refine ⟨oldCell, after, oldFound, of_steps release allocator _ _ _ _ oldCapacity capacity length before copied released after
    loaded rfl rfl copy free publish, finalValid, targetAfter, ?_, ?_, finalId.trans (releasePost.nextId.trans copyId),
    finalAddress.trans (releasePost.nextAddress.trans copyAddress), ?_, header, ?_, ?_⟩
  · rw [finalHeap, releasePost.registry, copyHeap]
  · rw [finalEffects, releaseEffects, copyEffects]
  · exact (finalFrame source (Ne.symm ownerSource)).trans releasePost.dead.2
  · intro index inside
    exact (RepresentativeArray.Copy.readFields_eq_of_slots copied.memory after.memory ⟨target, index * 32⟩ ⟨target, index * 32⟩
      (fun slot _ => RegisteredCopy.read_field_frame _ _ _ _ targetFrame)).trans (fields index inside)
  · intro query oldApart newApart ownerApart
    exact (finalFrame query ownerApart).trans (((releasePost.frame query oldApart).2).trans (copyFrame query newApart))

end Compiler.Extraction.RepresentativeArray.Backing.Relocation
