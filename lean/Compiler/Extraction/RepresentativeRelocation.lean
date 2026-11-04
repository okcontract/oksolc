/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeRegisteredPublication

namespace Compiler.Extraction.RepresentativeArray.Backing.Relocation
open Compiler.ZigAir.Memory
open Compiler.Extraction.Memory.Arguments.Normalization

/-- The shared reached release/publication suffix. Publication starts only
after successful release and retains its own reached store prefix. -/
def finish (release : Release.External σ) (allocator : Nat) (header oldData data : Address)
    (oldCapacity capacity : Nat) (before : Session σ) : Except Release.Fault Unit × Session σ :=
  let (freed, afterRelease) := Release.run release allocator oldData oldCapacity before
  match freed with
  | .error fault => (.error fault, afterRelease)
  | .ok () =>
    let (published, afterPublication) := Publication.Registered.run header data capacity afterRelease
    (published.mapError (fun fault => .memory fault), afterPublication)

/-- The reached fallback suffix after new backing was allocated. Read the
current items view, copy its initialized prefix, release the saved allocated
slice, then publish pointer and capacity in source order. Checked precondition
faults retain reached state; they are not native errors or rollback semantics.
The saved old view and new allocation are evaluated caller inputs. -/
def run (release : Release.External σ) (allocator : Nat) (header oldData data : Address)
    (oldCapacity capacity : Nat) (before : Session σ) : Except Release.Fault Unit × Session σ :=
  match readItems before.memory header with
  | .error fault => (.error (.memory fault), before)
  | .ok (.slice declared source length) =>
    if declared ≠ itemsType then (.error (.memory .malformed), before) else
    if (length ≠ 0 ∧ source.offset ≠ 0) ∨ data.offset ≠ 0 then (.error (.memory .memoryValidity), before) else
    let (copied, afterCopy) := RegisteredCopy.run source.allocation data.allocation length before
    match copied with
    | .error fault => (.error (.memory fault), afterCopy)
    | .ok () => finish release allocator header oldData data oldCapacity capacity afterCopy
  | .ok _ => (.error (.memory .malformed), before)

theorem of_steps (release : Release.External σ) (allocator : Nat) (header oldData data source : Address)
    (oldCapacity capacity length : Nat) (before copied released after : Session σ)
    (loaded : readItems before.memory header = .ok (.slice itemsType source length))
    (sourceRoot : source.offset = 0) (targetRoot : data.offset = 0)
    (copy : RegisteredCopy.run source.allocation data.allocation length before = (.ok (), copied))
    (free : Release.run release allocator oldData oldCapacity copied = (.ok (), released))
    (publish : Publication.Registered.run header data capacity released = (.ok (), after)) :
    run release allocator header oldData data oldCapacity capacity before = (.ok (), after) := by
  simp only [run, loaded, ne_self_iff_false, ↓reduceIte, sourceRoot, targetRoot, and_false, or_self, copy, finish, free, publish, Except.mapError]

/-- Empty copy does not inspect the source sentinel. Release still checks the
saved old capacity, and pointer/capacity publication keeps its source order. -/
theorem empty_source (release : Release.External σ) (allocator : Nat) (header oldData data source : Address)
    (oldCapacity capacity : Nat) (before : Session σ)
    (loaded : readItems before.memory header = .ok (.slice itemsType source 0)) (targetRoot : data.offset = 0) :
    run release allocator header oldData data oldCapacity capacity before =
      finish release allocator header oldData data oldCapacity capacity before := by
  simp only [run, loaded, ne_self_iff_false, false_and, targetRoot, or_self, ↓reduceIte,
    RegisteredCopy.run, RepresentativeArray.Copy.run]

/-- Successful release cannot consume a declared owner allocation. This frame
also applies on an empty no-op or checked rejection, before any publication. -/
theorem release_owner_frame (runtimeSafety : Bool) (release : Release.External σ) (allocator capacity lifetime : Nat)
    (data : Address) (before : Session σ) (cell : Allocation)
    (found : before.memory.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety) :
    (Release.run release allocator data capacity before).2.memory.heap.lookup lifetime = some cell := by
  unfold Release.run
  split
  · exact found
  · cases checked : Release.check allocator data capacity before with
    | error fault => exact found
    | ok result =>
      rcases result with ⟨heap, memory, base⟩
      obtain ⟨owned, _, _, rfl, _⟩ := Release.check_shape allocator data capacity before heap memory base checked
      obtain ⟨backing, backingFound, backingType, _, _⟩ := owned.2.2
      have apart := before.memory.heap.lookup_ne_of_type_ne lifetime data.allocation cell backing found backingFound
        (by simp [typed, backingType, Owner.viewType, Backing.type])
      simpa only [erase_lookup, if_neg apart] using found

theorem finish_storage (runtimeSafety : Bool) (release : Release.External σ) (allocator lifetime oldCapacity capacity : Nat)
    (oldData data : Address) (before : Session σ) (cell : Allocation) (valid : Valid before)
    (found : before.memory.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety) :
    let after := (finish release allocator (Owner.headerAddress ⟨lifetime, 0⟩) oldData data oldCapacity capacity before).2
    Valid after ∧ after.memory.nextId = before.memory.nextId ∧ after.memory.nextAddress = before.memory.nextAddress ∧
      (∀ query, query ≠ oldData.allocation → after.heap query = before.heap query) ∧
      (∀ query, query ≠ oldData.allocation → query ≠ lifetime → after.memory.heap.lookup query = before.memory.heap.lookup query) := by
  have post := Release.run_storage release allocator oldData oldCapacity before valid
  have owner := release_owner_frame runtimeSafety release allocator oldCapacity lifetime oldData before cell found typed
  unfold finish
  generalize executed : Release.run release allocator oldData oldCapacity before = result at post owner ⊢
  rcases result with ⟨outcome, released⟩
  cases outcome with
  | error fault => exact ⟨post.1, post.2.1, post.2.2.1, fun query apart => (post.2.2.2 query apart).1,
      fun query apart _ => (post.2.2.2 query apart).2⟩
  | ok value =>
    cases value
    have published := Publication.Registered.storage runtimeSafety lifetime cell data capacity released post.1 owner typed
    exact ⟨published.1, published.2.2.2.2.1.trans post.2.1, published.2.2.2.2.2.1.trans post.2.2.1,
      fun query apart => by rw [published.2.1]; exact (post.2.2.2 query apart).1,
      fun query apart different => (published.2.2.2.2.2.2 query different).trans (post.2.2.2 query apart).2⟩

theorem storage (runtimeSafety : Bool) (release : Release.External σ) (allocator lifetime oldCapacity capacity targetAllocator : Nat)
    (oldData data : Address) (before : Session σ) (cell : Allocation) (valid : Valid before)
    (found : before.memory.heap.lookup lifetime = some cell) (typed : cell.type = Owner.viewType runtimeSafety)
    (cells : List Storage.Cell) (registered : Compiler.Extraction.Memory.Vector targetAllocator before.heap data.allocation cells) :
    let after := (run release allocator (Owner.headerAddress ⟨lifetime, 0⟩) oldData data oldCapacity capacity before).2
    Valid after ∧ after.memory.nextId = before.memory.nextId ∧ after.memory.nextAddress = before.memory.nextAddress ∧
      (∀ query, query ≠ oldData.allocation → after.heap query = before.heap query) ∧
      (∀ query, query ≠ oldData.allocation → query ≠ data.allocation → query ≠ lifetime →
        after.memory.heap.lookup query = before.memory.heap.lookup query) := by
  unfold run
  cases loaded : readItems before.memory (Owner.headerAddress ⟨lifetime, 0⟩) with
  | error fault => exact ⟨valid, rfl, rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | ok value =>
    cases value with
    | slice declared source length =>
      dsimp only
      split
      · exact ⟨valid, rfl, rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
      · split
        · exact ⟨valid, rfl, rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
        · have copied := RegisteredCopy.storage source.allocation data.allocation length targetAllocator cells before valid registered
          generalize executed : RegisteredCopy.run source.allocation data.allocation length before = result at copied ⊢
          rcases result with ⟨outcome, afterCopy⟩
          cases outcome with
          | error fault => exact ⟨copied.1, copied.2.2.2.2.1, copied.2.2.2.2.2.1,
              fun query _ => congrFun copied.2.1 query, fun query _ apart _ => copied.2.2.2.2.2.2 query apart⟩
          | ok value =>
            cases value
            obtain ⟨owner, ownerFound, shape⟩ := copied.2.2.2.1 lifetime cell found
            have finished := finish_storage runtimeSafety release allocator lifetime oldCapacity capacity oldData data afterCopy owner copied.1
              ownerFound (shape.2.1.trans typed)
            refine ⟨finished.1, finished.2.1.trans copied.2.2.2.2.1, finished.2.2.1.trans copied.2.2.2.2.2.1,
              fun query apart => (finished.2.2.2.1 query apart).trans (congrFun copied.2.1 query), ?_⟩
            intro query oldApart newApart ownerApart
            exact (finished.2.2.2.2 query oldApart ownerApart).trans (copied.2.2.2.2.2.2 query newApart)
    | _ => exact ⟨valid, rfl, rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

end Compiler.Extraction.RepresentativeArray.Backing.Relocation
