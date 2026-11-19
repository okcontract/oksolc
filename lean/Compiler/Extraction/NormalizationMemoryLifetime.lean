/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationMemoryContracts

namespace Compiler.Extraction.Memory.Arguments.Normalization
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory.WordArray
open Compiler.Extraction.Cache

theorem released_source (source : View) (original : List NodeId)
    (represented : Represents before source original)
    (post : ReleasePost heap before allocator slice afterHeap after)
    (separate : original ≠ [] → source.allocation ≠ slice.address) :
    Represents after source original := by
  by_cases empty : original = []
  · subst original
    exact ⟨represented.1, fun _ impossible => False.elim (by simp at impossible)⟩
  · exact represented_frame source original represented (post.frame source.allocation (separate empty)).2

structure Taken (allocator : Nat) (sourceView : View) (original : List NodeId)
    (beforeHandle : Handle) (before : Session σ) (slice : ArgumentSlice) (handle : Handle) (after : Session σ) : Prop where
  ready : Ready allocator sourceView original handle after
  values : slice.items = beforeHandle.values
  contents : Represents after.memory (view slice) beforeHandle.values
  live : SliceValid allocator after.heap slice
  detached : handle.owned = none
  separate : original ≠ [] → sourceView.allocation ≠ slice.address
  sameValues : handle.values = beforeHandle.values
  moved : ∀ owned, beforeHandle.owned = some owned → slice = owned ∧ after = before
  freshBorrow : beforeHandle.owned = none → slice.address = before.memory.nextId
  frame : ∀ id cell, before.memory.heap.lookup id = some cell →
    after.memory.heap.lookup id = some cell ∧ after.heap id = before.heap id

/-- Both takeOwned branches, including ordinary duplication OOM, from the
actual initialized handle. Success gives independent caller ownership and
detaches lookup ownership; an owned transfer invokes no external operation. -/
theorem take_refines (external : External σ) (allocator : Nat) (source : View) (original : List NodeId)
    (handle : Handle) (before : Session σ) (ready : Ready allocator source original handle before)
    (admitted : Admitted external) :
    ∃ result after, takeOwned normalizationOwnershipCode external allocator handle before = (result, after) ∧
      match result with
      | .ok (slice, remaining) => Taken allocator source original handle before slice remaining after
      | .error .outOfMemory => handle.owned = none ∧ after.heap = before.heap ∧ after.memory = before.memory ∧
          Ready allocator source original handle after
      | .error _ => False := by
  cases ownership : handle.owned with
  | some owned =>
    have facts := ready.owned owned ownership
    let remaining := { handle with owned := none }
    refine ⟨.ok (owned, remaining), before, ?_, ?_⟩
    · simp only [takeOwned, ownership, normalizationOwnershipCode, ↓reduceIte]; rfl
    · refine ⟨⟨ready.valid, ready.contents, ready.source, ?_, ?_⟩, facts.1, ?_, facts.2.2, rfl,
        fun nonempty => ready.separate nonempty owned ownership, rfl, ?_, ?_, ?_⟩
      · intro slice impossible; cases impossible
      · intro _ slice impossible; cases impossible
      · rw [facts.2.1]; exact ready.contents
      · intro slice same; rw [ownership] at same; cases same; exact ⟨rfl, rfl⟩
      · intro impossible; rw [ownership] at impossible; cases impossible
      · intro id cell found; exact ⟨found, rfl⟩
  | none =>
    obtain ⟨result, heap, memory, effects, duplicated, post⟩ := Duplication.run_total before.heap before.memory allocator
      handle.items handle.values (external.allocate .duplicate before) before.effects ready.valid.memory ready.valid.related ready.contents
      (fun _ => ready.valid.injected.fresh ready.valid.memory)
      (fun nonempty base effects response => admitted .duplicate before handle.values base effects ready.valid.memory nonempty response)
    cases result with
    | none =>
      refine ⟨.error .outOfMemory, ⟨heap, memory, effects⟩, ?_, rfl, post.1, post.2.1, ?_⟩
      · simp only [takeOwned, ownership, duplicated]
      · rcases post with ⟨rfl, rfl, _⟩
        exact ⟨⟨ready.valid.memory, ready.valid.related, ready.valid.injected⟩, ready.contents, ready.source, ready.owned, ready.separate⟩
    | some slice =>
      have valid := duplication_valid before allocator handle.items handle.values slice heap memory effects ready.valid post
      have preserved : Represents memory source original := by
        by_cases empty : original = []
        · subst original
          exact ⟨ready.source.1, fun _ impossible => False.elim (by simp at impossible)⟩
        · have older := Compiler.ZigAir.Memory.WordAllocation.source_older before.memory source original ready.valid.memory ready.source empty
          exact represented_frame source original ready.source (post.frame source.allocation (by omega))
      refine ⟨.ok (slice, handle), ⟨heap, memory, effects⟩, ?_,
        ⟨⟨valid, post.source, preserved, ?_, ?_⟩, ?_, post.copied, post.live, ownership, ?_, rfl, ?_, ?_, ?_⟩⟩
      · simp only [takeOwned, ownership, duplicated]
      · intro owned impossible; rw [ownership] at impossible; cases impossible
      · intro _ owned impossible; rw [ownership] at impossible; cases impossible
      · rw [post.descriptor]
      · intro nonempty
        have older := Compiler.ZigAir.Memory.WordAllocation.source_older before.memory source original ready.valid.memory ready.source nonempty
        rw [post.descriptor]; dsimp only; omega
      · intro owned impossible; rw [ownership] at impossible; cases impossible
      · intro _; rw [post.descriptor]
      · intro id cell found
        have older := (Compiler.ZigAir.Memory.valid_lookup before.memory id cell ready.valid.memory found).1
        have apart : id ≠ before.memory.nextId := by omega
        refine ⟨(post.frame id apart).trans found, ?_⟩
        rw [post.registration]
        split
        · rfl
        · exact write_other _ _ _ _ apart

def Consumed (slice : ArgumentSlice) (state : Session σ) : Prop :=
  slice.items = [] ∨ state.heap slice.address = none ∧ state.memory.heap.lookup slice.address = none

theorem released_consumed (post : ReleasePost heap memory allocator slice after.heap after.memory) : Consumed slice after := by
  by_cases empty : slice.items = []
  · exact Or.inl empty
  · exact Or.inr (post.dead empty)

/-- Lookup destruction consumes only its optional owned allocation; borrowed
input and caller scratch have no owned token to release. -/
theorem deinit_refines (external : External σ) (allocator : Nat) (source : View) (original : List NodeId)
    (handle : Handle) (before : Session σ) (ready : Ready allocator source original handle before) :
    ∃ after, deinitialize normalizationOwnershipCode external allocator handle before = (.ok (), after) ∧
      Valid after ∧ Represents after.memory source original ∧
      (∀ slice, handle.owned = some slice → Consumed slice after) ∧
      (∀ id, (∀ slice, handle.owned = some slice → id ≠ slice.address) →
        after.memory.heap.lookup id = before.memory.heap.lookup id ∧ after.heap id = before.heap id) := by
  cases ownership : handle.owned with
  | none =>
    refine ⟨before, ?_, ready.valid, ready.source, ?_, ?_⟩
    · simp only [deinitialize, ownership]
    · intro slice impossible; cases impossible
    · intro id _; exact ⟨rfl, rfl⟩
  | some slice =>
    obtain ⟨after, freed, valid, post, _⟩ := free_valid external allocator slice before ready.valid (ready.owned slice ownership).2.2
    refine ⟨after, ?_, valid, released_source source original ready.source post (fun nonempty => ready.separate nonempty slice ownership), ?_, ?_⟩
    · simpa only [deinitialize, ownership, normalizationOwnershipCode, ↓reduceIte] using freed
    · intro owned same; cases same; exact released_consumed post
    · intro id separate
      have kept := post.frame id (separate slice rfl)
      exact ⟨kept.2, kept.1⟩

structure Closed (external : External σ) (allocator : Nat) (sourceView : View) (original : List NodeId)
    (exit : NormalizationOwnership.Exit) (handle : Handle) (before : Session σ) (result : Except Failure Outcome) (after : Session σ) : Prop where
  valid : Valid after
  source : Represents after.memory sourceView original
  outcome : match result with
    | .error .outOfMemory => exit ≠ .lookup ∧ handle.owned = none ∧ after.heap = before.heap ∧ after.memory = before.memory
    | .error _ => False
    | .ok .lookup => exit = .lookup ∧ ∀ slice, handle.owned = some slice → Consumed slice after
    | .ok (.transferred slice) => exit = .transfer ∧ slice.items = handle.values ∧
        Represents after.memory (view slice) handle.values ∧ SliceValid allocator after.heap slice ∧
        ∀ owned, handle.owned = some owned → slice = owned
    | .ok .cleaned => exit = .cleanup ∧ (∀ owned, handle.owned = some owned → Consumed owned after) ∧
        ∃ slice remaining reached, takeOwned normalizationOwnershipCode external allocator handle before = (.ok (slice, remaining), reached) ∧
          remaining.owned = none ∧ free external allocator slice reached = (.ok (), after) ∧ Consumed slice after
  frame : ∀ id cell, before.memory.heap.lookup id = some cell →
    (∀ owned, handle.owned = some owned → id ≠ owned.address) →
      after.memory.heap.lookup id = some cell ∧ after.heap id = before.heap id

theorem continue_refines (external : External σ) (allocator : Nat) (source : View) (original : List NodeId)
    (exit : NormalizationOwnership.Exit) (handle : Handle) (before : Session σ)
    (ready : Ready allocator source original handle before) (admitted : Admitted external) :
    ∃ result after, continueWith normalizationOwnershipCode external allocator exit handle before = (result, after) ∧
      Closed external allocator source original exit handle before result after := by
  cases exit with
  | lookup =>
    obtain ⟨after, closed, valid, sourceKept, consumed, frame⟩ := deinit_refines external allocator source original handle before ready
    exact ⟨.ok .lookup, after, by simp only [continueWith, close, closed],
      ⟨valid, sourceKept, ⟨rfl, consumed⟩, fun id _ found apart => ⟨((frame id apart).1).trans found, (frame id apart).2⟩⟩⟩
  | transfer | cleanup =>
    obtain ⟨result, reached, taken, post⟩ := take_refines external allocator source original handle before ready admitted
    cases result with
    | error fault =>
      cases fault with
      | allocation | preparation | release => contradiction
      | outOfMemory =>
        rcases post with ⟨borrowed, sameHeap, sameMemory, afterReady⟩
        all_goals
          refine ⟨.error .outOfMemory, reached, ?_,
            ⟨afterReady.valid, afterReady.source, ⟨by decide, borrowed, sameHeap, sameMemory⟩, ?_⟩⟩
          · simp only [continueWith, taken, close, deinitialize, borrowed]
          · intro id cell found _; exact ⟨by simpa only [sameMemory] using found, congrFun sameHeap id⟩
    | ok pair =>
      rcases pair with ⟨slice, remaining⟩
      all_goals
        first
        | exact ⟨.ok (.transferred slice), reached,
            by simp only [continueWith, taken, close, deinitialize, post.detached],
            ⟨post.ready.valid, post.ready.source, ⟨rfl, post.values, post.contents, post.live,
              fun owned own => (post.moved owned own).1⟩, fun id cell found _ => post.frame id cell found⟩⟩
        | obtain ⟨after, released, valid, releasePost, _⟩ := free_valid external allocator slice reached post.ready.valid post.live
          refine ⟨.ok .cleaned, after, ?_, ⟨valid, released_source source original post.ready.source releasePost post.separate,
            ⟨rfl, ?_, slice, remaining, reached, taken, post.detached, released, released_consumed releasePost⟩, ?_⟩⟩
          · simp only [continueWith, taken, released, close, deinitialize, post.detached]
          · intro owned own
            rw [← (post.moved owned own).1]
            exact released_consumed releasePost
          · intro id cell found notOwned
            have apart : id ≠ slice.address := by
              cases owner : handle.owned with
              | none =>
                rw [post.freshBorrow owner]
                have older := (Compiler.ZigAir.Memory.valid_lookup before.memory id cell ready.valid.memory found).1
                omega
              | some owned => rw [(post.moved owned owner).1]; exact notOwned owned owner
            have old := post.frame id cell found
            have kept := releasePost.frame id apart
            exact ⟨kept.2.trans old.1, kept.1.trans old.2⟩

end Compiler.Extraction.Memory.Arguments.Normalization
