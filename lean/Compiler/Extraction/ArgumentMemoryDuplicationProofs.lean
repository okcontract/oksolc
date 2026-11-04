/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.ArgumentMemoryDuplication
import Compiler.Extraction.ArgumentMemoryAllocationProofs
import Compiler.ZigAir.MemoryWordCopyProofs

namespace Compiler.Extraction.Memory.Arguments.Duplication
open Compiler.Algebraic Compiler.Extraction.Storage
open Compiler.ZigAir.Memory Compiler.ZigAir.Memory.WordArray

theorem run_length_rejected (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : WordAllocation.Allocator σ) (effects : σ)
    (different : source.length ≠ items.length) :
    run heap state allocator source items request effects = ((.error (.memory .sourceBounds), heap, state), effects) := by
  simp only [run, if_pos different]

theorem run_empty (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (request : WordAllocation.Allocator σ) (effects : σ) (empty : source.length = 0) :
    run heap state allocator source [] request effects = ((.ok (some ⟨state.nextId, []⟩), heap, state), effects) := by
  simp [run, empty, Allocation.reserve_empty, view, WordCopy.copy, WordCopy.disjoint, WordCopy.copyFrom]

theorem run_allocation_fault (heap registered : Heap) (state allocated : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : WordAllocation.Allocator σ) (effects reached : σ) (fault : Allocation.Fault)
    (length : source.length = items.length)
    (failed : Allocation.reserve heap state allocator items request effects = ((.error fault, registered, allocated), reached)) :
    run heap state allocator source items request effects = ((.error fault, registered, allocated), reached) := by
  simp only [run, length, ne_eq, not_true_eq_false, ↓reduceIte, failed]

theorem run_oom (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : WordAllocation.Allocator σ) (effects reached : σ)
    (valid : state.valid = true) (nonempty : items ≠ []) (represented : Represents state source items)
    (response : request (items.length * 4) effects = (none, reached)) :
    run heap state allocator source items request effects = ((.ok none, heap, state), reached) := by
  simp only [run, represented.1.symm, ne_eq, not_true_eq_false, ↓reduceIte,
    Allocation.reserve_failed heap state allocator items request effects reached valid nonempty source represented response]

/-- With consistent descriptors, duplication retains exactly the allocator's
reached private effects on every allocation/copy outcome. -/
theorem run_reached_effects (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : WordAllocation.Allocator σ) (effects : σ)
    (length : source.length = items.length) :
    (run heap state allocator source items request effects).2 = (Allocation.reserve heap state allocator items request effects).2 := by
  simp only [run, length, ne_eq, not_true_eq_false, ↓reduceIte]
  cases Allocation.reserve heap state allocator items request effects with
  | mk outcome reached =>
    rcases outcome with ⟨result, registered, allocated⟩
    cases result with
    | error fault => rfl
    | ok destination =>
      cases destination with
      | none => rfl
      | some slice =>
        dsimp only
        cases WordCopy.copy allocated source (view slice) with
        | mk result after => cases result <;> rfl

/-- Copying retains the high-water mark of the actual accepted allocation. -/
theorem run_address (heap registered : Heap) (state allocated : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : Compiler.ZigAir.Memory.WordAllocation.Allocator σ)
    (effects reached : σ) (slice : ArgumentSlice) (length : source.length = items.length)
    (reserved : Allocation.reserve heap state allocator items request effects = ((.ok (some slice), registered, allocated), reached)) :
    (run heap state allocator source items request effects).1.2.2.nextAddress = allocated.nextAddress := by
  simp only [run, length, ne_eq, not_true_eq_false, ↓reduceIte, reserved]
  have counter := Compiler.ZigAir.Memory.WordCopy.copy_address allocated source (view slice)
  cases copied : Compiler.ZigAir.Memory.WordCopy.copy allocated source (view slice) with
  | mk result after =>
    rw [copied] at counter
    cases result <;> exact counter

theorem run_preserves_valid (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : WordAllocation.Allocator σ) (effects : σ)
    (valid : state.valid = true) : (run heap state allocator source items request effects).1.2.2.valid = true := by
  unfold run
  split
  · exact valid
  · have allocatedValid := Allocation.reserve_preserves_valid heap state allocator items request effects valid
    cases reserved : Allocation.reserve heap state allocator items request effects with
    | mk outcome reached =>
      rcases outcome with ⟨result, registered, allocated⟩
      rw [reserved] at allocatedValid
      cases result with
      | error fault => exact allocatedValid
      | ok destination =>
        cases destination with
        | none => exact allocatedValid
        | some slice =>
          dsimp only
          have preserved := (WordCopy.copy_storage allocated source (view slice) allocatedValid).1
          cases copied : WordCopy.copy allocated source (view slice) with
          | mk result after =>
            rw [copied] at preserved
            cases result <;> exact preserved

theorem copy_owned (state : Compiler.ZigAir.Memory.State) (source target : View) (id length : Nat)
    (valid : state.valid = true) (owned : Owned state id length) :
    Owned (WordCopy.copy state source target).2 id length :=
  owned_retained state _ id length owned (WordCopy.copy_storage state source target valid).2

/-- Even a copy fault retains the accepted persistent allocation's ownership.
Its initialized payload is not published by this metadata-only theorem. -/
theorem run_allocated_owned (heap registered : Heap) (state allocated : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : WordAllocation.Allocator σ) (effects reached : σ) (slice : ArgumentSlice)
    (length : source.length = items.length) (nonempty : items ≠ [])
    (reserved : Allocation.reserve heap state allocator items request effects = ((.ok (some slice), registered, allocated), reached)) :
    Owned (run heap state allocator source items request effects).1.2.2 slice.address items.length := by
  obtain ⟨base, rfl, rfl, rfl, _, _, valid⟩ :=
    Allocation.reserve_success heap registered state allocated allocator items request effects reached slice nonempty reserved
  have owned := copy_owned _ source (view ⟨state.nextId, items⟩) state.nextId items.length valid
    (Allocation.extend_owned state items.length base)
  simp only [run, length, ne_eq, not_true_eq_false, ↓reduceIte, reserved]
  cases copied : WordCopy.copy (WordAllocation.extend state items.length base) source (view ⟨state.nextId, items⟩) with
  | mk result after =>
    rw [copied] at owned
    cases result <;> exact owned

/-- Copy initializes the registered payload exactly, without sorting, changing
allocator identity, resizing or creating a second logical registration. -/
theorem copy_registered (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (slice : ArgumentSlice) (valid : state.valid = true)
    (owned : Owned state slice.address slice.items.length)
    (registered : heap slice.address = some ⟨allocator, .arguments slice.items⟩)
    (others : Related (write heap slice.address none) state) (represented : Represents state source slice.items)
    (separate : WordCopy.disjoint source (view slice) = true) :
    ∃ after, WordCopy.copy state source (view slice) = (.ok (), after) ∧ after.valid = true ∧
      Related heap after ∧ Owned after slice.address slice.items.length ∧ Represents after source slice.items ∧
      Represents after (view slice) slice.items ∧ Frame (view slice) state after := by
  obtain ⟨after, copied, afterValid, _, preserved, initialized, frame⟩ := WordCopy.copy_refines state source (view slice) slice.items
    valid (owned_writable state slice.address slice.items.length owned) represented represented.1.symm separate
  have retained := copy_owned state source (view slice) slice.address slice.items.length valid owned
  rw [copied] at retained
  have related := related_publish heap state after allocator (view slice) slice.items others frame.heapFrame retained rfl initialized
  have unchanged : write heap slice.address (some ⟨allocator, .arguments slice.items⟩) = heap := by
    funext id
    by_cases same : id = slice.address
    · subst id; simp [write, registered]
    · simp [write, same]
  change Related (write heap slice.address (some ⟨allocator, .arguments slice.items⟩)) after at related
  rw [unchanged] at related
  exact ⟨after, copied, afterValid, related, retained, preserved, initialized, frame⟩

theorem empty_post (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat) (source : View)
    (valid : state.valid = true) (related : Related heap state) (represented : Represents state source []) :
    Post heap state allocator source [] ⟨state.nextId, []⟩ heap state := by
  refine ⟨rfl, valid, related, ?_, represented, Or.inl rfl, rfl, fun _ => rfl, ?_, ?_, ?_, fun _ _ => rfl, by simp, Nat.le_refl _⟩
  · exact ⟨rfl, fun _ impossible => False.elim (by simp at impossible)⟩
  · intro nonempty; exact False.elim (nonempty rfl)
  · intro nonempty; exact False.elim (nonempty rfl)
  · intro nonempty; exact False.elim (nonempty rfl)

theorem run_of_allocation (heap registered : Heap) (state allocated : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : WordAllocation.Allocator σ) (effects reached : σ) (slice : ArgumentSlice)
    (valid : state.valid = true) (related : Related heap state) (represented : Represents state source items)
    (nonempty : items ≠ [])
    (reserved : Allocation.reserve heap state allocator items request effects = ((.ok (some slice), registered, allocated), reached)) :
    ∃ after, run heap state allocator source items request effects = ((.ok (some slice), registered, after), reached) ∧
      Post heap state allocator source items slice registered after := by
  obtain ⟨base, rfl, rfl, rfl, fresh, _, allocatedValid⟩ :=
    Allocation.reserve_success heap registered state allocated allocator items request effects reached slice nonempty reserved
  have older := WordAllocation.source_older state source items valid represented nonempty
  obtain ⟨after, copied, afterValid, afterRelated, owned, preserved, initialized, frame⟩ :=
    copy_registered _ _ allocator source ⟨state.nextId, items⟩ allocatedValid (Allocation.extend_owned state items.length base)
      (write_same _ _ _) (Allocation.extend_others heap state allocator base items valid related)
      (WordAllocation.source_preserved state items.length base source items valid represented)
      (by simp [WordCopy.disjoint, view, show source.allocation ≠ state.nextId by omega])
  refine ⟨after, ?_, rfl, afterValid, afterRelated, initialized, preserved, Or.inr (write_same _ _ _), ?_, ?_,
    fun _ => fresh, ?_, fun _ => owned, ?_, ?_, ?_⟩
  · simp only [run, represented.1.symm, ne_eq, not_true_eq_false, ↓reduceIte, reserved, copied]
  · simp [List.isEmpty_eq_false_iff.mpr nonempty]
  · intro empty; exact False.elim (nonempty empty)
  · intro _; change source.allocation ≠ state.nextId; omega
  · intro id apart
    exact (frame.allocations id apart).trans (by simp only [WordAllocation.extend_lookup, if_neg (Ne.symm apart)])
  · simpa [List.isEmpty_eq_false_iff.mpr nonempty, WordAllocation.extend] using frame.nextId
  · rw [frame.nextAddress]
    exact Nat.le_max_left _ _

theorem run_admitted (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator base : Nat)
    (source : View) (items : List NodeId) (request : WordAllocation.Allocator σ) (effects reached : σ)
    (valid : state.valid = true) (related : Related heap state) (represented : Represents state source items)
    (nonempty : items ≠ []) (fresh : heap state.nextId = none)
    (response : request (items.length * 4) effects = (some base, reached)) (fits : WordAllocation.Fits state items.length base) :
    ∃ after, run heap state allocator source items request effects =
        ((.ok (some ⟨state.nextId, items⟩), write heap state.nextId (some ⟨allocator, .arguments items⟩), after), reached) ∧
      Post heap state allocator source items ⟨state.nextId, items⟩ (write heap state.nextId (some ⟨allocator, .arguments items⟩)) after :=
  run_of_allocation heap _ state _ allocator source items request effects reached _ valid related represented nonempty
    (Allocation.reserve_admitted heap state allocator base items request effects reached valid nonempty source represented fresh response fits)

/-- Under the external allocation contract and source representation, every
request yields ordinary OOM or an exact owned duplicate. Zero length imposes
no condition on a callback that is never invoked. This is not a native proof. -/
theorem run_total (heap : Heap) (state : Compiler.ZigAir.Memory.State) (allocator : Nat)
    (source : View) (items : List NodeId) (request : WordAllocation.Allocator σ) (effects : σ)
    (valid : state.valid = true) (related : Related heap state) (represented : Represents state source items)
    (fresh : items ≠ [] → heap state.nextId = none)
    (admitted : items ≠ [] → ∀ base reached, request (items.length * 4) effects = (some base, reached) → WordAllocation.Fits state items.length base) :
    ∃ result registered after reached, run heap state allocator source items request effects = ((.ok result, registered, after), reached) ∧
      match result with
      | none => registered = heap ∧ after = state ∧ request (items.length * 4) effects = (none, reached)
      | some slice => Post heap state allocator source items slice registered after := by
  by_cases empty : items = []
  · subst items
    exact ⟨some ⟨state.nextId, []⟩, heap, state, effects, run_empty heap state allocator source request effects represented.1.symm,
      empty_post heap state allocator source valid related represented⟩
  · cases response : request (items.length * 4) effects with
    | mk selected reached =>
      cases selected with
      | none => exact ⟨none, heap, state, reached, run_oom heap state allocator source items request effects reached valid empty represented response,
          rfl, rfl, rfl⟩
      | some base =>
        obtain ⟨after, ran, post⟩ := run_admitted heap state allocator base source items request effects reached valid related represented empty
          (fresh empty) response (admitted empty base reached response)
        exact ⟨some ⟨state.nextId, items⟩, _, after, reached, ran, post⟩

theorem Post.release (post : Post heap state allocator sourceView items slice registered after) :
    ∃ heap final, release registered after allocator slice = .ok (heap, final) ∧ ReleasePost registered after allocator slice heap final :=
  release_refines registered after allocator slice post.valid post.related post.live

end Compiler.Extraction.Memory.Arguments.Duplication
