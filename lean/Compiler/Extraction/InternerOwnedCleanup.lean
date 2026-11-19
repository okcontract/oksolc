/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerOwnedContracts

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

def Closed (scope : Local) : Prop :=
  scope.lookup = none ∧ (scope.handedOff = true ∨ scope.slice = none)

theorem deinit_detached (external : External σ) (allocator : Nat) (before : State σ) (handle : Handle)
    (present : before.scope.lookup = some handle) (detached : handle.owned = none) :
    deinit external allocator before = (.ok (), { before with scope := { before.scope with lookup := none } }) := by
  simp [deinit, present, deinitialize, detached]

/-- After handoff, outer cleanup closes the detached lookup without freeing the
normalized owner again. The insert callback and its reached world are arbitrary;
semantic rejections retain their actual scope and effects. -/
theorem finish_handoff (external : External σ) (allocator : Nat) (lookup : Handle)
    (normalized : ArgumentSlice) (world : World σ) (insert : ArgumentSlice → GraphAction σ α)
    (detached : lookup.owned = none) :
    (let (result, reached) := (do handoff; graph insert : Action σ α)
       ⟨world, ⟨some lookup, some normalized, false⟩⟩
     finish external allocator result reached) =
      (let (result, reached) := insert normalized world
       if ordinary result then (result, ⟨reached, ⟨none, some normalized, true⟩⟩)
       else (result, ⟨reached, ⟨some lookup, some normalized, true⟩⟩)) := by
  cases executed : insert normalized world with
  | mk result reached =>
    simp only [Effect.bind, handoff, graph, executed, finish]
    split
    · simp only [cleanup, ↓reduceIte, deinit_detached external allocator
        ⟨reached, ⟨some lookup, some normalized, true⟩⟩ lookup rfl detached]
    · rfl

/-- Cleanup preserves graph mutations made by recursion. On the owned path the
free equality names the actual reached state, including its allocator effects. -/
structure CleanupPost (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (slice : ArgumentSlice) (before after : State σ) : Prop where
  good : Good source values after.world
  closed : Closed after.scope
  graph : after.world.graph = before.world.graph
  handedOff : before.scope.handedOff = true → after.world = before.world
  freed : before.scope.handedOff = false →
    free external allocator slice before.world.memory = (.ok (), after.world.memory) ∧
      Consumed slice after.world.memory

theorem cleanup_taken (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (slice : ArgumentSlice) (handle : Handle) (before : State σ)
    (present : before.scope.lookup = some handle) (detached : handle.owned = none)
    (output : before.scope.slice = some slice) (good : Good source values before.world)
    (live : before.scope.handedOff = false → SliceValid allocator before.world.memory.heap slice)
    (separate : values ≠ [] → source.allocation ≠ slice.address) :
    ∃ after, cleanup external allocator before = (.ok (), after) ∧
      CleanupPost external allocator source values slice before after := by
  cases transferred : before.scope.handedOff with
  | true =>
    refine ⟨{ before with scope := { before.scope with lookup := none } }, ?_, good, ?_, rfl, fun _ => rfl, ?_⟩
    · simp only [cleanup, transferred, ↓reduceIte, deinit_detached external allocator before handle present detached]
    · exact ⟨rfl, Or.inl transferred⟩
    · intro impossible; rw [transferred] at impossible; cases impossible
  | false =>
    obtain ⟨memory, released, valid, post, _⟩ := free_valid external allocator slice before.world.memory good.1 (live transferred)
    let reached : State σ := ⟨{ before.world with memory }, { before.scope with slice := none }⟩
    refine ⟨{ reached with scope := { reached.scope with lookup := none } }, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · simp only [cleanup, transferred, Bool.false_eq_true, ↓reduceIte, output, released]
      simpa only [reached, transferred] using deinit_detached external allocator reached handle present detached
    · exact ⟨valid, released_source source values good.2 post separate⟩
    · exact ⟨rfl, Or.inr rfl⟩
    · intro impossible; rw [transferred] at impossible; cases impossible
    · intro _; exact ⟨released, released_consumed post⟩

theorem finish_taken (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (slice : ArgumentSlice) (handle : Handle) (before : State σ) (result : Except Fault α)
    (completed : ordinary result = true) (present : before.scope.lookup = some handle) (detached : handle.owned = none)
    (output : before.scope.slice = some slice) (good : Good source values before.world)
    (live : before.scope.handedOff = false → SliceValid allocator before.world.memory.heap slice)
    (separate : values ≠ [] → source.allocation ≠ slice.address) :
    ∃ after, finish external allocator result before = (result, after) ∧
      CleanupPost external allocator source values slice before after := by
  obtain ⟨after, closed, post⟩ := cleanup_taken external allocator source values slice handle before present detached output good live separate
  exact ⟨after, by simp only [finish, completed, ↓reduceIte, closed], post⟩

theorem finish_semantic (external : External σ) (allocator : Nat) (result : Except Fault α) (before : State σ)
    (rejected : ordinary result = false) : finish external allocator result before = (result, before) := by
  simp [finish, rejected]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
