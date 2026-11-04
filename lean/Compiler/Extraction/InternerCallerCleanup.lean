/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerMemory

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Before transfer, lookup may still own its normalization temporary. After
transfer, reuse the existing reached-state cleanup contract. -/
inductive CanClose (allocator : Nat) (source : View) (values : List NodeId) : State σ → Prop where
  | empty (before : World σ) (good : Good source values before) :
      CanClose allocator source values ⟨before, { lookup := none }⟩
  | lookup (before : World σ) (handle : Handle) (ready : Ready allocator source values handle before.memory) :
      CanClose allocator source values ⟨before, { lookup := some handle }⟩
  | taken (before : State σ) (ready : ReadyToClose allocator source values before) :
      CanClose allocator source values before

theorem cleanup_lookup (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (handle : Handle) (before : World σ) (ready : Ready allocator source values handle before.memory) :
    ∃ after, cleanup external allocator ⟨before, { lookup := some handle }⟩ = (.ok (), after) ∧
      Good source values after.world ∧ Closed after.scope ∧ after.world.graph = before.graph ∧
      (∀ slice, handle.owned = some slice → Consumed slice after.world.memory) := by
  obtain ⟨memory, closed, valid, represented, consumed, _⟩ := deinit_refines external allocator source values handle before.memory ready
  refine ⟨⟨{ before with memory }, { lookup := none }⟩, ?_, ⟨valid, represented⟩, ⟨rfl, Or.inr rfl⟩, rfl, consumed⟩
  simp only [cleanup, Bool.false_eq_true, ↓reduceIte, deinit, closed]

theorem finish_canClose (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (before : State σ) (result : Except Fault α) (ready : CanClose allocator source values before)
    (completed : ordinary result = true) :
    ∃ after, finish external allocator result before = (result, after) ∧
      Good source values after.world ∧ Closed after.scope ∧ after.world.graph = before.world.graph := by
  cases ready with
  | empty world good =>
    exact ⟨⟨world, { lookup := none }⟩, by simp [finish, completed, cleanup, deinit], good, ⟨rfl, Or.inr rfl⟩, rfl⟩
  | lookup world handle ready =>
    obtain ⟨after, closed, good, scope, graph, _⟩ := cleanup_lookup external allocator source values handle world ready
    exact ⟨after, by simp only [finish, completed, ↓reduceIte, closed], good, scope, graph⟩
  | taken state ready =>
    obtain ⟨after, closed, good, scope, graph, _⟩ := finish_ready external allocator source values _ result ready completed
    exact ⟨after, closed, good, scope, graph⟩

theorem invoke_verified (external : External σ) (allocator : Nat) (source : View) (values : List NodeId)
    (action : Action σ α) (before : World σ)
    (checked : ordinary (action ⟨before, { lookup := none }⟩).1 = true →
      CanClose allocator source values (action ⟨before, { lookup := none }⟩).2) :
    let bodyResult := action ⟨before, { lookup := none }⟩
    let execution := invoke external allocator action before
    execution.1 = bodyResult.1 ∧
      (ordinary bodyResult.1 = false → execution.2 = bodyResult.2) ∧
      (ordinary bodyResult.1 = true → Good source values execution.2.world ∧ Closed execution.2.scope ∧
        execution.2.world.graph = bodyResult.2.world.graph) := by
  cases ran : action ⟨before, { lookup := none }⟩ with
  | mk result reached =>
    rw [ran] at checked
    simp only [invoke, ran]
    cases completed : ordinary result with
    | false => simp [finish_semantic external allocator result reached completed]
    | true =>
      obtain ⟨after, closed, good, scope, graph⟩ := finish_canClose external allocator source values reached result (checked completed) completed
      simp only [closed]
      simpa using And.intro good (And.intro scope graph)

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
