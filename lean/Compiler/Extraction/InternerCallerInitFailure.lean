/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerInit

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- An ordinary initializer error never publishes a lookup owner or changes
native/registry storage. Allocator effects remain those of the actual attempt. -/
theorem initialize_failed (external : External σ) (budget allocator : Nat) (source buffer : View)
    (request : Interner.Request) (before : World σ) (fault : Fault) (after : State σ)
    (good : Good source request.arguments before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external)
    (failed : initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩ = (.error fault, after))
    (completed : ordinary (.error fault : Except Fault NodeId) = true) :
    Good source request.arguments after.world ∧ after.scope = { lookup := none } ∧
      after.world.graph = before.graph ∧ after.world.memory.memory = before.memory.memory ∧
      after.world.memory.heap = before.memory.heap := by
  unfold initLookup at failed
  cases decoded : Interner.Scoped.commutative request.item with
  | error error =>
    rw [decoded] at failed
    cases failed
    exact ⟨good, rfl, rfl, rfl, rfl⟩
  | ok commutative =>
    rw [decoded] at failed
    dsimp only at failed
    obtain ⟨result, memory, ran, post⟩ := init_refines external budget allocator commutative source buffer
      request.arguments before.memory good.1 good.2 (scratch commutative) admitted
    rw [ran] at failed
    cases result with
    | ok handle => cases failed
    | error failure =>
      simp only [Prod.mk.injEq, Except.error.injEq] at failed
      rcases failed with ⟨rfl, rfl⟩
      cases failure with
      | outOfMemory => exact ⟨⟨post.2.2, by simpa only [post.2.1] using good.2⟩, rfl, rfl, post.2.1, post.1⟩
      | preparation reason => cases completed
      | allocation | release => exact False.elim post

theorem find_init_failed (external : External σ) (budget allocator : Nat) (p : Primitives σ) (q : Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ) (fault : Fault) (after : State σ)
    (room : q.atCapacity before.graph = false)
    (failed : initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩ = (.error fault, after)) :
    find external budget allocator p q source buffer request before = finish external allocator (.error fault : Except Fault NodeId) after := by
  unfold find invoke findBody Interner.FindCode.controlRun
  simp only [execution, OwnedCall.execution, bind, Effect.bind, room, Bool.false_eq_true, ↓reduceIte, failed]

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
