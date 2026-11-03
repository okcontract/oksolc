/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerCallerCleanup

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

def Initialized (allocator : Nat) (source : View) (request : Interner.Request)
    (execution : Except Fault (List NodeId) × State σ) : Prop :=
  match execution.1 with
  | .error fault => ordinary (.error fault : Except Fault (List NodeId)) = true →
      CanClose allocator source request.arguments execution.2
  | .ok values => ∃ handle, execution.2.scope = { lookup := some handle } ∧
      Ready allocator source request.arguments handle execution.2.world.memory ∧ handle.values = values ∧
      normalizeCode.run Compiler.Extraction.InsertionSort.sortIds request.item request.arguments = some values

theorem initialize_graph (external : External σ) (budget allocator : Nat) (source buffer : View)
    (request : Interner.Request) (before : State σ) :
    (initLookup external budget allocator source buffer request before).2.world.graph = before.world.graph := by
  unfold initLookup
  cases decoded : Interner.Scoped.commutative request.item with
  | error error => rfl
  | ok commutative =>
    dsimp only
    cases ran : init normalizationOwnershipCode external budget allocator commutative source buffer request.arguments before.world.memory with
    | mk result memory => cases result <;> rfl

theorem initialize_verified (external : External σ) (budget allocator : Nat) (source buffer : View)
    (request : Interner.Request) (before : World σ)
    (good : Good source request.arguments before)
    (scratch : ∀ commutative : Bool, commutative = true → 2 ≤ source.length → source.length ≤ buffer.length → Scratch source buffer before.memory)
    (admitted : Admitted external) :
    Initialized allocator source request
      (initLookup external budget allocator source buffer request ⟨before, { lookup := none }⟩) := by
  unfold initLookup
  cases decoded : Interner.Scoped.commutative request.item with
  | error error => exact fun _ => CanClose.empty before good
  | ok commutative =>
    dsimp only
    obtain ⟨result, memory, ran, post⟩ := init_refines external budget allocator commutative source buffer request.arguments
      before.memory good.1 good.2 (scratch commutative) admitted
    rw [ran]
    cases result with
    | ok handle =>
      refine ⟨handle, rfl, post.1, rfl, ?_⟩
      rw [post.2]
      exact normalized_projection request.item commutative source request.arguments good.2.1 decoded
    | error failure =>
      cases failure with
      | outOfMemory => exact fun _ => CanClose.empty _ ⟨post.2.2, by simpa only [post.2.1] using good.2⟩
      | preparation fault => simp [Initialized, ordinary, memoryFault, Fault.recoverable]
      | allocation | release => exact False.elim post

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Caller
