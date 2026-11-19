/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerOwnedMemoryEffects
import Compiler.Extraction.InternerCallerMemory
import Compiler.Extraction.NormalizationHostTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Only callback instrumentation is assumed. The caller's initialization,
control flow, handoff and deferred cleanup are derived below. This is not a
constructor-correctness or graph-preservation premise. -/
structure Primitives.Transport (physical : Primitives σ) (original : Primitives τ) (project : σ → τ) : Prop where
  simplify : ∀ key slice, Effect.Transport (World.mapEffects project) (physical.simplify key slice) (original.simplify key slice)
  publish : ∀ key slice id, Effect.Transport (World.mapEffects project) (physical.publish key slice id) (original.publish key slice id)
  insert : ∀ key slice deterministic,
    Effect.Transport (World.mapEffects project) (physical.insert key slice deterministic) (original.insert key slice deterministic)

namespace Caller.EffectTransport
variable {physical : External σ} {original : External τ} {project : σ → τ}
  (mapped : External.Transport physical original project)
include mapped

theorem initLookup (budget allocator : Nat) (source buffer : View) (request : Interner.Request) :
    Effect.Transport (State.mapEffects project)
      (Caller.initLookup physical budget allocator source buffer request)
      (Caller.initLookup original budget allocator source buffer request) := by
  intro before
  unfold Caller.initLookup
  simp only [State.mapEffects, World.mapEffects]
  cases Interner.Scoped.commutative request.item with
  | error fault => rfl
  | ok commutative =>
    dsimp only
    rw [mapped.init]
    dsimp only [Step.mapEffects]
    cases Normalization.init normalizationOwnershipCode physical budget allocator commutative source buffer
        request.arguments before.world.memory with
    | mk result reached => cases result <;> rfl

/-- The same source-bound control interpreter is used on both sides. Every
branch, including capacity/cache exits and semantic faults, retains exact state. -/
theorem findBody (budget allocator : Nat) {left : Primitives σ} {right : Primitives τ}
    (callbacks : left.Transport right project) (queries : Queries)
    (source buffer : View) (request : Interner.Request) :
    Effect.Transport (State.mapEffects project)
      (Caller.findBody physical budget allocator left queries source buffer request)
      (Caller.findBody original budget allocator right queries source buffer request) := by
  unfold Caller.findBody Interner.FindCode.controlRun Interner.FindCode.controlOwned Interner.FindCode.controlMiss
  simp only [Caller.execution, OwnedCall.execution]
  repeat first
    | exact initLookup mapped budget allocator source buffer _
    | exact OwnedCall.EffectTransport.take mapped allocator
    | exact OwnedCall.EffectTransport.graph _ _ (callbacks.simplify _)
    | exact OwnedCall.EffectTransport.graph _ _ (fun slice => callbacks.publish _ slice _)
    | exact OwnedCall.EffectTransport.graph _ _ (fun slice => callbacks.insert _ slice _)
    | exact Effect.Transport.pure (State.mapEffects project) _
    | exact fun _ => rfl
    | apply Effect.Transport.bind (State.mapEffects project)
    | split
    | (intro value)

theorem invoke (allocator : Nat) {left : Action σ α} {right : Action τ α}
    (action : Effect.Transport (State.mapEffects project) left right) (before : World σ) :
    Caller.invoke original allocator right (before.mapEffects project) =
      ((Caller.invoke physical allocator left before).1,
       (Caller.invoke physical allocator left before).2.mapEffects project) := by
  unfold Caller.invoke
  have called := action ⟨before, { lookup := none }⟩
  change right ⟨before.mapEffects project, { lookup := none }⟩ = _ at called
  rw [called]
  cases left ⟨before, { lookup := none }⟩ with
  | mk result reached => exact OwnedCall.EffectTransport.finish mapped allocator result reached

theorem find (budget allocator : Nat) {left : Primitives σ} {right : Primitives τ}
    (callbacks : left.Transport right project) (queries : Queries)
    (source buffer : View) (request : Interner.Request) (before : World σ) :
    Caller.find original budget allocator right queries source buffer request (before.mapEffects project) =
      ((Caller.find physical budget allocator left queries source buffer request before).1,
       (Caller.find physical budget allocator left queries source buffer request before).2.mapEffects project) :=
  invoke mapped allocator (findBody mapped budget allocator callbacks queries source buffer request) before

end Caller.EffectTransport

/-- Consume actual host instrumentation through the complete native caller.
Recursive/publication/insertion callbacks must discharge their own erasure;
this theorem alone does not claim their resource calls have been recorded. -/
theorem Caller.host_trace_erases (host : External σ) (budget allocator : Nat)
    {recorded : Primitives (HostTrace.Recorded σ)} {original : Primitives σ}
    (callbacks : recorded.Transport original HostTrace.Recorded.effects) (queries : Caller.Queries)
    (source buffer : View) (request : Interner.Request) (before : World (HostTrace.Recorded σ)) :
    Caller.find host budget allocator original queries source buffer request (before.mapEffects HostTrace.Recorded.effects) =
      ((Caller.find (HostTrace.record host) budget allocator recorded queries source buffer request before).1,
       (Caller.find (HostTrace.record host) budget allocator recorded queries source buffer request before).2.mapEffects HostTrace.Recorded.effects) :=
  Caller.EffectTransport.find (HostTrace.transport host) budget allocator callbacks queries source buffer request before

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall
