/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPublication
import Compiler.Extraction.OwnedKeysPhysicalEffects
import Compiler.Extraction.InternerCallerMemoryEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Project only allocator-private effects. The publication-owned key table
is retained, including the reached table after replacement or rejection. -/
def Effects.mapAllocator (project : σ → τ) (before : Effects σ) : Effects τ :=
  ⟨before.keys, project before.allocator⟩

theorem forget_mapEffects (project : σ → τ) (before : Session (Effects σ)) :
    forget (before.mapEffects (Effects.mapAllocator project)) = (forget before).mapEffects project := rfl

theorem external_transport {physical : External σ} {original : External τ} {project : σ → τ}
    (mapped : External.Transport physical original project) :
    External.Transport (external physical) (external original) (Effects.mapAllocator project) := by
  constructor
  · intro site before bytes effects
    exact congrArg (fun output : Option Nat × τ => (output.1, (⟨effects.keys, output.2⟩ : Effects τ)))
      (mapped.allocate site (forget before) bytes effects.allocator)
  · intro slice before
    exact congrArg (fun reached => (⟨before.effects.keys, reached⟩ : Effects τ))
      (mapped.release slice (forget before))

theorem probe_transport {left : OwnedKeys.Physical.Probe σ} {right : OwnedKeys.Physical.Probe τ}
    {project : σ → τ} (mapped : OwnedKeys.Physical.Probe.Transport left right project) :
    OwnedKeys.Physical.Probe.Transport (probe left) (probe right) (Effects.mapAllocator project) := by
  intro key before
  dsimp only [probe, Effects.mapAllocator]
  rw [forget_mapEffects, mapped]
  rfl

theorem admit_transport (project : σ → τ) (allocator : Nat) (source : View)
    (key : Key) (owned : ArgumentSlice) (before : World (Effects σ)) :
    admit allocator source key owned (before.mapEffects (Effects.mapAllocator project)) =
      admit allocator source key owned before := rfl

theorem commit_transport (project : σ → τ) (key : Key) (id : NodeId) (before : World (Effects σ))
    (execution : Except Failure Unit × OwnedKeys.Physical.State (Effects σ)) :
    commit key id (before.mapEffects (Effects.mapAllocator project))
        (execution.1, execution.2.mapEffects (Effects.mapAllocator project)) =
      ((commit key id before execution).1, (commit key id before execution).2.mapEffects (Effects.mapAllocator project)) := by
  rcases execution with ⟨result, reached⟩
  cases result <;> rfl

namespace EffectTransport
variable {physical : External σ} {original : External τ} {project : σ → τ}
  (mapped : External.Transport physical original project)
  {left : OwnedKeys.Physical.Probe σ} {right : OwnedKeys.Physical.Probe τ}
  (probes : OwnedKeys.Physical.Probe.Transport left right project)
include mapped probes

theorem body (allocator : Nat) (key : Key) (owned : ArgumentSlice) (id : NodeId) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator project))
      (Publication.body left physical allocator key owned id)
      (Publication.body right original allocator key owned id) := by
  intro before
  unfold Publication.body
  have called := OwnedKeys.Physical.run_transport (external_transport mapped) (probe_transport probes)
    allocator key ⟨owned.address, id⟩ (Publication.physical before)
  change OwnedKeys.Physical.run (probe right) (external original) allocator key ⟨owned.address, id⟩
    (Publication.physical (before.mapEffects (Effects.mapAllocator project))) = _ at called
  rw [called]
  exact commit_transport project key id before _

/-- Derive publication erasure from actual host calls and the same admission,
probe, old-key release and commit operations, without assuming publication's
result or reached graph. Rejected admission and release remain exact outcomes. -/
theorem publish (allocator : Nat) (source : View) (key : Key) (owned : ArgumentSlice) (id : NodeId) :
    Effect.Transport (World.mapEffects (Effects.mapAllocator project))
      (Publication.publish left physical allocator source key owned id)
      (Publication.publish right original allocator source key owned id) := by
  intro before
  unfold Publication.publish
  rw [admit_transport]
  cases admit allocator source key owned before with
  | error reason => rfl
  | ok value => cases value; exact body mapped probes allocator key owned id before

theorem callbacks (allocator : Nat) (source : View) {p : Primitives (Effects σ)} {q : Primitives (Effects τ)}
    (simplify : ∀ key slice, Effect.Transport (World.mapEffects (Effects.mapAllocator project)) (p.simplify key slice) (q.simplify key slice))
    (insert : ∀ key slice deterministic, Effect.Transport (World.mapEffects (Effects.mapAllocator project))
      (p.insert key slice deterministic) (q.insert key slice deterministic)) :
    (Publication.callbacks left physical allocator source p).Transport
      (Publication.callbacks right original allocator source q) (Effects.mapAllocator project) :=
  ⟨simplify, fun key slice id => publish mapped probes allocator source key slice id, insert⟩

/-- Consume the derived publication field immediately in the shared caller.
Only the actual simplification/recursive and insertion callbacks remain. -/
theorem find (budget allocator : Nat) (source buffer : View)
    {p : Primitives (Effects σ)} {q : Primitives (Effects τ)}
    (simplify : ∀ key slice, Effect.Transport (World.mapEffects (Effects.mapAllocator project)) (p.simplify key slice) (q.simplify key slice))
    (insert : ∀ key slice deterministic, Effect.Transport (World.mapEffects (Effects.mapAllocator project))
      (p.insert key slice deterministic) (q.insert key slice deterministic))
    (queries : Caller.Queries) (request : Interner.Request) (before : World (Effects σ)) :
    Caller.find (external original) budget allocator (Publication.callbacks right original allocator source q)
        queries source buffer request (before.mapEffects (Effects.mapAllocator project)) =
      ((Caller.find (external physical) budget allocator (Publication.callbacks left physical allocator source p)
          queries source buffer request before).1,
       (Caller.find (external physical) budget allocator (Publication.callbacks left physical allocator source p)
          queries source buffer request before).2.mapEffects (Effects.mapAllocator project)) :=
  Caller.EffectTransport.find (external_transport mapped) budget allocator
    (callbacks mapped probes allocator source simplify insert) queries source buffer request before

end EffectTransport
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Publication
