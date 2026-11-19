/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.NormalizationResources
import Compiler.Extraction.NormalizationMemoryEffects
import Compiler.Extraction.NormalizationTrace

namespace Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray

/-- Instrumentation changes private host effects only. Native handles, transferred
slices and explicit rejection remain the same descriptors. -/
def State.mapEffects (project : σ → τ) (before : State σ) : State τ :=
  { before with session := before.session.mapEffects project }

namespace EffectTransport
variable {left : External σ} {right : External τ} {project : σ → τ}
  (mapped : left.Transport right project)
include mapped

theorem allocate (allocator : Nat) (values : List NodeId)
    (site : NormalizationOwnership.Allocation) (before : State σ) :
    ResourceAdapter.allocate right allocator values site (before.mapEffects project) =
      ((ResourceAdapter.allocate left allocator values site before).1,
       (ResourceAdapter.allocate left allocator values site before).2.mapEffects project) := by
  unfold ResourceAdapter.allocate
  simp only [State.mapEffects]
  split
  · rfl
  · cases site with
    | temporary =>
      rw [mapped.reserve]
      cases Normalization.reserve left allocator values before.session with
      | mk result reached => cases result <;> rfl
    | duplicate =>
      rw [mapped.takeOwned]
      cases Normalization.takeOwned normalizationOwnershipCode left allocator before.handle before.session with
      | mk result reached => cases result <;> rfl

theorem release (allocator : Nat) (lookup : NormalizationOwnership.State) (before : State σ) :
    ResourceAdapter.release right allocator lookup (before.mapEffects project) =
      (ResourceAdapter.release left allocator lookup before).mapEffects project := by
  unfold ResourceAdapter.release
  simp only [State.mapEffects, outputSlice]
  split
  · rfl
  · split
    · rfl
    · rw [mapped.free]; rfl

end EffectTransport

theorem prepare_transport (project : σ → τ) (budget allocator : Nat)
    (source buffer : View) (values : List NodeId) (lookup : NormalizationOwnership.State) (before : State σ) :
    prepare budget allocator source buffer values lookup (before.mapEffects project) =
      ((prepare budget allocator source buffer values lookup before).1,
       (prepare budget allocator source buffer values lookup before).2.mapEffects project) := by
  unfold prepare
  simp only [State.mapEffects]
  rw [External.Transport.prepare (project := project)]
  cases Normalization.prepare normalizationOwnershipCode budget allocator buffer.length source
      (if lookup.origin = .scratch then bufferPrefix buffer source.length else before.handle.items)
      values (lookup.origin == .allocation) before.session with
  | mk result reached => cases result <;> rfl

/-- Derive every protocol primitive from the actual native host equations.
Neither successful allocation nor completed preparation is assumed. -/
theorem primitives_transport {left : External σ} {right : External τ} {project : σ → τ}
    (mapped : left.Transport right project) (budget allocator : Nat)
    (source buffer : View) (values : List NodeId) :
    NormalizationOwnership.Transport (primitives left budget allocator source buffer values)
      (primitives right budget allocator source buffer values) (State.mapEffects project) :=
  ⟨EffectTransport.allocate mapped allocator values, EffectTransport.release mapped allocator,
    prepare_transport project budget allocator source buffer values⟩

end Compiler.Extraction.Memory.Arguments.Normalization.ResourceAdapter

namespace Compiler.Extraction.Cache.NormalizationOwnership.Trace

/-- Preserve the protocol history when projecting its private effects. -/
def Recorded.mapEffects (project : σ → τ) (before : Recorded σ ε) : Recorded τ ε :=
  ⟨project before.effects, before.events⟩

theorem record_map {left : PreparedPrimitives σ ε} {right : PreparedPrimitives τ ε} {project : σ → τ}
    (mapped : Transport left right project) :
    Transport (record left) (record right) (Recorded.mapEffects project) := by
  constructor
  · intro site before
    simp only [record, Recorded.mapEffects, mapped.allocate]
  · intro lookup before
    simp only [record, Recorded.mapEffects, mapped.release]
  · intro lookup before
    simp only [record, Recorded.mapEffects, mapped.prepare]

end Compiler.Extraction.Cache.NormalizationOwnership.Trace
