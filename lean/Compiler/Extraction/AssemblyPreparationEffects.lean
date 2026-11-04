/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyItemCreationFields
import Compiler.Extraction.NormalizationMemoryEffects
import Compiler.Extraction.GraphEffects

namespace Compiler.Extraction
open Compiler.Algebraic Memory.Arguments.Normalization

/-- Exact observation of a host request at its reached session. This preserves
the complete response and private effects, including refused/invalid regions. -/
def Memory.Arguments.Normalization.HostTransport (project : σ → τ)
    (physical : α → Session σ → β × σ) (original : α → Session τ → β × τ) : Prop :=
  ∀ argument before, original argument (before.mapEffects project) =
    ((physical argument before).1, project (physical argument before).2)

namespace AssemblyItem.Creation

theorem create_transport (project : σ → τ) {physical : Allocate σ} {original : Allocate τ}
    (mapped : HostTransport project physical original) (allocator : Nat) (item : Cache.Item) :
    Effect.Transport (Session.mapEffects project) (create physical allocator item) (create original allocator item) := by
  intro before
  unfold create
  simp only [Session.mapEffects_memory]
  split
  · rfl
  · rw [mapped]
    cases physical layout before with
    | mk response effects =>
      cases response with
      | none => rfl
      | some base =>
        simp only [extend, Session.mapEffects_memory, Session.mapEffects_heap]
        split
        · rfl
        · cases before.heap before.memory.nextId <;> rfl

end AssemblyItem.Creation

namespace AssemblyClone.Physical

/-- Typed copy keeps the exact admitted allocation and initialized contents on
every outcome. It does not move source reads before the allocation request. -/
theorem copyAt_transport (project : σ → τ) (allocator base : Nat) (source : Bytes)
    (before : Session σ) (effects : σ) :
    copyAt allocator base source (before.mapEffects project) (project effects) =
      ((copyAt allocator base source before effects).1,
       (copyAt allocator base source before effects).2.mapEffects project) := by
  unfold copyAt
  simp only [extend, Session.mapEffects_memory, Session.mapEffects_heap]
  split
  · rfl
  · cases before.heap before.memory.nextId with
    | some block => rfl
    | none =>
      dsimp only
      split
      · rfl
      · split <;> rfl

theorem duplicate_transport (project : σ → τ) {physical : Allocate σ} {original : Allocate τ}
    (mapped : HostTransport project physical original) (allocator : Nat) (source : Bytes) :
    Effect.Transport (Session.mapEffects project) (duplicate physical allocator source) (duplicate original allocator source) := by
  intro before
  unfold duplicate
  simp only [Session.mapEffects_memory]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [mapped]
        cases physical source.contents.length before with
        | mk response effects =>
          cases response with
          | none => rfl
          | some base => exact copyAt_transport project allocator base source before effects

theorem run_transport (project : σ → τ) {physical : Allocate σ} {original : Allocate τ}
    (mapped : HostTransport project physical original) (allocator : Nat) (input : Value Metadata) :
    Effect.Transport (Session.mapEffects project) (run physical allocator input) (run original allocator input) := by
  intro before
  unfold run CloneCode.run cloneCode
  cases input.verbatim with
  | none => rfl
  | some source =>
    dsimp only [Cache.Scalar.run]
    rw [duplicate_transport project mapped]
    cases duplicate physical allocator source.data before with
    | mk result reached => cases result <;> rfl

end AssemblyClone.Physical

namespace AssemblyClone.NativeFields

theorem install_transport (project : σ → τ) (copied : ItemValue) (object : Nat) (before : Session σ) :
    install copied object (before.mapEffects project) = (install copied object before).map (Session.mapEffects project) := by
  unfold install
  simp only [Session.mapEffects_memory]
  cases AssemblyItem.Fields.assign (values copied) object before.memory <;> rfl

end AssemblyClone.NativeFields

/-- Project only the existing session. Invalidation and every native local
retain their reached values; these are observations, not new execution states. -/
def ExpressionDeinit.State.mapEffects (project : σ → τ) (before : ExpressionDeinit.State σ) : ExpressionDeinit.State τ :=
  ⟨before.memory.mapEffects project, before.invalidated⟩

def AssemblyClone.Physical.Insertion.State.mapEffects (project : σ → τ)
    (before : AssemblyClone.Physical.Insertion.State Metadata σ) : AssemblyClone.Physical.Insertion.State Metadata τ :=
  ⟨before.execution.mapEffects project, before.value⟩

def AssemblyItem.Creation.Insertion.State.mapEffects (project : σ → τ)
    (before : AssemblyItem.Creation.Insertion.State Metadata σ) : AssemblyItem.Creation.Insertion.State Metadata τ :=
  ⟨before.clone.mapEffects project, before.object⟩

end Compiler.Extraction
