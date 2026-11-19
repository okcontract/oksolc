/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerInsertionControlEffects

namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
open Compiler.Algebraic Compiler.Extraction.Storage Compiler.Extraction.Cache
open Compiler.ZigAir.Memory.WordArray RepresentativeArray

namespace SharedEffects
variable {project : σ → τ} {left : Operations σ} {right : Operations τ}
  (external : External.Transport left.arguments right.arguments project)
  (allocator count : Nat) (source : View) (input : AssemblyClone.Value Metadata)
  (key : Key) (normalized : ArgumentSlice)
  (leftGraph : Storage.State → State Metadata σ → Interner.Heap)
  (rightGraph : Storage.State → State Metadata τ → Interner.Heap)
include external

/-- Instantiate normalization's existing all-outcome proof at the actual
insertion ownership guard and reached duplicate local. -/
theorem arguments (owner : Storage.State) :
    Effect.Transport (State.mapEffects project)
      ((callbacks left allocator count source input key normalized leftGraph).attempt .arguments owner)
      ((callbacks right allocator count source input key normalized rightGraph).attempt .arguments owner) := by
  intro before
  dsimp only [callbacks]
  rw [memory_mapEffects]
  change (if !ownsArguments allocator normalized (memory before).heap then _ else _) = _
  split
  · rfl
  · rw [(Publication.external_transport external).takeOwned]
    cases takeOwned normalizationOwnershipCode (Publication.external left.arguments) allocator
        ⟨Arguments.view normalized, normalized.items, none⟩ (memory before) with
    | mk result reached =>
      cases result with
      | ok value => cases value; rfl
      | error fault => cases fault <;> rfl

theorem publish (probes : OwnedKeys.Physical.Probe.Transport left.probe right.probe project)
    (graphs : ∀ owner before, rightGraph owner (before.mapEffects project) = leftGraph owner before)
    (owner : Storage.State) :
    Effect.Transport (State.mapEffects project)
      ((callbacks left allocator count source input key normalized leftGraph).attempt .publish owner)
      ((callbacks right allocator count source input key normalized rightGraph).attempt .publish owner) := by
  intro before
  dsimp only [callbacks]
  rw [graphs, memory_mapEffects]
  have called := Publication.EffectTransport.publish external probes allocator source key normalized (BitVec.ofNat 32 count)
    ⟨leftGraph owner before, memory before⟩
  change Publication.publish right.probe right.arguments allocator source key normalized (BitVec.ofNat 32 count)
    ⟨leftGraph owner before, (memory before).mapEffects (Publication.Effects.mapAllocator project)⟩ = _ at called
  rw [called]
  cases Publication.publish left.probe left.arguments allocator source key normalized (BitVec.ofNat 32 count)
      ⟨leftGraph owner before, memory before⟩ with
  | mk result reached =>
    cases result with
    | ok value => cases value; rfl
    | error fault => cases fault with
      | language reason => cases reason <;> rfl
      | _ => rfl

/-- Both argument releases use the same reached memory and existing descriptor
selection. Missing descriptors and invalid ownership are preserved as faults. -/
theorem release (action : Storage.Release) (shared : action = .normalized ∨ action = .arguments)
    (owner : Storage.State) :
    Effect.Transport (State.mapEffects project)
      ((callbacks left allocator count source input key normalized leftGraph).release action owner)
      ((callbacks right allocator count source input key normalized rightGraph).release action owner) := by
  intro before
  have freed (slice : ArgumentSlice) := (Publication.external_transport external).free allocator slice (memory before)
  rcases shared with rfl | rfl
  · dsimp only [callbacks]
    rw [memory_mapEffects, freed]
    rfl
  · dsimp only [callbacks]
    change (match Insertion.arguments normalized owner before with | none => _ | some slice => _) = _
    cases Insertion.arguments normalized owner before with
    | none => rfl
    | some slice => dsimp only; rw [memory_mapEffects, freed]; rfl

end SharedEffects

namespace Native
variable {project : σ → τ} {left : Operations σ} {right : Operations τ}
  (external : External.Transport left.arguments right.arguments project)
  (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
  (runtimeSafety : Bool) (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
  (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
  (cells : List Storage.Cell) (value : Contract.Yul.Word)
  (leftGraph : Storage.State → Frame σ → Interner.Heap) (rightGraph : Storage.State → Frame τ → Interner.Heap)
  (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ))
include external

theorem shared_attempt_transport (probes : OwnedKeys.Physical.Probe.Transport left.probe right.probe project)
    (graphs : ∀ owner before, rightGraph owner (before.mapEffects project) = leftGraph owner before)
    (site : Storage.Allocation) (shared : site = .arguments ∨ site = .publish) (owner : Storage.State) :
    Effect.Transport (State.mapEffects project)
      ((callbacks left leftAllocate runtimeSafety allocator container source itemSource input key normalized cells value leftGraph leftGrowth).attempt site owner)
      ((callbacks right rightAllocate runtimeSafety allocator container source itemSource input key normalized cells value rightGraph rightGrowth).attempt site owner) := by
  intro before
  have called : Effect.Transport (State.mapEffects project)
      ((Insertion.callbacks left allocator cells.length source input key normalized leftGraph).attempt site owner)
      ((Insertion.callbacks right allocator cells.length source input key normalized rightGraph).attempt site owner) := by
    rcases shared with rfl | rfl
    · exact SharedEffects.arguments external allocator cells.length source input key normalized leftGraph rightGraph owner
    · exact SharedEffects.publish external allocator cells.length source input key normalized leftGraph rightGraph probes graphs owner
  rcases shared with rfl | rfl
  all_goals
    exact congrArg (fun output : Except Rejection Bool × Frame τ => (output.1.mapError Fault.base, output.2)) (called before)

theorem shared_release_transport (action : Storage.Release) (shared : action = .normalized ∨ action = .arguments)
    (owner : Storage.State) :
    Effect.Transport (State.mapEffects project)
      ((callbacks left leftAllocate runtimeSafety allocator container source itemSource input key normalized cells value leftGraph leftGrowth).release action owner)
      ((callbacks right rightAllocate runtimeSafety allocator container source itemSource input key normalized cells value rightGraph rightGrowth).release action owner) := by
  intro before
  have called := SharedEffects.release external allocator cells.length source input key normalized leftGraph rightGraph action shared owner before
  rcases shared with rfl | rfl
  all_goals
    exact congrArg (fun output : Except Rejection Unit × Frame τ => (output.1.mapError Fault.base, output.2)) called

/-- Only native backing growth and typed destruction/pop remain. Argument
duplication, publication and their releases are derived, not assumed here. -/
structure ResidualTransport (physical : Storage.Operations (Frame σ) Fault)
    (original : Storage.Operations (Frame τ) Fault) (project : σ → τ) : Prop where
  append : ∀ owner, Effect.Transport (State.mapEffects project) (physical.attempt .append owner) (original.attempt .append owner)
  release : ∀ action, action ≠ .normalized → action ≠ .arguments → ∀ owner,
    Effect.Transport (State.mapEffects project) (physical.release action owner) (original.release action owner)

theorem pending_transport (probes : OwnedKeys.Physical.Probe.Transport left.probe right.probe project)
    (graphs : ∀ owner before, rightGraph owner (before.mapEffects project) = leftGraph owner before)
    (remaining : ResidualTransport
      (callbacks left leftAllocate runtimeSafety allocator container source itemSource input key normalized cells value leftGraph leftGrowth)
      (callbacks right rightAllocate runtimeSafety allocator container source itemSource input key normalized cells value rightGraph rightGrowth) project) :
    PendingTransport
      (callbacks left leftAllocate runtimeSafety allocator container source itemSource input key normalized cells value leftGraph leftGrowth)
      (callbacks right rightAllocate runtimeSafety allocator container source itemSource input key normalized cells value rightGraph rightGrowth) project := by
  refine ⟨?_, remaining.append, ?_, ?_⟩
  · exact shared_attempt_transport external leftAllocate rightAllocate runtimeSafety allocator container source itemSource input
      key normalized cells value leftGraph rightGraph leftGrowth rightGrowth probes graphs .arguments (Or.inl rfl)
  · exact shared_attempt_transport external leftAllocate rightAllocate runtimeSafety allocator container source itemSource input
      key normalized cells value leftGraph rightGraph leftGrowth rightGrowth probes graphs .publish (Or.inr rfl)
  · intro action owner
    by_cases normalizedRelease : action = .normalized
    · exact shared_release_transport external leftAllocate rightAllocate runtimeSafety allocator container source itemSource input
        key normalized cells value leftGraph rightGraph leftGrowth rightGrowth action (Or.inl normalizedRelease) owner
    by_cases argumentRelease : action = .arguments
    · exact shared_release_transport external leftAllocate rightAllocate runtimeSafety allocator container source itemSource input
        key normalized cells value leftGraph rightGraph leftGrowth rightGrowth action (Or.inr argumentRelease) owner
    exact remaining.release action normalizedRelease argumentRelease owner

/-- The caller supplies graph agreement from its real insertion projection.
Only the unresolved native branches remain quantified over reached frames. -/
def ResidualObligations (project : σ → τ) (left : Operations σ) (right : Operations τ)
    (leftAllocate : Backing.Registry.Allocate σ) (rightAllocate : Backing.Registry.Allocate τ)
    (runtimeSafety : Bool) (allocator container : Nat) (source : View) (itemSource : Compiler.ZigAir.Memory.Address)
    (input : AssemblyClone.NativeFields.ItemValue) (key : Key) (normalized : ArgumentSlice)
    (leftGrowth : Option (Growth.Registered.Callbacks σ)) (rightGrowth : Option (Growth.Registered.Callbacks τ)) : Prop :=
  ∀ cells value (leftGraph : Storage.State → Frame σ → Interner.Heap) (rightGraph : Storage.State → Frame τ → Interner.Heap),
    (∀ owner before, rightGraph owner (before.mapEffects project) = leftGraph owner before) →
    ResidualTransport
      (callbacks left leftAllocate runtimeSafety allocator container source itemSource input key normalized cells value leftGraph leftGrowth)
      (callbacks right rightAllocate runtimeSafety allocator container source itemSource input key normalized cells value rightGraph rightGrowth) project

theorem callback_obligations (probes : OwnedKeys.Physical.Probe.Transport left.probe right.probe project)
    (remaining : ResidualObligations project left right leftAllocate rightAllocate runtimeSafety allocator container
      source itemSource input key normalized leftGrowth rightGrowth) :
    CallbackObligations project left right leftAllocate rightAllocate runtimeSafety allocator container
      source itemSource input key normalized leftGrowth rightGrowth := by
  intro cells value leftGraph rightGraph graphs
  exact pending_transport external leftAllocate rightAllocate runtimeSafety allocator container source itemSource input key normalized
    cells value leftGraph rightGraph leftGrowth rightGrowth probes graphs (remaining cells value leftGraph rightGraph graphs)

end Native
end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.Insertion
