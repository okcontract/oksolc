/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.AssemblyPreparationEffects
import Compiler.Extraction.ExpressionDeinitNative

namespace Compiler.Extraction
open Compiler.Algebraic Memory.Arguments.Normalization

/-- Exact host release at the reached session, before the executor installs its
registry/native-memory update. Rejected ownership never invokes this callback. -/
def Memory.Arguments.Normalization.HostReleaseTransport (project : σ → τ)
    (physical : α → Session σ → σ) (original : α → Session τ → τ) : Prop :=
  ∀ argument before, original argument (before.mapEffects project) = project (physical argument before)

theorem AssemblyItem.destroy_transport (project : σ → τ) {physical : AssemblyItem.Release σ} {original : AssemblyItem.Release τ}
    (mapped : HostReleaseTransport project physical original) (allocator object : Nat) :
    Effect.Transport (Session.mapEffects project) (AssemblyItem.destroy physical allocator object) (AssemblyItem.destroy original allocator object) := by
  intro before
  unfold AssemblyItem.destroy
  simp only [Session.mapEffects_heap, Session.mapEffects_memory]
  split
  · rfl
  · rw [mapped]; rfl

namespace AssemblyItemDeinit

def State.mapEffects (project : σ → τ) (before : State σ) : State τ :=
  ⟨before.memory.mapEffects project, before.invalidated⟩

variable {project : σ → τ} {physical : Release σ} {original : Release τ}
  (mapped : HostReleaseTransport project physical original)
include mapped

theorem free_transport (allocator : Nat) (slice : Bytes) :
    Effect.Transport (Session.mapEffects project) (free physical allocator slice) (free original allocator slice) := by
  intro before
  unfold free
  simp only [Session.mapEffects_heap, Session.mapEffects_memory]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · rw [mapped]; rfl

theorem stage_transport (allocator : Nat) (payload : Option Bytes) (stage : Stage) :
    Effect.Transport (State.mapEffects project) (stage.execute physical allocator payload) (stage.execute original allocator payload) := by
  intro before
  unfold Stage.execute
  change (if before.invalidated then _ else _) = _
  split
  · rfl
  · cases stage with
    | invalidate => rfl
    | payload => cases payload with
      | none => rfl
      | some slice =>
        dsimp only [State.mapEffects]
        rw [free_transport mapped allocator slice before.memory]

theorem execute_transport (allocator : Nat) (payload : Option Bytes) (stages : List Stage) :
    Effect.Transport (State.mapEffects project) (execute physical allocator payload stages) (execute original allocator payload stages) := by
  intro before
  induction stages generalizing before with
  | nil => rfl
  | cons stage rest ih =>
    unfold execute
    rw [stage_transport mapped allocator payload stage before]
    cases stage.execute physical allocator payload before with
    | mk result reached => cases result with
      | error fault => rfl
      | ok value => cases value; exact ih reached

theorem run_transport (allocator : Nat) (payload : Option Bytes) (before : Session σ) :
    run original allocator payload (before.mapEffects project) =
      ((run physical allocator payload before).1, (run physical allocator payload before).2.mapEffects project) :=
  execute_transport mapped allocator payload assemblyItemDeinitCode ⟨before, false⟩

namespace Native

omit mapped in
theorem finish_transport (project : σ → τ) (object : Compiler.ZigAir.Memory.Address) (before : Session σ) :
    finish object (before.mapEffects project) =
      ((finish object before).1, (finish object before).2.mapEffects project) := by
  unfold finish
  simp only [Session.mapEffects_memory]
  cases Compiler.ZigAir.Memory.invalidate before.memory true AssemblyItem.viewType object <;> rfl

theorem run_transport (allocator : Nat) (object : Compiler.ZigAir.Memory.Address) (before : Session σ) :
    run original allocator object (before.mapEffects project) =
      ((run physical allocator object before).1, (run physical allocator object before).2.mapEffects project) := by
  unfold run
  simp only [Session.mapEffects_memory]
  cases readPayload before.memory object with
  | error reason => rfl
  | ok payload =>
    dsimp only
    rw [AssemblyItemDeinit.run_transport mapped allocator payload before]
    cases AssemblyItemDeinit.run physical allocator payload before with
    | mk result reached => cases result with
      | error reason => rfl
      | ok value => cases value; exact finish_transport project object reached.memory

end Native
end AssemblyItemDeinit

namespace ExpressionDeinit

/-- Transport the existing stage traversal without restarting after a release
or adding unwinding after a semantic rejection. -/
theorem executeStages_transport (project : σ → τ)
    {physical : Stage → State σ → Except ε Unit × State σ} {original : Stage → State τ → Except ε Unit × State τ}
    (mapped : ∀ stage, Effect.Transport (State.mapEffects project) (physical stage) (original stage)) (stages : List Stage) :
    Effect.Transport (State.mapEffects project) (executeStages physical stages) (executeStages original stages) := by
  intro before
  induction stages generalizing before with
  | nil => rfl
  | cons stage rest ih =>
    simp only [executeStages]
    rw [mapped stage before]
    cases physical stage before with
    | mk result reached => cases result with
      | error reason => rfl
      | ok value => cases value; exact ih reached

namespace Native
variable {project : σ → τ} {leftBytes : AssemblyItemDeinit.Release σ} {rightBytes : AssemblyItemDeinit.Release τ}
  {leftObjects : AssemblyItem.Release σ} {rightObjects : AssemblyItem.Release τ}
  {left : External σ} {right : External τ}
  (bytes : HostReleaseTransport project leftBytes rightBytes) (objects : HostReleaseTransport project leftObjects rightObjects)
  (external : External.Transport left right project)
include bytes objects external

theorem step_transport (allocator : Nat) (descriptor : Compiler.ZigAir.Memory.Address) (stage : Stage) :
    Effect.Transport (State.mapEffects project) (step leftBytes leftObjects left allocator descriptor stage)
      (step rightBytes rightObjects right allocator descriptor stage) := by
  intro before
  unfold step
  dsimp only [State.mapEffects]
  change (if before.invalidated then _ else _) = _
  split
  · rfl
  · cases stage with
    | itemValue =>
      change (match Fields.item before.memory.memory descriptor with | .error reason => _ | .ok object => _) = _
      cases Fields.item before.memory.memory descriptor with
      | error reason => rfl
      | ok object =>
        dsimp only
        rw [AssemblyItemDeinit.Native.run_transport bytes allocator object before.memory]
        rfl
    | itemAllocation =>
      change (match Fields.item before.memory.memory descriptor with | .error reason => _ | .ok object => _) = _
      cases Fields.item before.memory.memory descriptor with
      | error reason => rfl
      | ok object =>
        dsimp only
        split
        · rfl
        · rw [AssemblyItem.destroy_transport project objects allocator object.allocation before.memory]
    | arguments =>
      change (match Fields.arguments before.memory descriptor with | .error reason => _ | .ok slice => _) = _
      cases Fields.arguments before.memory descriptor with
      | error reason => rfl
      | ok slice =>
        dsimp only
        rw [external.free allocator slice before.memory]
        rfl
    | invalidate =>
      change (match Expression.invalidate before.memory.memory descriptor with | .error reason => _ | .ok memory => _) = _
      cases Expression.invalidate before.memory.memory descriptor <;> rfl

theorem run_transport (allocator : Nat) (descriptor : Compiler.ZigAir.Memory.Address) (before : Session σ) :
    run rightBytes rightObjects right allocator descriptor (before.mapEffects project) =
      ((run leftBytes leftObjects left allocator descriptor before).1,
       (run leftBytes leftObjects left allocator descriptor before).2.mapEffects project) :=
  executeStages_transport project (step_transport bytes objects external allocator descriptor) expressionDeinitCode ⟨before, false⟩

end Native
end ExpressionDeinit
end Compiler.Extraction
