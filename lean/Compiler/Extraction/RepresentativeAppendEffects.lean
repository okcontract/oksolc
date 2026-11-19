/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.RepresentativeCapacityEffects
import Compiler.Extraction.RepresentativeRegisteredGrowthAppend

namespace Compiler.Extraction.RepresentativeArray.Append
open Compiler.ZigAir.Memory Compiler.Algebraic
open Compiler.Extraction.Memory.Arguments.Normalization

namespace Execution
variable {project : σ → τ}
  {left : State → Address → Nat → σ → (Except ε (Option Unit) × State) × σ}
  {right : State → Address → Nat → τ → (Except ε (Option Unit) × State) × τ}
  (mapped : ∀ state header minimum effects, right state header minimum (project effects) =
    ((left state header minimum effects).1, project (left state header minimum effects).2))
include mapped

/-- One capacity boundary for both routes. The subsequent native length and
descriptor stores are the same execution, including partial rejection. -/
theorem runWithCapacity_transport (reject : Fault → ε) (state : State) (header item arguments : Address)
    (length : Nat) (id sequence : Int) (effects : σ) :
    runWithCapacity reject right state header item arguments length id sequence (project effects) =
      ((runWithCapacity reject left state header item arguments length id sequence effects).1,
       project (runWithCapacity reject left state header item arguments length id sequence effects).2) := by
  unfold runWithCapacity
  split
  · rfl
  · dsimp only
    split
    · rfl
    · rw [mapped]
      cases left state header _ effects with
      | mk outcome reached =>
        rcases outcome with ⟨result, ready⟩
        cases result with
        | error reason => rfl
        | ok value => cases value with
          | none => rfl
          | some value =>
            cases value
            dsimp only
            split <;> rfl
  · rfl

theorem ownerWithCapacity_transport (reject : Fault → ε) (runtimeSafety : Bool) (state : State) (owner item arguments : Address)
    (length : Nat) (id sequence : Int) (effects : σ) :
    ownerWithCapacity reject right runtimeSafety state owner item arguments length id sequence (project effects) =
      ((ownerWithCapacity reject left runtimeSafety state owner item arguments length id sequence effects).1,
       project (ownerWithCapacity reject left runtimeSafety state owner item arguments length id sequence effects).2) := by
  unfold ownerWithCapacity
  split
  · rfl
  · exact runWithCapacity_transport mapped reject state _ item arguments length id sequence effects
  · rfl
end Execution

namespace Registered

theorem admit_transport (project : σ → τ) (allocator lifetime : Nat) (cells : List Storage.Cell) (before : Session σ) :
    admit allocator lifetime cells (before.mapEffects project) = admit allocator lifetime cells before := rfl

theorem finish_transport (project : σ → τ) (allocator owner : Nat) (cells : List Storage.Cell) (cell : Storage.Cell)
    (before reached : Session σ) (registry : Compiler.Extraction.Memory.Heap) :
    finish allocator owner cells cell (before.mapEffects project) (reached.mapEffects project) registry =
      ((finish allocator owner cells cell before reached registry).1,
       (finish allocator owner cells cell before reached registry).2.mapEffects project) := by
  unfold finish
  simp only [Session.mapEffects_memory]
  split
  · rfl
  · split
    · change (match admit allocator _ cells ({ before with heap := registry }.mapEffects project) with | .error reason => _ | .ok () => _) = _
      rw [admit_transport]
      split <;> simp_all only <;> rfl
    · rfl
  · rfl

variable {project : σ → τ} {left : Backing.Registry.Allocate σ} {right : Backing.Registry.Allocate τ}
  (allocated : Backing.Registry.Allocate.Transport project left right)
include allocated

theorem run_transport (runtimeSafety : Bool) (allocator owner : Nat) (cells : List Storage.Cell) (cell : Storage.Cell) :
    Effect.Transport (Session.mapEffects project)
      (run runtimeSafety left allocator owner cells cell) (run runtimeSafety right allocator owner cells cell) := by
  intro before
  unfold run Execution.ownerRun
  dsimp only [Session.mapEffects]
  rw [Execution.ownerWithCapacity_transport (fun state header minimum effects => Capacity.ensure_transport allocated allocator minimum state header effects)]
  cases Execution.ownerWithCapacity _ _ runtimeSafety before.memory _ _ _ _ _ _ before.effects with
  | mk outcome effects =>
    rcases outcome with ⟨result, memory⟩
    cases result with
    | error reason => rfl
    | ok value => cases value with
      | none => rfl
      | some value => cases value; exact finish_transport project allocator owner cells cell before { before with memory, effects } before.heap

variable {leftCalls : Growth.Registered.Callbacks σ} {rightCalls : Growth.Registered.Callbacks τ}
  (calls : Growth.Registered.Callbacks.Transport project leftCalls rightCalls)
include calls

theorem growingCapacity_transport (allocator minimum : Nat) (state : State) (header : Address)
    (context : Compiler.Extraction.Memory.Heap × σ) :
    growingCapacity rightCalls right allocator state header minimum (context.1, project context.2) =
      ((growingCapacity leftCalls left allocator state header minimum context).1,
       (growingCapacity leftCalls left allocator state header minimum context).2.1,
       project (growingCapacity leftCalls left allocator state header minimum context).2.2) := by
  exact congrArg (fun result : Except Backing.Release.Fault (Option Unit) × Session τ =>
    ((result.1.mapError growthFault, result.2.memory), (result.2.heap, result.2.effects)))
    (Capacity.Registered.ensure_transport allocated calls allocator minimum header ⟨context.1, state, context.2⟩)

theorem runWithGrowth_transport (runtimeSafety : Bool) (allocator owner : Nat) (cells : List Storage.Cell) (cell : Storage.Cell) :
    Effect.Transport (Session.mapEffects project)
      (runWithGrowth leftCalls runtimeSafety left allocator owner cells cell)
      (runWithGrowth rightCalls runtimeSafety right allocator owner cells cell) := by
  intro before
  unfold runWithGrowth
  dsimp only [Session.mapEffects]
  rw [Execution.ownerWithCapacity_transport (project := fun context : Compiler.Extraction.Memory.Heap × σ => (context.1, project context.2))
    (fun state header minimum context => growingCapacity_transport allocated calls allocator minimum state header context)
    (fun fault => .memory fault) runtimeSafety before.memory ⟨owner, 0⟩ ⟨cell.itemAddress, 0⟩ ⟨cell.argumentsAddress, 0⟩
    cell.arguments.length (Storage.idFor cells).toNat cell.sequence.toNat (before.heap, before.effects)]
  cases Execution.ownerWithCapacity _ _ runtimeSafety before.memory _ _ _ _ _ _ (before.heap, before.effects) with
  | mk outcome context =>
    rcases outcome with ⟨result, memory⟩
    cases result with
    | error reason => rfl
    | ok value => cases value with
      | none => rfl
      | some value => cases value; exact finish_transport project allocator owner cells cell before ⟨context.1, memory, context.2⟩ context.1

end Registered
end Compiler.Extraction.RepresentativeArray.Append
