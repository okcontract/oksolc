/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityStorageDeployment

/-! Deployment preservation parameterized by the complete source creation
outcome. Initialization and explicit constructors share this single frame,
installation and subsequent-call proof. -/
namespace Compiler.Validation.SolidityStorage.Creation
open Contract.Evm
open Contract.Interaction (Word)

def expected (runtime : List UInt8) : Outcome → Outcome
  | .returned _ cells => .returned runtime cells
  | .reverted bytes => .reverted bytes
  | .fault => .fault

def TracePreserves (initial : Input → Outcome)
    (creation runtime : List UInt8) (steps : Nat) : Prop :=
  ∀ input (state : Stateful.State) (original : Stateful.Slots),
    Conforms (expected runtime (initial input))
      ((Stateful.run creation input ⟨original, false⟩ steps
        { state with machine := {}, storage := fun _ => 0 }).map Stateful.Result.effects)

def observation (world : World) (transaction : Stateful.Transaction) (ctx : Contract.Context)
    (input : Input) (trace : Guarded.Trace Stateful.Effects) (gas : Nat) : Stateful.Frame :=
  Stateful.finishCreation world (world.prepare ctx.self) transaction ctx input
    ((meter trace gas).map Stateful.Effects.result)

def FramePreserves (initial : Input → Outcome)
    (creation runtime : List UInt8) (steps : Nat) (world : World) (transaction : Stateful.Transaction)
    (ctx : Contract.Context) (fresh : Fresh world ctx.self) (input : Input) : Prop :=
  ∃ trace, Conforms (expected runtime (initial input)) trace ∧
    (Stateful.run creation input ⟨transaction.original ctx.self, false⟩ steps
      (Stateful.initial world transaction ctx.self)).map Stateful.Result.effects = trace ∧
    ∀ fuel gas, steps ≤ fuel → Stateful.executeCreation creation world transaction ctx fresh input fuel gas =
      observation world transaction ctx input trace gas

theorem frame (initial : Input → Outcome)
    (creation runtime : List UInt8) (steps : Nat) (initSize : creation.length ≤ 49152)
    (trace : TracePreserves initial creation runtime steps)
    (world transaction ctx) (fresh : Fresh world ctx.self) (input : Input) :
    FramePreserves initial creation runtime steps world transaction ctx fresh input := by
  let state := Stateful.initial world transaction ctx.self
  have zero : world.storage ctx.self = fun _ => 0 := funext fresh.2.2
  have checked := trace input state (transaction.original ctx.self)
  have shape : { state with machine := {}, storage := fun _ => 0 } = state := by
    simp only [state, Stateful.initial, zero]
  rw [shape] at checked
  refine ⟨_, checked, rfl, ?_⟩
  intro fuel gas enough
  unfold Stateful.executeCreation
  rw [if_pos initSize, Stateful.creation_projected,
    metered _ creation input ⟨transaction.original ctx.self, false⟩ state steps checked fuel gas enough]
  rfl

theorem installed (runtime : List UInt8) (source : Outcome)
    (world transaction ctx input trace gas)
    (checked : Conforms (expected runtime source) trace)
    (success : (observation world transaction ctx input trace gas).status = .returned) :
    ∃ bytes cells, source = .returned bytes cells ∧
      (observation world transaction ctx input trace gas).world.code ctx.self = runtime ∧
      (observation world transaction ctx input trace gas).world.storage ctx.self = cells := by
  cases source with
  | fault =>
    change trace = .fault at checked
    subst trace
    simp [observation, meter, Guarded.Metered.map, Stateful.finishCreation, Stateful.observe] at success
  | reverted bytes =>
    obtain ⟨used, needed, cells, warm, refund, rfl⟩ := checked
    simp only [observation, meter] at success
    split at success <;> simp [Guarded.Metered.map, Stateful.finishCreation, Stateful.observe,
      Stateful.Effects.result] at success
  | returned bytes cells =>
    obtain ⟨used, needed, warm, refund, rfl⟩ := checked
    by_cases funded : needed ≤ gas
    · by_cases deposit : runtime.length ≤ 24576 ∧ runtime.head? ≠ some 0xef ∧ 200 * runtime.length ≤ gas - used
      · refine ⟨bytes, cells, rfl, ?_, ?_⟩ <;>
          simp [observation, meter, funded, Guarded.Metered.map, Stateful.finishCreation,
            Stateful.Effects.result, finishDeployment, deposit, World.install, World.transfer,
            Stateful.World.store] <;> split <;> simp
      · simp [observation, meter, funded, Guarded.Metered.map, Stateful.finishCreation,
          Stateful.Effects.result, finishDeployment, deposit] at success
    · simp [observation, meter, funded, Guarded.Metered.map, Stateful.finishCreation, Stateful.observe] at success

theorem deployable (runtime : List UInt8) (bytes : List UInt8) (cells : Stateful.Slots) (world transaction ctx input trace)
    (size : runtime.length ≤ 24576) (runtimePrefix : runtime.head? ≠ some 0xef)
    (checked : Conforms (expected runtime (.returned bytes cells)) trace) :
    ∃ gas, (observation world transaction ctx input trace gas).status = .returned := by
  obtain ⟨used, needed, warm, refund, rfl⟩ := checked
  refine ⟨max needed (used + 200 * runtime.length), ?_⟩
  have funded : needed ≤ max needed (used + 200 * runtime.length) := Nat.le_max_left _ _
  have deposit : 200 * runtime.length ≤ max needed (used + 200 * runtime.length) - used := by omega
  simp [observation, meter, funded, Guarded.Metered.map, Stateful.finishCreation,
    Stateful.Effects.result, finishDeployment, size, runtimePrefix, deposit]

def Preserves (source : ContractSource) (initial : Input → Outcome)
    (creation runtime : List UInt8) (creationSteps runtimeSteps : Nat) : Prop :=
  CallsPreserves source runtime runtimeSteps ∧
  TracePreserves initial creation runtime creationSteps ∧
  (∀ world transaction ctx fresh input,
    FramePreserves initial creation runtime creationSteps world transaction ctx fresh input) ∧
  (∀ world transaction ctx fresh bytes cells, initial {} = .returned bytes cells → ∃ gas,
    (Stateful.executeCreation creation world transaction ctx fresh {} creationSteps gas).status = .returned) ∧
  (∀ world transaction ctx fresh input fuel gas, creationSteps ≤ fuel →
    let deployed := Stateful.executeCreation creation world transaction ctx fresh input fuel gas
    deployed.status = .returned → ∃ bytes cells, initial input = .returned bytes cells ∧
      deployed.world.code ctx.self = runtime ∧
      deployed.world.storage ctx.self = cells ∧
      ∀ caller callInput isStatic, SolidityCall.Sized callInput →
        CallPreserves source runtime runtimeSteps deployed.world deployed.transaction
          ⟨caller, ctx.self⟩ callInput isStatic)

/-- Exact source creation outcome, all gas budgets, store/code installation
and every subsequent call compose. A reverting source need not deploy. -/
theorem certify (source : ContractSource) (initial : Input → Outcome)
    (creation runtime : List UInt8) (creationSteps runtimeSteps : Nat)
    (calls : CallsPreserves source runtime runtimeSteps)
    (initSize : creation.length ≤ 49152) (runtimeSize : runtime.length ≤ 24576)
    (runtimePrefix : runtime.head? ≠ some 0xef)
    (trace : TracePreserves initial creation runtime creationSteps) :
    Preserves source initial creation runtime creationSteps runtimeSteps := by
  have frames := frame initial creation runtime creationSteps initSize trace
  refine ⟨calls, trace, frames, ?_, ?_⟩
  · intro world transaction ctx fresh bytes cells initialized
    obtain ⟨target, checked, _, executed⟩ := frames world transaction ctx fresh {}
    rw [initialized] at checked
    obtain ⟨gas, success⟩ := deployable runtime bytes cells world transaction ctx {} target runtimeSize runtimePrefix checked
    exact ⟨gas, by rw [executed _ _ (Nat.le_refl _)]; exact success⟩
  · intro world transaction ctx fresh input fuel gas enough deployed success
    obtain ⟨target, checked, _, executed⟩ := frames world transaction ctx fresh input
    have ran : deployed = observation world transaction ctx input target gas := executed fuel gas enough
    obtain ⟨bytes, cells, initialized, code, stored⟩ := installed runtime _ world transaction ctx input target gas checked (by rwa [← ran])
    refine ⟨bytes, cells, initialized, by rwa [ran], by rwa [ran], ?_⟩
    intro caller callInput isStatic sized
    exact calls.preserve deployed.world deployed.transaction ⟨caller, ctx.self⟩ callInput isStatic sized (by rwa [ran])

end Compiler.Validation.SolidityStorage.Creation
