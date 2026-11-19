/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityCall

/-! Creation-to-call composition for the closed pure-function source fragment,
whose implicit constructor is nonpayable and has no effects. Exact creation
bytes must return the certified runtime. Address derivation, creator nonce and
message admission precede this frame; gas excludes intrinsic/initcode charges.
No premise assumes the runtime is already installed. -/
namespace Compiler.Validation.SolidityDeployment
open Contract.Evm SolidityFunction

def outcome (runtime : List UInt8) (input : Input) : Halt :=
  if input.value = 0#256 then .returned runtime else .reverted []

def observation (runtime : List UInt8) (world : World) (ctx : Contract.Context)
    (input : Input) (cost gas : Nat) : Observation :=
  if cost ≤ gas then
    if input.value = 0#256 then
      if cost + 200 * runtime.length ≤ gas then
        ⟨.returned, runtime, (world.prepare ctx.self).install ctx.self runtime,
          gas - (cost + 200 * runtime.length)⟩
      else ⟨.exceptional, [], world, 0⟩
    else ⟨.reverted, [], world, gas - cost⟩
  else ⟨.exceptional, [], world, 0⟩

theorem metered (creation runtime : List UInt8) (input : Input) (steps cost : Nat)
    (trace : Contract.Evm.run creation input steps {} = .finished cost (outcome runtime input))
    (fuel gas : Nat) (enough : steps ≤ fuel) :
    runMetered creation input fuel gas {} =
      if cost ≤ gas then .finished (gas - cost) (outcome runtime input) else .exceptional := by
  have longer := run_more creation input steps {} cost (outcome runtime input) (fuel - steps) trace
  rw [show steps + (fuel - steps) = fuel by omega] at longer
  exact metered_of_run creation input fuel {} cost (outcome runtime input) gas longer

theorem frame (creation runtime : List UInt8) (input : Input) (steps cost : Nat)
    (trace : Contract.Evm.run creation input steps {} = .finished cost (outcome runtime input))
    (initSize : creation.length ≤ 49152)
    (runtimeSize : runtime.length ≤ 24576) (runtimePrefix : runtime.head? ≠ some 0xef)
    (world : World) (ctx : Contract.Context) (fresh : Fresh world ctx.self)
    (fuel gas : Nat) (enough : steps ≤ fuel) :
    executeCreation creation world ctx fresh input fuel gas =
      observation runtime world ctx input cost gas := by
  simp only [executeCreation, if_pos initSize,
    metered creation runtime input steps cost trace fuel gas enough]
  by_cases funded : cost ≤ gas
  · by_cases value : input.value = 0#256
    · have deposit : 200 * runtime.length ≤ gas - cost ↔ cost + 200 * runtime.length ≤ gas := by omega
      simp [observation, outcome, funded, value, finishDeployment, runtimeSize, runtimePrefix,
        deposit, World.transfer, Nat.sub_sub]
    · simp [observation, outcome, funded, value, finishDeployment, observeCall]
  · simp [observation, funded, finishDeployment, observeCall]

theorem installed (runtime : List UInt8) (world : World) (ctx : Contract.Context)
    (input : Input) (cost gas : Nat)
    (success : (observation runtime world ctx input cost gas).status = .returned) :
    (observation runtime world ctx input cost gas).world.code ctx.self = runtime := by
  by_cases funded : cost ≤ gas <;> by_cases value : input.value = 0#256 <;>
    by_cases deposit : cost + 200 * runtime.length ≤ gas <;>
    simp_all [observation, World.install]

/-- Source-independent exact creation certificate, reused by single-function
and complete-contract endpoints. -/
def Frames (creation runtime : List UInt8) (steps : Nat) : Prop :=
  ∀ input, ∃ cost,
    Contract.Evm.run creation input steps {} = .finished cost (outcome runtime input) ∧
    ∀ world ctx fresh fuel gas, steps ≤ fuel →
      executeCreation creation world ctx fresh input fuel gas =
        observation runtime world ctx input cost gas

theorem certifyFrames (creation runtime : List UInt8) (steps : Nat)
    (initSize : creation.length ≤ 49152)
    (runtimeSize : runtime.length ≤ 24576) (runtimePrefix : runtime.head? ≠ some 0xef)
    (trace : ∀ input, ∃ cost,
      Contract.Evm.run creation input steps {} = .finished cost (outcome runtime input)) :
    Frames creation runtime steps := by
  intro input
  obtain ⟨cost, checked⟩ := trace input
  exact ⟨cost, checked, frame creation runtime input steps cost checked initSize runtimeSize runtimePrefix⟩

theorem deployable (creation runtime : List UInt8) (steps : Nat)
    (frames : Frames creation runtime steps) (world : World) (ctx : Contract.Context)
    (fresh : Fresh world ctx.self) :
    ∃ gas, (executeCreation creation world ctx fresh {} steps gas).status = .returned := by
  obtain ⟨cost, _, execution⟩ := frames {}
  refine ⟨cost + 200 * runtime.length, ?_⟩
  rw [execution world ctx fresh steps _ (Nat.le_refl _)]
  simp [observation]

/-- Successful checked creation installs the runtime used by subsequent calls.
Share this connection across single-function, complete and empty contracts. -/
theorem installed_of_frames {creation runtime : List UInt8} {steps : Nat}
    (frames : Frames creation runtime steps) (world : World) (ctx : Contract.Context)
    (fresh : Fresh world ctx.self) (input : Input) (fuel gas : Nat) (enough : steps ≤ fuel)
    (success : (executeCreation creation world ctx fresh input fuel gas).status = .returned) :
    (executeCreation creation world ctx fresh input fuel gas).world.code ctx.self = runtime := by
  obtain ⟨cost, _, execution⟩ := frames input
  rw [execution world ctx fresh fuel gas enough] at success ⊢
  exact installed runtime world ctx input cost gas success

/-- The endpoint includes deployment failure observations, a successful
deployment witness, and calls to the code in the world actually produced by
creation. The call size domain is inherited unchanged from `SolidityCall`. -/
def Preserves (source : Source) (creation runtime : List UInt8)
    (creationSteps runtimeSteps : Nat) : Prop :=
  SolidityCall.Preserves source runtime runtimeSteps ∧
  (∀ input, ∃ cost,
    Contract.Evm.run creation input creationSteps {} = .finished cost (outcome runtime input) ∧
    ∀ world ctx fresh fuel gas, creationSteps ≤ fuel →
      executeCreation creation world ctx fresh input fuel gas =
        observation runtime world ctx input cost gas) ∧
  (∀ world ctx fresh, ∃ gas,
    (executeCreation creation world ctx fresh {} creationSteps gas).status = .returned) ∧
  (∀ world ctx fresh input fuel gas, creationSteps ≤ fuel →
    let deployed := executeCreation creation world ctx fresh input fuel gas
    deployed.status = .returned → ∀ caller callInput, SolidityCall.Sized callInput →
      ∃ cost, ∀ callFuel callGas, runtimeSteps ≤ callFuel →
        executeCall deployed.world ⟨caller, ctx.self⟩ callInput callFuel callGas =
          SolidityCall.observation source callInput deployed.world ⟨caller, ctx.self⟩ cost callGas)

theorem certify (source : Source) (creation runtime : List UInt8)
    (creationSteps runtimeSteps : Nat)
    (calls : SolidityCall.Preserves source runtime runtimeSteps)
    (initSize : creation.length ≤ 49152)
    (runtimeSize : runtime.length ≤ 24576) (runtimePrefix : runtime.head? ≠ some 0xef)
    (trace : ∀ input, ∃ cost,
      Contract.Evm.run creation input creationSteps {} = .finished cost (outcome runtime input)) :
    Preserves source creation runtime creationSteps runtimeSteps := by
  have frames := certifyFrames creation runtime creationSteps initSize runtimeSize runtimePrefix trace
  refine ⟨calls, frames, deployable creation runtime creationSteps frames, ?_⟩
  · intro world ctx fresh input fuel gas enough deployed success caller callInput sized
    have code : deployed.world.code ctx.self = runtime :=
      installed_of_frames frames world ctx fresh input fuel gas enough success
    obtain ⟨cost, _, _, execution⟩ := calls.2 callInput sized
    exact ⟨cost, fun callFuel callGas enough =>
      execution deployed.world ⟨caller, ctx.self⟩ callFuel callGas code enough⟩

end Compiler.Validation.SolidityDeployment
