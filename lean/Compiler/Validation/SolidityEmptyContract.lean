/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityContract

/-! Complete certificates for a source contract with no functions, fallback,
receive handler, state or explicit constructor. Runtime rejection is proved for
every input, not by quantifying over an empty list of selected functions. The
existing nonempty-contract certificate keeps its function-witness requirement. -/
namespace Compiler.Validation.SolidityEmptyContract
open Contract.Evm SolidityFunction SolidityCall

@[simp] theorem outcome_empty (input : Input) : SolidityContract.outcome [] input = .reverted [] := by
  simp [SolidityContract.outcome, SolidityContract.select]

def CallsPreserves (code : List UInt8) (steps : Nat) : Prop :=
  ∀ input, ∃ cost,
    Contract.Evm.run code input steps {} = .finished cost (.reverted []) ∧
    (∀ fuel gas, steps ≤ fuel → runMetered code input fuel gas {} =
      if cost ≤ gas then .finished (gas - cost) (.reverted []) else .exceptional) ∧
    (∀ world ctx fuel gas, world.code ctx.self = code → steps ≤ fuel →
      executeCall world ctx input fuel gas = SolidityContract.observation [] input world ctx cost gas)

theorem certifyCalls (code : List UInt8) (steps : Nat)
    (trace : ∀ input, ∃ cost, Contract.Evm.run code input steps {} = .finished cost (.reverted [])) :
    CallsPreserves code steps := by
  intro input
  obtain ⟨cost, checked⟩ := trace input
  have same : Contract.Evm.run code input steps {} = .finished cost (SolidityContract.outcome [] input) := by
    simpa only [outcome_empty] using checked
  refine ⟨cost, checked, ?_, ?_⟩
  · simpa only [outcome_empty] using SolidityContract.metered [] code input steps cost same
  · exact fun world ctx fuel gas installed enough =>
      SolidityContract.frame [] code input steps cost same world ctx fuel gas installed enough

/-- Includes failure and rollback at every gas budget, a successful deployment
witness and calls to the runtime in the world actually returned by creation. -/
def Preserves (creation runtime : List UInt8) (creationSteps runtimeSteps : Nat) : Prop :=
  CallsPreserves runtime runtimeSteps ∧
  SolidityDeployment.Frames creation runtime creationSteps ∧
  (∀ world ctx fresh, ∃ gas,
    (executeCreation creation world ctx fresh {} creationSteps gas).status = .returned) ∧
  (∀ world ctx fresh input fuel gas, creationSteps ≤ fuel →
    let deployed := executeCreation creation world ctx fresh input fuel gas
    deployed.status = .returned → ∀ caller callInput, ∃ cost,
      ∀ callFuel callGas, runtimeSteps ≤ callFuel →
        executeCall deployed.world ⟨caller, ctx.self⟩ callInput callFuel callGas =
          SolidityContract.observation [] callInput deployed.world ⟨caller, ctx.self⟩ cost callGas)

theorem certify (creation runtime : List UInt8) (creationSteps runtimeSteps : Nat)
    (calls : CallsPreserves runtime runtimeSteps)
    (initSize : creation.length ≤ 49152)
    (runtimeSize : runtime.length ≤ 24576) (runtimePrefix : runtime.head? ≠ some 0xef)
    (trace : ∀ input, ∃ cost,
      Contract.Evm.run creation input creationSteps {} = .finished cost (SolidityDeployment.outcome runtime input)) :
    Preserves creation runtime creationSteps runtimeSteps := by
  have frames := SolidityDeployment.certifyFrames creation runtime creationSteps initSize runtimeSize runtimePrefix trace
  refine ⟨calls, frames, SolidityDeployment.deployable creation runtime creationSteps frames, ?_⟩
  intro world ctx fresh input fuel gas enough deployed success caller callInput
  have installed : deployed.world.code ctx.self = runtime :=
    SolidityDeployment.installed_of_frames frames world ctx fresh input fuel gas enough success
  obtain ⟨cost, _, _, execution⟩ := calls callInput
  exact ⟨cost, fun callFuel callGas enough => execution deployed.world ⟨caller, ctx.self⟩ callFuel callGas installed enough⟩

end Compiler.Validation.SolidityEmptyContract
