/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityDeployment

/-! Shared exact-byte dispatch, metering and deployment certificates. Each
source method supplies its own signature, admitted-call domain and behavior;
complete runtime traces and a witness for every method remain mandatory. -/
namespace Compiler.Validation.SolidityDispatch
open Contract.Evm SolidityFunction SolidityCall

variable {α : Type} (selector : α → Nat) (method : α → Input → Halt)
  (validCall : α → Input → Prop)

def select (sources : List α) (input : Input) : Option α :=
  sources.find? fun source => decide
    (loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 (selector source))

def outcome (sources : List α) (input : Input) : Halt :=
  if input.calldata.length < 4 then .reverted [] else
    match select selector sources input with
    | none => .reverted []
    | some source => method source input

def observation (sources : List α) (input : Input) (world : World)
    (ctx : Contract.Context) (cost gas : Nat) : Observation :=
  if cost ≤ gas then
    match outcome selector method sources input with
    | .returned bytes => ⟨.returned, bytes, world.transfer ctx.caller ctx.self input.value, gas - cost⟩
    | .reverted bytes => ⟨.reverted, bytes, world, gas - cost⟩
  else ⟨.exceptional, [], world, 0⟩

theorem dispatch (sources : List α) (code : List UInt8) (steps : Nat)
    (short : ∀ input, Sized input → input.calldata.length < 4 → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (unknown : ∀ input, Sized input → 4 ≤ input.calldata.length →
      (∀ source ∈ sources,
        loadWord input.calldata 0 >>> 224 ≠ BitVec.ofNat 256 (selector source)) → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (selected : ∀ source ∈ sources, ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 (selector source) → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (method source input)) :
    ∀ input, Sized input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (outcome selector method sources input) := by
  intro input sized
  by_cases header : input.calldata.length < 4
  · simpa only [outcome, if_pos header] using short input sized header
  · cases found : select selector sources input with
    | none =>
      have absent := List.find?_eq_none.mp found
      have rejected : ∀ source ∈ sources,
          loadWord input.calldata 0 >>> 224 ≠ BitVec.ofNat 256 (selector source) := by
        simpa only [decide_eq_true_eq] using absent
      simpa only [outcome, if_neg header, found] using
        unknown input sized (Nat.le_of_not_gt header) rejected
    | some source =>
      have member := List.mem_of_find?_eq_some found
      have matched := List.find?_some found
      have matched : loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 (selector source) := by
        simpa only [decide_eq_true_eq] using matched
      simpa only [outcome, if_neg header, found] using
        selected source member input sized (Nat.le_of_not_gt header) matched

theorem metered (sources : List α) (code : List UInt8) (input : Input) (steps cost : Nat)
    (trace : Contract.Evm.run code input steps {} = .finished cost (outcome selector method sources input))
    (fuel gas : Nat) (enough : steps ≤ fuel) :
    runMetered code input fuel gas {} =
      if cost ≤ gas then .finished (gas - cost) (outcome selector method sources input) else .exceptional := by
  have longer := run_more code input steps {} cost (outcome selector method sources input) (fuel - steps) trace
  rw [show steps + (fuel - steps) = fuel by omega] at longer
  exact metered_of_run code input fuel {} cost (outcome selector method sources input) gas longer

theorem frame (sources : List α) (code : List UInt8) (input : Input) (steps cost : Nat)
    (trace : Contract.Evm.run code input steps {} = .finished cost (outcome selector method sources input))
    (world : World) (ctx : Contract.Context) (fuel gas : Nat)
    (installed : world.code ctx.self = code) (enough : steps ≤ fuel) :
    executeCall world ctx input fuel gas = observation selector method sources input world ctx cost gas := by
  simp only [executeCall, installed, metered selector method sources code input steps cost trace fuel gas enough]
  by_cases funded : cost ≤ gas
  · cases result : outcome selector method sources input <;> simp [observation, funded, result, observeCall]
  · simp [observation, funded, observeCall]

def CallsPreserves (sources : List α) (code : List UInt8) (steps : Nat) : Prop :=
  sources ≠ [] ∧
  (sources.map fun source => BitVec.ofNat 256 (selector source)).Nodup ∧
  (∀ source ∈ sources, ∃ input, Sized input ∧ validCall source input) ∧
  ∀ input, Sized input → ∃ cost,
    Contract.Evm.run code input steps {} = .finished cost (outcome selector method sources input) ∧
    (∀ fuel gas, steps ≤ fuel → runMetered code input fuel gas {} =
      if cost ≤ gas then .finished (gas - cost) (outcome selector method sources input) else .exceptional) ∧
    (∀ world ctx fuel gas, world.code ctx.self = code → steps ≤ fuel →
      executeCall world ctx input fuel gas = observation selector method sources input world ctx cost gas)

theorem certifyCalls (sources : List α) (code : List UInt8) (steps : Nat)
    (nonempty : sources ≠ [])
    (unique : (sources.map fun source => BitVec.ofNat 256 (selector source)).Nodup)
    (inhabited : ∀ source ∈ sources, ∃ input, Sized input ∧ validCall source input)
    (trace : ∀ input, Sized input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (outcome selector method sources input)) :
    CallsPreserves selector method validCall sources code steps := by
  refine ⟨nonempty, unique, inhabited, fun input sized => ?_⟩
  obtain ⟨cost, checked⟩ := trace input sized
  exact ⟨cost, checked, metered selector method sources code input steps cost checked,
    fun world ctx fuel gas installed enough =>
      frame selector method sources code input steps cost checked world ctx fuel gas installed enough⟩

def Preserves (sources : List α) (creation runtime : List UInt8)
    (creationSteps runtimeSteps : Nat) : Prop :=
  CallsPreserves selector method validCall sources runtime runtimeSteps ∧
  (∀ input, ∃ cost,
    Contract.Evm.run creation input creationSteps {} = .finished cost (SolidityDeployment.outcome runtime input) ∧
    ∀ world ctx fresh fuel gas, creationSteps ≤ fuel →
      executeCreation creation world ctx fresh input fuel gas =
        SolidityDeployment.observation runtime world ctx input cost gas) ∧
  (∀ world ctx fresh, ∃ gas,
    (executeCreation creation world ctx fresh {} creationSteps gas).status = .returned) ∧
  (∀ world ctx fresh input fuel gas, creationSteps ≤ fuel →
    let deployed := executeCreation creation world ctx fresh input fuel gas
    deployed.status = .returned → ∀ caller callInput, Sized callInput →
      ∃ cost, ∀ callFuel callGas, runtimeSteps ≤ callFuel →
        executeCall deployed.world ⟨caller, ctx.self⟩ callInput callFuel callGas =
          observation selector method sources callInput deployed.world ⟨caller, ctx.self⟩ cost callGas)

theorem certify (sources : List α) (creation runtime : List UInt8)
    (creationSteps runtimeSteps : Nat)
    (calls : CallsPreserves selector method validCall sources runtime runtimeSteps)
    (initSize : creation.length ≤ 49152)
    (runtimeSize : runtime.length ≤ 24576) (runtimePrefix : runtime.head? ≠ some 0xef)
    (trace : ∀ input, ∃ cost,
      Contract.Evm.run creation input creationSteps {} = .finished cost (SolidityDeployment.outcome runtime input)) :
    Preserves selector method validCall sources creation runtime creationSteps runtimeSteps := by
  have frames := SolidityDeployment.certifyFrames creation runtime creationSteps
    initSize runtimeSize runtimePrefix trace
  refine ⟨calls, frames, SolidityDeployment.deployable creation runtime creationSteps frames, ?_⟩
  · intro world ctx fresh input fuel gas enough deployed success caller callInput sized
    have code : deployed.world.code ctx.self = runtime :=
      SolidityDeployment.installed_of_frames frames world ctx fresh input fuel gas enough success
    obtain ⟨cost, _, _, execution⟩ := calls.2.2.2 callInput sized
    exact ⟨cost, fun callFuel callGas enough =>
      execution deployed.world ⟨caller, ctx.self⟩ callFuel callGas code enough⟩

end Compiler.Validation.SolidityDispatch
