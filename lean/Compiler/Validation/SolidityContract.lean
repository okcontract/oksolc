/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityDispatch

/-! Exact-byte certificates for complete contracts in the closed expression
fragment with per-function payability. Selection uses the source signature's
Keccak selector. Every declared function has a canonical-call witness, and
duplicate selectors are excluded.
All runtime traces start at PC zero in the same complete bytecode image. -/
namespace Compiler.Validation.SolidityContract
open Contract.Evm SolidityFunction SolidityCall

def select (sources : List Source) (input : Input) : Option Source :=
  sources.find? fun source => decide
    (loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector)

def outcome (sources : List Source) (input : Input) : Halt :=
  if input.calldata.length < 4 then .reverted [] else
    match select sources input with
    | none => .reverted []
    | some source => SolidityCall.outcome source input

def observation (sources : List Source) (input : Input) (world : World)
    (ctx : Contract.Context) (cost gas : Nat) : Observation :=
  if cost ≤ gas then
    match outcome sources input with
    | .returned bytes => ⟨.returned, bytes, world.transfer ctx.caller ctx.self input.value, gas - cost⟩
    | .reverted bytes => ⟨.reverted, bytes, world, gas - cost⟩
  else ⟨.exceptional, [], world, 0⟩

private theorem dispatch_outcome (sources : List Source) (input : Input) :
    SolidityDispatch.outcome Source.selector SolidityCall.outcome sources input = outcome sources input := by
  unfold SolidityDispatch.outcome outcome SolidityDispatch.select select
  split
  · rfl
  · split <;> simp_all only

private theorem dispatch_observation (sources : List Source) (input : Input) (world : World)
    (ctx : Contract.Context) (cost gas : Nat) :
    SolidityDispatch.observation Source.selector SolidityCall.outcome sources input world ctx cost gas =
      observation sources input world ctx cost gas := by
  simp only [SolidityDispatch.observation, observation, dispatch_outcome]
  split <;> rfl

theorem dispatch (sources : List Source) (code : List UInt8) (steps : Nat)
    (short : ∀ input, Sized input → input.calldata.length < 4 → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (unknown : ∀ input, Sized input → 4 ≤ input.calldata.length →
      (∀ source ∈ sources,
        loadWord input.calldata 0 >>> 224 ≠ BitVec.ofNat 256 source.selector) → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (selected : ∀ source ∈ sources, ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (SolidityCall.outcome source input)) :
    ∀ input, Sized input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (outcome sources input) := by
  simpa only [dispatch_outcome] using
    SolidityDispatch.dispatch Source.selector SolidityCall.outcome sources code steps short unknown selected

/-- Combine the selected function's argument/value paths without assuming
anything about another function's entry point or an unknown-selector path. -/
theorem selected (source : Source) (code : List UInt8) (steps : Nat)
    (paid : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → ¬AcceptsValue source input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (truncated : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → AcceptsValue source input →
      input.calldata.length < 4 + 32 * source.parameters.length → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (returned : ∀ input, Sized input → Accepts source input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (source.result input))
    (input : Input) (sized : Sized input) (header : 4 ≤ input.calldata.length)
    (matched : loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector) :
    ∃ cost, Contract.Evm.run code input steps {} = .finished cost (SolidityCall.outcome source input) := by
  by_cases value : AcceptsValue source input
  · by_cases full : 4 + 32 * source.parameters.length ≤ input.calldata.length
    · simpa only [SolidityCall.outcome, if_pos (show Accepts source input from ⟨value, full, matched⟩)] using
        returned input sized ⟨value, full, matched⟩
    · have rejected : ¬Accepts source input := fun accepted => full accepted.2.1
      simpa only [SolidityCall.outcome, if_neg rejected] using
        truncated input sized header matched value (Nat.lt_of_not_ge full)
  · have rejected : ¬Accepts source input := fun accepted => value accepted.1
    simpa only [SolidityCall.outcome, if_neg rejected] using paid input sized header matched value

theorem metered (sources : List Source) (code : List UInt8) (input : Input) (steps cost : Nat)
    (trace : Contract.Evm.run code input steps {} = .finished cost (outcome sources input))
    (fuel gas : Nat) (enough : steps ≤ fuel) :
    runMetered code input fuel gas {} =
      if cost ≤ gas then .finished (gas - cost) (outcome sources input) else .exceptional := by
  simpa only [dispatch_outcome] using SolidityDispatch.metered Source.selector SolidityCall.outcome sources code input steps cost
    (by simpa only [dispatch_outcome] using trace) fuel gas enough

theorem frame (sources : List Source) (code : List UInt8) (input : Input) (steps cost : Nat)
    (trace : Contract.Evm.run code input steps {} = .finished cost (outcome sources input))
    (world : World) (ctx : Contract.Context) (fuel gas : Nat)
    (installed : world.code ctx.self = code) (enough : steps ≤ fuel) :
    executeCall world ctx input fuel gas = observation sources input world ctx cost gas := by
  simpa only [dispatch_observation] using SolidityDispatch.frame Source.selector SolidityCall.outcome sources code input steps cost
    (by simpa only [dispatch_outcome] using trace) world ctx fuel gas installed enough

def CallsPreserves (sources : List Source) (code : List UInt8) (steps : Nat) : Prop :=
  sources ≠ [] ∧
  (sources.map fun source => BitVec.ofNat 256 source.selector).Nodup ∧
  (∀ source ∈ sources, ∃ input, Sized input ∧ source.ValidCall input) ∧
  ∀ input, Sized input → ∃ cost,
    Contract.Evm.run code input steps {} = .finished cost (outcome sources input) ∧
    (∀ fuel gas, steps ≤ fuel → runMetered code input fuel gas {} =
      if cost ≤ gas then .finished (gas - cost) (outcome sources input) else .exceptional) ∧
    (∀ world ctx fuel gas, world.code ctx.self = code → steps ≤ fuel →
      executeCall world ctx input fuel gas = observation sources input world ctx cost gas)

theorem certifyCalls (sources : List Source) (code : List UInt8) (steps : Nat)
    (nonempty : sources ≠ [])
    (unique : (sources.map fun source => BitVec.ofNat 256 source.selector).Nodup)
    (inhabited : ∀ source ∈ sources, ∃ input, Sized input ∧ source.ValidCall input)
    (trace : ∀ input, Sized input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (outcome sources input)) :
    CallsPreserves sources code steps := by
  simpa only [SolidityDispatch.CallsPreserves, CallsPreserves, dispatch_outcome, dispatch_observation] using
    SolidityDispatch.certifyCalls Source.selector SolidityCall.outcome Source.ValidCall sources code steps nonempty unique inhabited
      (by simpa only [dispatch_outcome] using trace)

def Preserves (sources : List Source) (creation runtime : List UInt8)
    (creationSteps runtimeSteps : Nat) : Prop :=
  CallsPreserves sources runtime runtimeSteps ∧
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
          observation sources callInput deployed.world ⟨caller, ctx.self⟩ cost callGas)

theorem certify (sources : List Source) (creation runtime : List UInt8)
    (creationSteps runtimeSteps : Nat)
    (calls : CallsPreserves sources runtime runtimeSteps)
    (initSize : creation.length ≤ 49152)
    (runtimeSize : runtime.length ≤ 24576) (runtimePrefix : runtime.head? ≠ some 0xef)
    (trace : ∀ input, ∃ cost,
      Contract.Evm.run creation input creationSteps {} = .finished cost (SolidityDeployment.outcome runtime input)) :
    Preserves sources creation runtime creationSteps runtimeSteps := by
  simpa only [SolidityDispatch.Preserves, Preserves, SolidityDispatch.CallsPreserves, CallsPreserves, dispatch_outcome, dispatch_observation] using
    SolidityDispatch.certify Source.selector SolidityCall.outcome Source.ValidCall sources creation runtime creationSteps runtimeSteps
      (by simpa only [SolidityDispatch.CallsPreserves, CallsPreserves, dispatch_outcome, dispatch_observation] using calls)
      initSize runtimeSize runtimePrefix trace

end Compiler.Validation.SolidityContract
