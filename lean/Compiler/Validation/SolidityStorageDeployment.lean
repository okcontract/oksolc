/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityStorage

/-! Complete deployment-to-storage-call certificates. The admitted contracts
have an implicit nonpayable constructor and zero-initialized full-word slots.
The exact creation code must leave storage, warming and refunds unchanged and
return precisely the certified runtime. No installed-code premise survives the
composed endpoint. Transaction/CREATE admission still precedes this frame. -/
namespace Compiler.Validation.SolidityStorage
open Contract.Evm SolidityCall

def creationEffects (runtime : List UInt8) (input : Input) (state : Stateful.State) : Stateful.Effects :=
  ⟨SolidityDeployment.outcome runtime input, state.storage, state.warm, state.refund⟩

theorem store_initial (world : World) (target : Address) :
    Stateful.World.store world target (world.storage target) = world := by
  unfold Stateful.World.store
  have same : (fun a => if a = target then world.storage target else world.storage a) = world.storage := by
    funext a
    split <;> simp_all
  rw [same]

theorem commit_initial (world : World) (transaction : Stateful.Transaction) (target : Address) :
    transaction.commit target (Stateful.initial world transaction target) = transaction := by
  unfold Stateful.Transaction.commit Stateful.initial
  have same : (fun a => if a = target then transaction.warm target else transaction.warm a) = transaction.warm := by
    funext a
    split <;> simp_all
  rw [same]

theorem creation_frame (creation runtime : List UInt8) (steps : Nat)
    (initSize : creation.length ≤ 49152) (runtimeSize : runtime.length ≤ 24576)
    (runtimePrefix : runtime.head? ≠ some 0xef)
    (world : World) (transaction : Stateful.Transaction) (ctx : Contract.Context)
    (fresh : Fresh world ctx.self) (input : Input) (cost : Nat)
    (trace : (Stateful.run creation input ⟨transaction.original ctx.self, false⟩ steps
        (Stateful.initial world transaction ctx.self)).map Stateful.Result.effects =
      .finished cost cost (creationEffects runtime input (Stateful.initial world transaction ctx.self)))
    (fuel gas : Nat) (enough : steps ≤ fuel) :
    Stateful.executeCreation creation world transaction ctx fresh input fuel gas =
      ⟨SolidityDeployment.observation runtime world ctx input cost gas, transaction⟩ := by
  unfold Stateful.executeCreation
  rw [if_pos initSize, Stateful.creation_projected,
    metered_finished creation input ⟨transaction.original ctx.self, false⟩
      (Stateful.initial world transaction ctx.self) steps cost cost _ trace fuel gas enough]
  by_cases funded : cost ≤ gas
  · by_cases value : input.value = 0#256
    · have deposit : 200 * runtime.length ≤ gas - cost ↔ cost + 200 * runtime.length ≤ gas := by omega
      have stored : Stateful.World.store (world.prepare ctx.self) ctx.self (world.storage ctx.self) =
          world.prepare ctx.self := store_initial (world.prepare ctx.self) ctx.self
      simp [Guarded.Metered.map, creationEffects, SolidityDeployment.outcome, SolidityDeployment.observation,
        funded, value, Stateful.finishCreation, Stateful.Effects.result, Stateful.initial,
        finishDeployment, runtimeSize, runtimePrefix, deposit, World.transfer, stored, Nat.sub_sub]
      split <;> simp_all [Stateful.Transaction.commit]
      exact commit_initial world transaction ctx.self
    · simp [Guarded.Metered.map, creationEffects, SolidityDeployment.outcome, SolidityDeployment.observation,
        funded, value, Stateful.finishCreation, Stateful.observe, Stateful.Effects.result]
  · simp [Guarded.Metered.map, SolidityDeployment.observation, funded, Stateful.finishCreation, Stateful.observe]

def CreationPreserves (creation runtime : List UInt8) (steps : Nat) : Prop :=
  ∀ input (state : Stateful.State) (original : Stateful.Slots), ∃ cost,
    (Stateful.run creation input ⟨original, false⟩ steps { state with machine := {} }).map Stateful.Result.effects =
      .finished cost cost (creationEffects runtime input state)

def Preserves (source : ContractSource) (creation runtime : List UInt8)
    (creationSteps runtimeSteps : Nat) : Prop :=
  CallsPreserves source runtime runtimeSteps ∧
  CreationPreserves creation runtime creationSteps ∧
  (∀ world transaction ctx fresh input, ∃ cost, ∀ fuel gas, creationSteps ≤ fuel →
    Stateful.executeCreation creation world transaction ctx fresh input fuel gas =
      ⟨SolidityDeployment.observation runtime world ctx input cost gas, transaction⟩) ∧
  (∀ world transaction ctx fresh, ∃ gas,
    (Stateful.executeCreation creation world transaction ctx fresh {} creationSteps gas).status = .returned) ∧
  (∀ world transaction ctx fresh input fuel gas, creationSteps ≤ fuel →
    let deployed := Stateful.executeCreation creation world transaction ctx fresh input fuel gas
    deployed.status = .returned → ∀ caller callInput isStatic, Sized callInput →
      CallPreserves source runtime runtimeSteps deployed.world deployed.transaction
        ⟨caller, ctx.self⟩ callInput isStatic)

theorem certify (source : ContractSource) (creation runtime : List UInt8)
    (creationSteps runtimeSteps : Nat)
    (calls : CallsPreserves source runtime runtimeSteps)
    (initSize : creation.length ≤ 49152) (runtimeSize : runtime.length ≤ 24576)
    (runtimePrefix : runtime.head? ≠ some 0xef)
    (trace : CreationPreserves creation runtime creationSteps) :
    Preserves source creation runtime creationSteps runtimeSteps := by
  have frames : ∀ world transaction ctx fresh input, ∃ cost, ∀ fuel gas, creationSteps ≤ fuel →
      Stateful.executeCreation creation world transaction ctx fresh input fuel gas =
        ⟨SolidityDeployment.observation runtime world ctx input cost gas, transaction⟩ := by
    intro world transaction ctx fresh input
    obtain ⟨cost, checked⟩ := trace input (Stateful.initial world transaction ctx.self)
      (transaction.original ctx.self)
    exact ⟨cost, creation_frame creation runtime creationSteps initSize runtimeSize runtimePrefix
      world transaction ctx fresh input cost checked⟩
  refine ⟨calls, trace, frames, ?_, ?_⟩
  · intro world transaction ctx fresh
    obtain ⟨cost, execution⟩ := frames world transaction ctx fresh {}
    refine ⟨cost + 200 * runtime.length, ?_⟩
    rw [execution creationSteps _ (Nat.le_refl _)]
    simp [SolidityDeployment.observation]
  · intro world transaction ctx fresh input fuel gas enough deployed success caller callInput isStatic sized
    obtain ⟨cost, execution⟩ := frames world transaction ctx fresh input
    have installed : deployed.world.code ctx.self = runtime := by
      dsimp only [deployed] at *
      rw [execution fuel gas enough] at success ⊢
      exact SolidityDeployment.installed runtime world ctx input cost gas success
    exact calls.preserve deployed.world deployed.transaction ⟨caller, ctx.self⟩ callInput isStatic sized installed

end Compiler.Validation.SolidityStorage
