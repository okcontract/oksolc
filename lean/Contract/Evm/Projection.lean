/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Contract.Evm.StorageFrames
import Contract.Interaction.MemoryProofs

namespace Contract.Evm.Guarded

def Trace.map (f : α → β) : Trace α → Trace β
  | .finished used needed value => .finished used needed (f value)
  | .fault => .fault
  | .unsupported op => .unsupported op
  | .exhausted => .exhausted

def Metered.map (f : α → β) : Metered α → Metered β
  | .finished remaining value => .finished remaining (f value)
  | .exceptional => .exceptional
  | .unsupported op => .unsupported op
  | .exhausted => .exhausted

theorem Trace.map_charge (f : α → β) (trace : Trace α) (cost guard : Nat) :
    (trace.charge cost guard).map f = (trace.map f).charge cost guard := by cases trace <;> rfl

/-- Projection erases unobservable machine internals, never gas or failure. -/
theorem mapped_more (step : σ → Step σ α) (f : α → β) (fuel state used needed result extra)
    (h : (run step fuel state).map f = .finished used needed result) :
    (run step (fuel + extra) state).map f = .finished used needed result := by
  cases hr : run step fuel state <;> simp [hr, Trace.map] at h
  case finished u n r =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [run_more _ _ _ _ _ _ _ hr]
    rfl

theorem mapped_metered (step : σ → Step σ α) (f : α → β) (fuel state used needed result gas)
    (h : (run step fuel state).map f = .finished used needed result) :
    (runMetered step fuel gas state).map f =
      if needed ≤ gas then .finished (gas - used) result else .exceptional := by
  cases hr : run step fuel state <;> simp [hr, Trace.map] at h
  case finished u n r =>
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [metered_of_run _ _ _ _ _ _ _ hr]
    split <;> rfl

theorem fault_of_mapped (step : σ → Step σ α) (f : α → β) (fuel state)
    (h : (run step fuel state).map f = .fault) : run step fuel state = .fault := by
  cases hr : run step fuel state <;> simp_all [Trace.map]

end Contract.Evm.Guarded

namespace Contract.Evm.Stateful

/-- Check the state transition independently of its execution continuation.
This keeps symbolic jump conditions out of decoder reductions under `run`. -/
theorem step_jump (code : List UInt8) (input : Input) (env : Environment)
    (pc : Nat) (dest condition : Interaction.Word) (rest : List Interaction.Word)
    (memory : Interaction.Memory) (memoryWords : Nat) (storage : Slots)
    (warm : Interaction.Word → Bool) (refund : Int)
    (opcode : (code[pc]?.getD 0).toNat = 0x57) :
    step code input env ⟨⟨pc, dest :: condition :: rest, memory, memoryWords⟩, storage, warm, refund⟩ =
      if condition = 0#256 then
        .next 10 0 ⟨⟨pc + 1, rest, memory, memoryWords⟩, storage, warm, refund⟩
      else if dest.toNat ∈ jumpDestinations code then
        .next 10 0 ⟨⟨dest.toNat, rest, memory, memoryWords⟩, storage, warm, refund⟩
      else .fault := by
  by_cases zero : condition = 0#256 <;>
    by_cases valid : dest.toNat ∈ jumpDestinations code <;>
    simp [step, coreStep, Evm.step, opcode, zero, valid]

/-- Specialized equations keep the step function opaque until its state is
known. They are definitionally the generic engine, not another interpreter. -/
theorem run_zero (code input env state) : run code input env 0 state = .exhausted := rfl

theorem run_succ (code input env fuel state) :
    run code input env (fuel + 1) state = match step code input env state with
      | .next cost guard after => (run code input env fuel after).charge cost guard
      | .halt cost result => .finished cost cost result
      | .fault => .fault
      | .unsupported op => .unsupported op := by
  unfold run
  rw [Guarded.run]
  cases step code input env state <;> rfl

theorem projected_zero (code input env state) (f : Result → α) :
    (run code input env 0 state).map f = .exhausted := rfl

theorem projected_succ (code input env fuel state) (f : Result → α) :
    (run code input env (fuel + 1) state).map f = match step code input env state with
      | .next cost guard after => ((run code input env fuel after).map f).charge cost guard
      | .halt cost result => .finished cost cost (f result)
      | .fault => .fault
      | .unsupported op => .unsupported op := by
  rw [run_succ]
  cases step code input env state with
  | next cost guard after => exact Guarded.Trace.map_charge _ _ _ _
  | halt | fault | unsupported => rfl

structure Effects where
  halt : Halt
  storage : Slots
  warm : Interaction.Word → Bool
  refund : Int

def Result.effects (result : Result) : Effects :=
  ⟨result.halt, result.state.storage, result.state.warm, result.state.refund⟩

def Effects.result (effects : Effects) : Result :=
  ⟨effects.halt, { storage := effects.storage, warm := effects.warm, refund := effects.refund }⟩

theorem observe_projected (world transaction ctx input) (result : Guarded.Metered Result) :
    observe world transaction ctx input result =
      observe world transaction ctx input ((result.map Result.effects).map Effects.result) := by
  cases result with
  | finished remaining result => cases result with
    | mk halt state => cases halt <;> rfl
  | exceptional | unsupported | exhausted => rfl

theorem creation_projected (world prepared transaction ctx input) (result : Guarded.Metered Result) :
    finishCreation world prepared transaction ctx input result =
      finishCreation world prepared transaction ctx input ((result.map Result.effects).map Effects.result) := by
  cases result with
  | finished remaining result => cases result with
    | mk halt state => cases halt <;> rfl
  | exceptional | unsupported | exhausted => rfl

theorem write_same (storage : Slots) (key : Interaction.Word) : write storage key (storage key) = storage := by
  funext other
  simp only [write]
  split
  · rename_i h; rw [h]
  · rfl

end Contract.Evm.Stateful
