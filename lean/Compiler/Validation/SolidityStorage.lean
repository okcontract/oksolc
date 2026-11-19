/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityStorageSource
import Compiler.Validation.SolidityABI

namespace Compiler.Validation.SolidityStorage
open Contract.Evm SolidityFunction SolidityCall
open Contract.Interaction (Word wordBytes)

/-- A completed exact trace fixes all gas budgets, including the SSTORE sentry.
Unsupported instructions and fuel exhaustion remain explicit and cannot satisfy
`Conforms`; they are never interpreted as an accepted source result. -/
def meter : Guarded.Trace Stateful.Effects → Nat → Guarded.Metered Stateful.Effects
  | .finished used needed effects, gas =>
    if needed ≤ gas then .finished (gas - used) effects else .exceptional
  | .fault, _ => .exceptional
  | .unsupported opcode, _ => .unsupported opcode
  | .exhausted, _ => .exhausted

/-- Functional checking can discharge each instruction without expanding the
gas expression. The final certificate still meters the exact original trace. -/
theorem conforms_charge (expected : Outcome) (trace : Guarded.Trace Stateful.Effects)
    (cost guard : Nat) : Conforms expected (trace.charge cost guard) ↔ Conforms expected trace := by
  cases trace with
  | finished used needed effects =>
    cases effects with
    | mk halt cells warm refund =>
      cases expected <;> cases halt <;>
        simp [Conforms, Guarded.Trace.charge, Stateful.Effects.mk.injEq]
  | fault | unsupported | exhausted => cases expected <;> simp [Conforms, Guarded.Trace.charge]

theorem conforms_finished_returned (used needed : Nat) (effects : Stateful.Effects)
    (bytes : List UInt8) (cells : Stateful.Slots) :
    Conforms (.returned bytes cells) (.finished used needed effects) ↔
      effects.halt = .returned bytes ∧ effects.storage = cells := by
  cases effects with
  | mk halt storage warm refund =>
    cases halt <;> simp [Conforms, Stateful.Effects.mk.injEq]

theorem conforms_finished_reverted (used needed : Nat) (effects : Stateful.Effects)
    (bytes : List UInt8) :
    Conforms (.reverted bytes) (.finished used needed effects) ↔ effects.halt = .reverted bytes := by
  cases effects with
  | mk halt storage warm refund =>
    cases halt <;> simp [Conforms, Stateful.Effects.mk.injEq]

theorem conforms_fault : Conforms .fault .fault := rfl

theorem charge_add (trace : Guarded.Trace α) (first guardFirst second guardSecond : Nat) :
    (trace.charge second guardSecond).charge first guardFirst =
      trace.charge (first + second) (max guardFirst (first + guardSecond)) := by
  cases trace <;> simp only [Guarded.Trace.charge]
  case finished used needed result =>
    congr 1 <;> omega

theorem charge_finished (cost guard used needed : Nat) (effects : α) :
    (Guarded.Trace.finished used needed effects).charge cost guard =
      .finished (cost + used) (max guard (cost + needed)) effects := rfl

theorem metered_finished (code : List UInt8) (input : Input) (env : Stateful.Environment)
    (state : Stateful.State) (steps used needed : Nat) (effects : Stateful.Effects)
    (trace : (Stateful.run code input env steps state).map Stateful.Result.effects =
      .finished used needed effects) (fuel gas : Nat) (enough : steps ≤ fuel) :
    (Stateful.runMetered code input env fuel gas state).map Stateful.Result.effects =
      if needed ≤ gas then .finished (gas - used) effects else .exceptional := by
  have longer := Guarded.mapped_more (Stateful.step code input env) Stateful.Result.effects
    steps state used needed effects (fuel - steps) trace
  rw [show steps + (fuel - steps) = fuel by omega] at longer
  exact Guarded.mapped_metered _ _ _ _ _ _ _ _ longer

theorem metered (source : Outcome) (code : List UInt8) (input : Input) (env : Stateful.Environment)
    (state : Stateful.State) (steps : Nat)
    (checked : Conforms source ((Stateful.run code input env steps state).map Stateful.Result.effects))
    (fuel gas : Nat) (enough : steps ≤ fuel) :
    (Stateful.runMetered code input env fuel gas state).map Stateful.Result.effects =
      meter ((Stateful.run code input env steps state).map Stateful.Result.effects) gas := by
  cases source with
  | fault =>
    have fault := Guarded.fault_of_mapped (Stateful.step code input env) Stateful.Result.effects
      steps state checked
    have longer := Guarded.fault_more _ _ _ (fuel - steps) fault
    rw [show steps + (fuel - steps) = fuel by omega] at longer
    rw [checked, meter, show Stateful.runMetered code input env fuel gas state = .exceptional from
      Guarded.metered_of_fault _ _ _ _ longer]
    rfl
  | returned bytes cells =>
    obtain ⟨used, needed, warm, refund, trace⟩ := checked
    rw [trace, meter]
    exact metered_finished code input env state steps used needed _ trace fuel gas enough
  | reverted bytes =>
    obtain ⟨used, needed, cells, warm, refund, trace⟩ := checked
    rw [trace, meter]
    exact metered_finished code input env state steps used needed _ trace fuel gas enough

def TracePreserves (source : ContractSource) (code : List UInt8) (steps : Nat) : Prop :=
  ∀ input, Sized input → ∀ (state : Stateful.State) (env : Stateful.Environment),
    Conforms (outcome source input state.storage env.isStatic)
      ((Stateful.run code input env steps { state with machine := {} }).map Stateful.Result.effects)

theorem dispatch (source : ContractSource) (code : List UInt8) (steps : Nat)
    (empty : ∀ input, Sized input → input.calldata.length = 0 →
      ∀ (state : Stateful.State) (env : Stateful.Environment),
      Conforms (emptyOutcome source input state.storage env.isStatic)
        ((Stateful.run code input env steps { state with machine := {} }).map Stateful.Result.effects))
    (short : ∀ input, Sized input → 0 < input.calldata.length → input.calldata.length < 4 → ∀ (state : Stateful.State) (env : Stateful.Environment),
      Conforms (.reverted []) ((Stateful.run code input env steps
        { state with machine := {} }).map Stateful.Result.effects))
    (unknown : ∀ input, Sized input → 4 ≤ input.calldata.length →
      (∀ function ∈ source.functions,
        loadWord input.calldata 0 >>> 224 ≠ BitVec.ofNat 256 function.call.selector) → ∀ (state : Stateful.State) (env : Stateful.Environment),
      Conforms (.reverted []) ((Stateful.run code input env steps
        { state with machine := {} }).map Stateful.Result.effects))
    (selected : ∀ function ∈ source.functions, ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 function.call.selector → ∀ (state : Stateful.State) (env : Stateful.Environment),
      Conforms (function.outcome source.variables input state.storage env.isStatic)
        ((Stateful.run code input env steps { state with machine := {} }).map Stateful.Result.effects)) :
    TracePreserves source code steps := by
  intro input sized state env
  by_cases noData : input.calldata.length = 0
  · simpa only [outcome, if_pos noData] using empty input sized noData state env
  have nonempty : 0 < input.calldata.length := Nat.pos_of_ne_zero noData
  by_cases header : input.calldata.length < 4
  · simpa only [outcome, if_neg noData, if_pos header] using short input sized nonempty header state env
  · cases found : select source input with
    | none =>
      have absent := List.find?_eq_none.mp found
      have rejected : ∀ function ∈ source.functions,
          loadWord input.calldata 0 >>> 224 ≠ BitVec.ofNat 256 function.call.selector := by
        simpa only [decide_eq_true_eq] using absent
      simpa only [outcome, if_neg noData, if_neg header, found] using
        unknown input sized (Nat.le_of_not_gt header) rejected state env
    | some function =>
      have member := List.mem_of_find?_eq_some found
      have chosen := List.find?_some found
      have chosen : loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 function.call.selector := by
        simpa only [decide_eq_true_eq] using chosen
      simpa only [outcome, if_neg noData, if_neg header, found] using
        selected function member input sized (Nat.le_of_not_gt header) chosen state env

theorem selected (variables : Layout) (function : Function) (code : List UInt8) (steps : Nat)
    (paid : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 function.call.selector →
      ¬function.call.AcceptsValue input → ∀ (state : Stateful.State) (env : Stateful.Environment),
      Conforms (.reverted [])
        ((Stateful.run code input env steps { state with machine := {} }).map Stateful.Result.effects))
    (truncated : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 function.call.selector →
      function.call.AcceptsValue input → input.calldata.length < 4 + 32 * function.call.parameters.length →
      ∀ (state : Stateful.State) (env : Stateful.Environment), Conforms (.reverted [])
        ((Stateful.run code input env steps { state with machine := {} }).map Stateful.Result.effects))
    (malformed : ∀ input, Sized input → function.call.AcceptsValue input →
      4 + 32 * function.call.parameters.length ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 function.call.selector →
      ¬function.call.Arguments input → ∀ (state : Stateful.State) (env : Stateful.Environment),
      Conforms (.reverted [])
        ((Stateful.run code input env steps { state with machine := {} }).map Stateful.Result.effects))
    (returned : ∀ input, Sized input → function.call.Accepts input →
      ∀ (state : Stateful.State) (env : Stateful.Environment),
      Conforms (function.result variables input state.storage env.isStatic)
        ((Stateful.run code input env steps { state with machine := {} }).map Stateful.Result.effects))
    (input : Input) (sized : Sized input) (header : 4 ≤ input.calldata.length)
    (chosen : loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 function.call.selector)
    (state : Stateful.State) (env : Stateful.Environment) :
    Conforms (function.outcome variables input state.storage env.isStatic)
      ((Stateful.run code input env steps { state with machine := {} }).map Stateful.Result.effects) :=
  SolidityABI.Source.selected function.call input chosen
    (function.result variables input state.storage env.isStatic) (.reverted [])
    (fun result => Conforms result
      ((Stateful.run code input env steps { state with machine := {} }).map Stateful.Result.effects))
    (fun value => paid input sized header chosen value state env)
    (fun value short => truncated input sized header chosen value short state env)
    (fun value full arguments => malformed input sized value full chosen arguments state env)
    (fun accepted => returned input sized accepted state env)

/-- The exact trace determines the entire target frame, including warming and
refund data carried into subsequent calls. The same trace must conform to the
source evaluator. Quantification includes arbitrary original/current storage,
warmth, refund counters, static mode and every gas budget. -/
def CallPreserves (source : ContractSource) (runtime : List UInt8) (steps : Nat)
    (world : World) (transaction : Stateful.Transaction) (ctx : Contract.Context)
    (input : Input) (isStatic : Bool) : Prop :=
  ∃ trace, Conforms (outcome source input (world.storage ctx.self) isStatic) trace ∧
    (Stateful.run runtime input ⟨transaction.original ctx.self, isStatic⟩ steps
      (Stateful.initial world transaction ctx.self)).map Stateful.Result.effects = trace ∧
    ∀ fuel gas, steps ≤ fuel →
      Stateful.executeCall world transaction ctx input isStatic fuel gas =
        Stateful.observe world transaction ctx input ((meter trace gas).map Stateful.Effects.result)

structure CallsPreserves (source : ContractSource) (runtime : List UInt8) (steps : Nat) : Prop where
  nonempty : source.functions ≠ [] ∨ source.receive.isSome = true
  variables : source.variables.names.Nodup
  arity : ∀ function ∈ source.functions, function.parameterTypes.length = function.abi.parameters.length
  selectors : (source.functions.map fun function => BitVec.ofNat 256 function.call.selector).Nodup
  inhabited : ∀ function ∈ source.functions, ∃ input, Sized input ∧ function.call.ValidCall input
  trace : TracePreserves source runtime steps
  preserve : ∀ world transaction ctx input isStatic, Sized input → world.code ctx.self = runtime →
    CallPreserves source runtime steps world transaction ctx input isStatic

theorem certifyCalls (source : ContractSource) (runtime : List UInt8) (steps : Nat)
    (nonempty : source.functions ≠ [] ∨ source.receive.isSome = true)
    (variables : source.variables.names.Nodup)
    (arity : ∀ function ∈ source.functions, function.parameterTypes.length = function.abi.parameters.length)
    (unique : (source.functions.map fun function => BitVec.ofNat 256 function.call.selector).Nodup)
    (inhabited : ∀ function ∈ source.functions, ∃ input, Sized input ∧ function.call.ValidCall input)
    (trace : TracePreserves source runtime steps) : CallsPreserves source runtime steps := by
  refine ⟨nonempty, variables, arity, unique, inhabited, trace, ?_⟩
  intro world transaction ctx input isStatic sized installed
  let state := Stateful.initial world transaction ctx.self
  let env : Stateful.Environment := ⟨transaction.original ctx.self, isStatic⟩
  have checked := trace input sized state env
  change Conforms (outcome source input (world.storage ctx.self) isStatic)
    ((Stateful.run runtime input env steps state).map Stateful.Result.effects) at checked
  refine ⟨_, checked, rfl, ?_⟩
  intro fuel gas enough
  unfold Stateful.executeCall
  rw [installed, Stateful.observe_projected]
  rw [metered _ runtime input env state steps checked fuel gas enough]

end Compiler.Validation.SolidityStorage
