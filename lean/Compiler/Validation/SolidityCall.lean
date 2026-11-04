/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityFunction

/-! Complete external-call observations for the admitted single-function source
fragment. Trailing calldata is allowed. Short calldata, unknown selectors and
value rejected by the selected method revert. Admitted calls return the source
word or its checked arithmetic panic. The explicit length bound is part of this
certificate's scope, not an EVM consensus limit. Parsing and source admission remain trusted.
Deployment, transaction admission and transaction fees remain outside the frame. -/
namespace Compiler.Validation.SolidityCall
open Contract.Yul Contract.Evm SolidityFunction

def Sized (input : Input) : Prop := input.calldata.length < 2 ^ 64

theorem length_word (size : Nat) (bounded : size < 2 ^ 64) :
    (BitVec.ofNat 256 size).toNat = size := by
  simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show size < 2 ^ 256 by omega)]

/-- Subtraction-based dispatch/decoder tests compare words for equality. -/
theorem word_sub_eq_zero (left right : BitVec 256) :
    left - right = 0#256 ↔ left = right := by
  simpa only [BitVec.zero_add] using (BitVec.sub_eq_iff_eq_add (x := left) (y := right) (z := 0#256))

/-- The viaIR ABI guard uses signed subtraction after checking the selector's
four-byte prefix. Its word arithmetic agrees with the source length test. -/
theorem length_sub_four (size : Nat) (bounded : size < 2 ^ 64) (header : 4 ≤ size) :
    (~~~(3#256) + BitVec.ofNat 256 size).toInt = (size - 4 : Nat) := by
  rw [BitVec.add_comm, show ~~~(3#256) = -(4#256) by decide, ← BitVec.sub_eq_add_neg]
  rw [BitVec.ofNat_sub_ofNat_of_le size 4 (by decide) header]
  rw [BitVec.toInt_eq_toNat_of_lt]
  · rw [length_word (size - 4) (by omega)]
  · rw [length_word (size - 4) (by omega)]; omega

/-- Keep symbolic execution's accumulated cost as one wrapper. Expanding the
wrapper before the next instruction is known creates large nested matches. -/
theorem charge_add (result : Execution) (first second : Nat) :
    (result.charge second).charge first = result.charge (first + second) := by
  cases result <;> simp [Execution.charge, Nat.add_assoc]

theorem charge_finished (first rest : Nat) (result : Halt) :
    (Execution.finished rest result).charge first = .finished (first + rest) result := rfl

/-- Payability is per selected method; body effects remain in the admitted
expression fragment. Message funding/admission precedes the call frame. -/
def AcceptsValue (source : Source) (input : Input) : Prop :=
  if source.payable then True else input.value = 0

instance (source : Source) (input : Input) : Decidable (AcceptsValue source input) := by
  unfold AcceptsValue
  split <;> infer_instance

theorem acceptsValue_zero (source : Source) (input : Input) (zero : input.value = 0) :
    AcceptsValue source input := by simp [AcceptsValue, zero]

/-- Selector and argument admission are shared by payable expression methods
and the separate nonpayable storage route. -/
def AcceptsArguments (source : Source) (input : Input) : Prop :=
  4 + 32 * source.parameters.length ≤ input.calldata.length ∧
    loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector

instance (source : Source) (input : Input) : Decidable (AcceptsArguments source input) :=
  inferInstanceAs (Decidable (_ ∧ _))

def Accepts (source : Source) (input : Input) : Prop :=
  AcceptsValue source input ∧ AcceptsArguments source input

instance (source : Source) (input : Input) : Decidable (Accepts source input) :=
  inferInstanceAs (Decidable (_ ∧ _))

def outcome (source : Source) (input : Input) : Halt :=
  if Accepts source input then source.result input else .reverted []

theorem outcome_accepts (source : Source) (input : Input) (accepted : Accepts source input) :
    outcome source input = source.result input := if_pos accepted

theorem outcome_rejects (source : Source) (input : Input) (rejected : ¬Accepts source input) :
    outcome source input = .reverted [] := if_neg rejected

def observation (source : Source) (input : Input) (world : World) (ctx : Contract.Context) (cost gas : Nat) : Observation :=
  if cost ≤ gas then
    match outcome source input with
    | .returned bytes => ⟨.returned, bytes, world.transfer ctx.caller ctx.self input.value, gas - cost⟩
    | .reverted bytes => ⟨.reverted, bytes, world, gas - cost⟩
  else ⟨.exceptional, [], world, 0⟩

theorem metered (source : Source) (code : List UInt8) (input : Input) (steps cost : Nat)
    (trace : Contract.Evm.run code input steps {} = .finished cost (outcome source input))
    (fuel gas : Nat) (enough : steps ≤ fuel) :
    runMetered code input fuel gas {} =
      if cost ≤ gas then .finished (gas - cost) (outcome source input) else .exceptional := by
  have longer := run_more code input steps {} cost (outcome source input) (fuel - steps) trace
  rw [show steps + (fuel - steps) = fuel by omega] at longer
  exact metered_of_run code input fuel {} cost (outcome source input) gas longer

theorem frame (source : Source) (code : List UInt8) (input : Input) (steps cost : Nat)
    (trace : Contract.Evm.run code input steps {} = .finished cost (outcome source input))
    (world : World) (ctx : Contract.Context) (fuel gas : Nat)
    (installed : world.code ctx.self = code) (enough : steps ≤ fuel) :
    executeCall world ctx input fuel gas = observation source input world ctx cost gas := by
  simp only [executeCall, installed, metered source code input steps cost trace fuel gas enough]
  by_cases funded : cost ≤ gas
  · cases result : outcome source input <;> simp [observation, funded, result, observeCall]
  · simp [observation, funded, observeCall]

/-- Every calldata/value in the stated size domain, including rejected calls,
has a checked exact-byte trace. Gas exhaustion remains exceptional; reversion
retains unused gas and rolls back incoming value. No input enumeration occurs. -/
def Preserves (source : Source) (code : List UInt8) (steps : Nat) : Prop :=
  (∃ input, Sized input ∧ source.ValidCall input) ∧
  ∀ input, Sized input → ∃ cost,
    Contract.Evm.run code input steps {} = .finished cost (outcome source input) ∧
    (∀ fuel gas, steps ≤ fuel → runMetered code input fuel gas {} =
      if cost ≤ gas then .finished (gas - cost) (outcome source input) else .exceptional) ∧
    (∀ world ctx fuel gas, world.code ctx.self = code → steps ≤ fuel →
      executeCall world ctx input fuel gas = observation source input world ctx cost gas)

theorem certify (source : Source) (code : List UInt8) (steps : Nat)
    (inhabited : ∃ input, Sized input ∧ source.ValidCall input)
    (trace : ∀ input, Sized input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (outcome source input)) :
    Preserves source code steps := by
  refine ⟨inhabited, fun input sized => ?_⟩
  obtain ⟨cost, checked⟩ := trace input sized
  exact ⟨cost, checked, metered source code input steps cost checked,
    fun world ctx fuel gas installed enough => frame source code input steps cost checked world ctx fuel gas installed enough⟩

/-- Compose independently checked dispatch paths. Each premise executes the
same complete runtime, with a partition of the input domain rather than a
selected internal entry point. -/
theorem dispatch (source : Source) (code : List UInt8) (steps : Nat)
    (short : ∀ input, Sized input → input.calldata.length < 4 → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (unknown : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 ≠ BitVec.ofNat 256 source.selector → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (paid : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → ¬AcceptsValue source input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (truncated : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → AcceptsValue source input →
      input.calldata.length < 4 + 32 * source.parameters.length → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (returned : ∀ input, Sized input → Accepts source input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (source.result input)) :
    ∀ input, Sized input → ∃ cost, Contract.Evm.run code input steps {} = .finished cost (outcome source input) := by
  intro input sized
  by_cases header : input.calldata.length < 4
  · obtain ⟨cost, ran⟩ := short input sized header
    have rejected : ¬Accepts source input := fun accepted => by have := accepted.2.1; omega
    exact ⟨cost, by rw [outcome_rejects source input rejected]; exact ran⟩
  · have header := Nat.le_of_not_gt header
    by_cases selected : loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector
    · by_cases value : AcceptsValue source input
      · by_cases full : 4 + 32 * source.parameters.length ≤ input.calldata.length
        · obtain ⟨cost, ran⟩ := returned input sized ⟨value, full, selected⟩
          exact ⟨cost, by rw [outcome_accepts source input ⟨value, full, selected⟩]; exact ran⟩
        · obtain ⟨cost, ran⟩ := truncated input sized header selected value (Nat.lt_of_not_ge full)
          exact ⟨cost, by rw [outcome_rejects source input (fun accepted => full accepted.2.1)]; exact ran⟩
      · obtain ⟨cost, ran⟩ := paid input sized header selected value
        exact ⟨cost, by rw [outcome_rejects source input (fun accepted => value accepted.1)]; exact ran⟩
    · obtain ⟨cost, ran⟩ := unknown input sized header selected
      exact ⟨cost, by rw [outcome_rejects source input (fun accepted => selected accepted.2.2)]; exact ran⟩

/-- Existing canonical-call certificates follow from the stronger statement.
The arity premise matches the closed source parser's existing eight-word bound. -/
theorem canonical (source : Source) (code : List UInt8) (steps : Nat)
    (arity : source.parameters.length ≤ 8) (unchecked : source.checked = false)
    (checked : Preserves source code steps) :
    SolidityFunction.Preserves source code steps := by
  apply SolidityFunction.certify source code steps unchecked
  · obtain ⟨input, _, valid⟩ := checked.1; exact ⟨input, valid⟩
  · intro input valid
    have sized : Sized input := by unfold Sized; rw [valid.2.1]; omega
    obtain ⟨cost, ran, _⟩ := checked.2 input sized
    have accepted : Accepts source input := ⟨acceptsValue_zero source input valid.1, Nat.le_of_eq valid.2.1.symm, valid.2.2⟩
    exact ⟨cost, by simpa [outcome, accepted, Source.result, unchecked] using ran⟩

end Compiler.Validation.SolidityCall
