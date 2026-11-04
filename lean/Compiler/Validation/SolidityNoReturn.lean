/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityABI

/-! Empty function bodies with no return values. The closed source grammar
admits unused uint256/bytes4 parameters and explicit pure/view/payable methods.
This does not admit state reads, arbitrary statements or dynamic ABI values. -/
namespace Compiler.Validation.SolidityNoReturn
open Contract.Evm SolidityFunction SolidityCall

-- Preserve the existing emitted-proof interface while sharing its semantics.
export SolidityABI (Parameter Source sub_mask_zero zero_sub_mask mask_sub_zero zero_mask_sub)
namespace Parameter
export SolidityABI.Parameter (name Accepts)
end Parameter
namespace Source
export SolidityABI.Source (signature selector Arguments AcceptsValue Accepts ValidCall)
end Source

def outcome (source : Source) (input : Input) : Halt :=
  if source.Accepts input then .returned [] else .reverted []

/-- Common typed-call guards for a terminal body returning exact bytes. The
artifact trace must derive those bytes; this is not a callback assumption. -/
def returning (source : Source) (bytes : List UInt8) (input : Input) : Halt :=
  if source.Accepts input then .returned bytes else .reverted []

theorem selected_returning (source : Source) (bytes : List UInt8) (code : List UInt8) (steps : Nat)
    (paid : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → ¬source.AcceptsValue input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (truncated : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → source.AcceptsValue input →
      input.calldata.length < 4 + 32 * source.parameters.length → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (malformed : ∀ input, Sized input → source.AcceptsValue input →
      4 + 32 * source.parameters.length ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → ¬source.Arguments input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (returned : ∀ input, Sized input → source.Accepts input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.returned bytes))
    (input : Input) (sized : Sized input) (header : 4 ≤ input.calldata.length)
    (matched : loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector) :
    ∃ cost, Contract.Evm.run code input steps {} = .finished cost (returning source bytes input) := by
  exact SolidityABI.Source.selected source input matched (.returned bytes) (.reverted [])
    (fun result => ∃ cost, Contract.Evm.run code input steps {} = .finished cost result)
    (paid input sized header matched) (truncated input sized header matched)
    (fun value full arguments => malformed input sized value full matched arguments)
    (returned input sized)

theorem selected (source : Source) (code : List UInt8) (steps : Nat)
    (paid : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → ¬source.AcceptsValue input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (truncated : ∀ input, Sized input → 4 ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → source.AcceptsValue input →
      input.calldata.length < 4 + 32 * source.parameters.length → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (malformed : ∀ input, Sized input → source.AcceptsValue input →
      4 + 32 * source.parameters.length ≤ input.calldata.length →
      loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector → ¬source.Arguments input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.reverted []))
    (returned : ∀ input, Sized input → source.Accepts input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.returned []))
    (input : Input) (sized : Sized input) (header : 4 ≤ input.calldata.length)
    (matched : loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector) :
    ∃ cost, Contract.Evm.run code input steps {} = .finished cost (outcome source input) := by
  simpa only [returning, outcome] using
    selected_returning source [] code steps paid truncated malformed returned input sized header matched

end Compiler.Validation.SolidityNoReturn
