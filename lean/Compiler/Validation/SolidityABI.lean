/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityCall

/-! Shared static ABI admission for bounded source-to-bytecode certificates.
Argument types determine selectors and canonical encodings independently of
compiler output. This module admits calls; it does not model function bodies,
dynamic ABI values, transaction admission or the Solidity parser. -/
namespace Compiler.Validation.SolidityABI
open Contract.Evm

inductive Parameter where
  | word | bytes4 | boolean
  deriving DecidableEq, Repr

def Parameter.name : Parameter → String
  | .word => "uint256" | .bytes4 => "bytes4" | .boolean => "bool"

/-- Fixed bytes are left-aligned; Boolean words must be exactly zero or one. -/
def Parameter.Accepts : Parameter → BitVec 256 → Prop
  | .word, _ => True
  | .boolean, value => value = 0 ∨ value = 1
  | .bytes4, value => value &&& (BitVec.ofNat 256 (2 ^ 256 - 2 ^ 224)) = value

instance (parameter : Parameter) (value : BitVec 256) : Decidable (parameter.Accepts value) := by
  cases parameter <;> unfold Parameter.Accepts <;> infer_instance

/-- Native Boolean decoders compare the argument with its zero/one cleanup.
Accepting arbitrary nonzero values would silently widen the Solidity ABI. -/
theorem boolean_accepts_iff_cleanup (value : BitVec 256) :
    Parameter.boolean.Accepts value ↔ (if value = 0 then 0 else 1) = value := by
  by_cases zero : value = 0
  · simp [Parameter.Accepts, zero]
  · simp only [Parameter.Accepts, zero, ↓reduceIte, false_or]
    exact eq_comm

/-- Two native ISZERO operations produce the Boolean zero/one cleanup. -/
theorem boolean_double_iszero (value : BitVec 256) :
    (if (if value = 0 then 1#256 else 0#256) = 0 then 1#256 else 0#256) =
      (if value = 0 then 0#256 else 1#256) := by
  by_cases zero : value = 0 <;> simp [zero]

/-- Native ABI helpers may subtract the masked word in either order. Keep
the zero test oriented toward the same padding predicate without rewriting
unrelated execution equalities. -/
theorem sub_mask_zero (value mask : BitVec 256) :
    value - (mask &&& value) = 0#256 ↔ mask &&& value = value := by
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add, eq_comm]

theorem zero_sub_mask (value mask : BitVec 256) :
    0#256 = value - (mask &&& value) ↔ mask &&& value = value := by
  rw [eq_comm, sub_mask_zero]

theorem mask_sub_zero (value mask : BitVec 256) :
    (mask &&& value) - value = 0#256 ↔ mask &&& value = value := by
  rw [BitVec.sub_eq_iff_eq_add, BitVec.zero_add]

theorem zero_mask_sub (value mask : BitVec 256) :
    0#256 = (mask &&& value) - value ↔ mask &&& value = value := by
  rw [eq_comm, mask_sub_zero]

structure Source where
  name : String
  parameters : List Parameter
  payable : Bool := false

def Source.signature (source : Source) : String :=
  source.name ++ "(" ++ String.intercalate "," (source.parameters.map Parameter.name) ++ ")"

def Source.selector (source : Source) : Nat := Contract.Export.Keccak.selector source.signature

def Source.Arguments (source : Source) (input : Input) : Prop :=
  ∀ parameter ∈ source.parameters.zipIdx,
    parameter.1.Accepts (loadWord input.calldata (4 + 32 * parameter.2))

instance (source : Source) (input : Input) : Decidable (source.Arguments input) :=
  inferInstanceAs (Decidable (∀ parameter ∈ source.parameters.zipIdx, _))

def Source.AcceptsValue (source : Source) (input : Input) : Prop :=
  if source.payable then True else input.value = 0

instance (source : Source) (input : Input) : Decidable (source.AcceptsValue input) := by
  unfold Source.AcceptsValue; split <;> infer_instance

def Source.Accepts (source : Source) (input : Input) : Prop :=
  source.AcceptsValue input ∧ 4 + 32 * source.parameters.length ≤ input.calldata.length ∧
    loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector ∧ source.Arguments input

instance (source : Source) (input : Input) : Decidable (source.Accepts input) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def Source.ValidCall (source : Source) (input : Input) : Prop :=
  input.value = 0 ∧ input.calldata.length = 4 + 32 * source.parameters.length ∧
    loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector ∧ source.Arguments input

instance (source : Source) (input : Input) : Decidable (source.ValidCall input) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- One argument-admission partition, independent of a body evaluator and of
whether the target trace is pure or stateful. Each rejection remains an explicit
consumer obligation, including malformed complete argument words. -/
theorem Source.selected {α : Type} (source : Source) (input : Input)
    (matched : loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector)
    (success failure : α) (P : α → Prop)
    (paid : ¬source.AcceptsValue input → P failure)
    (truncated : source.AcceptsValue input →
      input.calldata.length < 4 + 32 * source.parameters.length → P failure)
    (malformed : source.AcceptsValue input →
      4 + 32 * source.parameters.length ≤ input.calldata.length →
      ¬source.Arguments input → P failure)
    (returned : source.Accepts input → P success) :
    P (if source.Accepts input then success else failure) := by
  by_cases value : source.AcceptsValue input
  · by_cases full : 4 + 32 * source.parameters.length ≤ input.calldata.length
    · by_cases arguments : source.Arguments input
      · rw [if_pos (show source.Accepts input from ⟨value, full, matched, arguments⟩)]
        exact returned ⟨value, full, matched, arguments⟩
      · rw [if_neg (fun accepted : source.Accepts input => arguments accepted.2.2.2)]
        exact malformed value full arguments
    · rw [if_neg (fun accepted : source.Accepts input => full accepted.2.1)]
      exact truncated value (Nat.lt_of_not_ge full)
  · rw [if_neg (fun accepted : source.Accepts input => value accepted.1)]
    exact paid value

/-- Bridge the existing expression ABI without changing its word-only scope. -/
def Source.ofFunction (source : SolidityFunction.Source) : Source :=
  { name := source.name, parameters := source.parameters.map (fun _ => .word),
    payable := source.payable }

@[simp] theorem Source.ofFunction_selector (source : SolidityFunction.Source) :
    (Source.ofFunction source).selector = source.selector := by
  simp [ofFunction, Source.selector, Source.signature, SolidityFunction.Source.selector,
    SolidityFunction.Source.signature, Parameter.name, List.map_map, Function.comp_def]

@[simp] theorem Source.ofFunction_arguments (source : SolidityFunction.Source) (input : Input) :
    (Source.ofFunction source).Arguments input := by
  intro parameter member
  have typed := List.fst_mem_of_mem_zipIdx member
  simp only [ofFunction, List.mem_map] at typed
  obtain ⟨_, _, same⟩ := typed
  rw [← same]
  trivial

@[simp] theorem Source.ofFunction_accepts (source : SolidityFunction.Source) (input : Input) :
    (Source.ofFunction source).Accepts input ↔ SolidityCall.Accepts source input := by
  simp only [Source.Accepts, ofFunction_arguments, and_true, ofFunction_selector]
  simp only [ofFunction, List.length_map, Source.AcceptsValue,
    SolidityCall.Accepts, SolidityCall.AcceptsValue, SolidityCall.AcceptsArguments]
  rfl

end Compiler.Validation.SolidityABI
