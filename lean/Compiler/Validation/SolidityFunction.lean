/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Validation.SolidityChecked
import Contract.Evm.Execution
import Contract.Evm.Frames
import Contract.Interaction.MemoryProofs
import Contract.Export.Keccak

/-! Single pure external uint256 functions, with explicitly typed operands in
a checked or unchecked return expression. The source ABI decodes word arguments directly
from byte calldata. Ordinary compiler artifacts are proved by symbolic execution
in the shared raw-byte EVM, including memory expansion and exact gas accounting.
The legacy word-only preservation predicate below is explicitly unchecked;
SolidityCall and SolidityDeployment cover checked outcomes, invalid calls and
deployment. Parsing and Solidity fragment admission remain trusted. -/
namespace Compiler.Validation.SolidityFunction
open Contract.Yul Contract.Evm
open Contract.Interaction (wordBytes)

structure Source where
  name : String
  parameters : List String
  body : SolidityWord.Expr
  checked : Bool := false
  payable : Bool := false

def Source.signature (source : Source) : String :=
  source.name ++ "(" ++ String.intercalate "," (source.parameters.map (fun _ => "uint256")) ++ ")"

def Source.selector (source : Source) : Nat := Contract.Export.Keccak.selector source.signature

def Source.locals (source : Source) (input : Input) (name : String) : Word :=
  match source.parameters.idxOf? name with
  | some index => loadWord input.calldata (4 + 32 * index)
  | none => 0

def Source.returnBytes (source : Source) (input : Input) : List UInt8 :=
  wordBytes (source.body.eval (source.locals input))

/-- ABI body outcome; checked arithmetic may revert after successful argument
decoding. The canonical word-only interface below retains its unchecked scope. -/
def Source.result (source : Source) (input : Input) : Halt :=
  if source.checked then
    match source.body.evalChecked (source.locals input) with
    | .ok value => .returned (wordBytes value)
    | .error bytes => .reverted bytes
  else .returned (source.returnBytes input)

def Source.ValidCall (source : Source) (input : Input) : Prop :=
  input.value = 0 ∧ input.calldata.length = 4 + 32 * source.parameters.length ∧
    loadWord input.calldata 0 >>> 224 = BitVec.ofNat 256 source.selector

instance (source : Source) (input : Input) : Decidable (source.ValidCall input) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem return_word (memory : Contract.Interaction.Memory) (offset : Nat) (value : Word) :
    (memory.write offset (wordBytes value)).read offset 32 = wordBytes value := by
  simpa only [Contract.Interaction.wordBytes_length] using
    Contract.Interaction.Memory.read_write memory offset (wordBytes value)

theorem shl_word (a b : Word) : SolidityWord.Binary.shl.eval a b = a <<< b.toNat := by
  change (if b.toNat < 256 then a <<< b.toNat else 0) = a <<< b.toNat
  split
  · rfl
  · rw [BitVec.shiftLeft_eq_zero (by omega)]
    rfl

theorem shr_word (a b : Word) : SolidityWord.Binary.shr.eval a b = a >>> b.toNat := by
  change (if b.toNat < 256 then a >>> b.toNat else 0) = a >>> b.toNat
  split
  · rfl
  · rw [BitVec.ushiftRight_eq_zero (by omega)]
    rfl

/-- A checked completed byte execution gives the exact outcome for every gas
budget and all larger step bounds. A too-small gas budget exceptionally halts;
it cannot be turned into an accepted source return. -/
theorem metered_runtime (source : Source) (code : List UInt8) (input : Input)
    (steps cost : Nat)
    (trace : Contract.Evm.run code input steps {} = .finished cost (.returned (source.returnBytes input)))
    (fuel gas : Nat) (enoughSteps : steps ≤ fuel) :
    runMetered code input fuel gas {} =
      if cost ≤ gas then .finished (gas - cost) (.returned (source.returnBytes input)) else .exceptional := by
  have longer := run_more code input steps {} cost (.returned (source.returnBytes input)) (fuel - steps) trace
  rw [show steps + (fuel - steps) = fuel by omega] at longer
  exact metered_of_run code input fuel {} cost (.returned (source.returnBytes input)) gas longer

/-- The read-only instruction semantics transports the persistent world. The
code premise binds execution to the bytes installed at this account. -/
theorem runtime_frame (source : Source) (code : List UInt8) (input : Input)
    (world : World) (ctx : Contract.Context) (steps cost fuel gas : Nat)
    (valid : source.ValidCall input) (installed : world.code ctx.self = code)
    (trace : Contract.Evm.run code input steps {} = .finished cost (.returned (source.returnBytes input)))
    (enoughSteps : steps ≤ fuel) (enoughGas : cost ≤ gas) :
    executeCall world ctx input fuel gas =
      ⟨.returned, source.returnBytes input, world, gas - cost⟩ := by
  simp only [executeCall, installed, metered_runtime source code input steps cost trace fuel gas enoughSteps,
    if_pos enoughGas, observeCall]
  simp [World.transfer, show input.value = 0#256 from valid.1]

/-- Unchecked artifact acceptance includes a nonempty calling domain, execution of the
exact bytes, every gas budget, and preservation of the installed account world.
The execution fuel is a proved upper bound, not a bounded input enumeration. -/
def Preserves (source : Source) (code : List UInt8) (steps : Nat) : Prop :=
  source.checked = false ∧
  (∃ input, source.ValidCall input) ∧
  ∀ input, source.ValidCall input → ∃ cost,
    Contract.Evm.run code input steps {} = .finished cost (.returned (source.returnBytes input)) ∧
    (∀ fuel gas, steps ≤ fuel → runMetered code input fuel gas {} =
      if cost ≤ gas then .finished (gas - cost) (.returned (source.returnBytes input)) else .exceptional) ∧
    (∀ world ctx fuel gas, world.code ctx.self = code → steps ≤ fuel → cost ≤ gas →
      executeCall world ctx input fuel gas = ⟨.returned, source.returnBytes input, world, gas - cost⟩)

theorem certify (source : Source) (code : List UInt8) (steps : Nat)
    (unchecked : source.checked = false)
    (inhabited : ∃ input, source.ValidCall input)
    (trace : ∀ input, source.ValidCall input → ∃ cost,
      Contract.Evm.run code input steps {} = .finished cost (.returned (source.returnBytes input))) :
    Preserves source code steps := by
  refine ⟨unchecked, inhabited, fun input valid => ?_⟩
  obtain ⟨cost, checked⟩ := trace input valid
  exact ⟨cost, checked, metered_runtime source code input steps cost checked,
    fun world ctx fuel gas installed enoughSteps enoughGas =>
      runtime_frame source code input world ctx steps cost fuel gas valid installed checked enoughSteps enoughGas⟩

end Compiler.Validation.SolidityFunction
