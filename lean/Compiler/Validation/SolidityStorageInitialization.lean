/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityStorageCreation

/-! Source-declaration initializers run in order from zero storage. Arithmetic
is checked and reads observe previous writes, including default-zero forward
references. The exact target trace owns gas, access warming and refunds; the
source fixes the complete store or panic bytes. Creation admission is unchanged. -/
namespace Compiler.Validation.SolidityStorage.Initialization
open Contract.Evm
open Contract.Interaction (Word)

abbrev Initializer := Nat × SolidityWord.Expr

def evaluate (variables : Layout) : List Initializer → Stateful.Slots → Except (List UInt8) Stateful.Slots
  | [], cells => .ok cells
  | (slot, expr) :: rest, cells => do
    let value ← expr.evalChecked (locals variables
      { name := "constructor", parameters := [], body := .literal 0, checked := true } {} cells)
    match variables.write slot value cells with
    | none => .error []
    | some after => evaluate variables rest after

def result (variables : Layout) (initializers : List Initializer) (input : Input) :
    Except (List UInt8) Stateful.Slots :=
  if input.value = 0#256 then evaluate variables initializers (fun _ => 0) else .error []

def sourceOutcome : Except (List UInt8) Stateful.Slots → Outcome
  | .ok cells => .returned [] cells
  | .error bytes => .reverted bytes

def source (variables : Layout) (initializers : List Initializer) (input : Input) : Outcome :=
  sourceOutcome (result variables initializers input)

abbrev expected (runtime : List UInt8) (outcome : Except (List UInt8) Stateful.Slots) :=
  Creation.expected runtime (sourceOutcome outcome)

abbrev TracePreserves (variables : Layout) (initializers : List Initializer) :=
  Creation.TracePreserves (source variables initializers)

abbrev observation := Creation.observation

abbrev FramePreserves (variables : Layout) (initializers : List Initializer) :=
  Creation.FramePreserves (source variables initializers)

abbrev Preserves (contract : ContractSource) (initializers : List Initializer) :=
  Creation.Preserves contract (source contract.variables initializers)

/-- Compatibility endpoint for contracts with declaration initializers and an
implicit empty nonpayable constructor. The full frame proof is shared. -/
theorem certify (contract : ContractSource) (initializers : List Initializer)
    (creation runtime : List UInt8) (creationSteps runtimeSteps : Nat)
    (calls : CallsPreserves contract runtime runtimeSteps)
    (initSize : creation.length ≤ 49152) (runtimeSize : runtime.length ≤ 24576)
    (runtimePrefix : runtime.head? ≠ some 0xef)
    (trace : TracePreserves contract.variables initializers creation runtime creationSteps) :
    Preserves contract initializers creation runtime creationSteps runtimeSteps :=
  Creation.certify contract (source contract.variables initializers) creation runtime creationSteps runtimeSteps
    calls initSize runtimeSize runtimePrefix trace

end Compiler.Validation.SolidityStorage.Initialization
