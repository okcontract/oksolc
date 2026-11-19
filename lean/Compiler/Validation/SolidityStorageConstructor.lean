/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityStorageInitialization

namespace Compiler.Validation.SolidityStorage.Constructor
open Contract.Evm

structure Body where
  statements : List Statement := []
  checked : Bool := true
  payable : Bool := false

/-- A constructor's bare return ends initialization; it never ABI-encodes a
runtime return value. Declaration initializers always use checked arithmetic,
even when the subsequent constructor body is unchecked. -/
def result (variables : Layout) (initializers : List Initialization.Initializer)
    (body : Body) (input : Input) : Outcome :=
  if !body.payable && input.value != 0#256 then .reverted [] else
    match Initialization.evaluate variables initializers (fun _ => 0) with
    | .error bytes => .reverted bytes
    | .ok cells =>
      match SolidityStorage.statements variables
          { name := "constructor", parameters := [], body := .literal 0, checked := body.checked }
          input false body.statements cells with
      | .next after | .halt (.returned _ after) => .returned [] after
      | .halt outcome => outcome

abbrev TracePreserves (variables : Layout) (initializers : List Initialization.Initializer)
    (body : Body) := Creation.TracePreserves (result variables initializers body)

abbrev Preserves (source : ContractSource) (initializers : List Initialization.Initializer)
    (body : Body) := Creation.Preserves source (result source.variables initializers body)

/-- Initializers, the complete constructor statement tree, exact creation bytes,
all frame gas budgets, whole-store/code installation and every runtime call.
Source faults and reverts remain distinct, and only source success requires a
successful deployment witness. -/
theorem certify (source : ContractSource) (initializers : List Initialization.Initializer) (body : Body)
    (creation runtime : List UInt8) (creationSteps runtimeSteps : Nat)
    (calls : CallsPreserves source runtime runtimeSteps)
    (initSize : creation.length ≤ 49152) (runtimeSize : runtime.length ≤ 24576)
    (runtimePrefix : runtime.head? ≠ some 0xef)
    (trace : TracePreserves source.variables initializers body creation runtime creationSteps) :
    Preserves source initializers body creation runtime creationSteps runtimeSteps :=
  Creation.certify source (result source.variables initializers body) creation runtime creationSteps runtimeSteps
    calls initSize runtimeSize runtimePrefix trace

end Compiler.Validation.SolidityStorage.Constructor
