/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityContract
import Compiler.Validation.SolidityNoReturn
import Compiler.Validation.SolidityRawReturn

/-! A complete method inventory may mix existing expression functions and
empty functions with no return values, and closed raw-word assembly returns.
Every method keeps its own source
semantics and canonical-call witness; dispatch and deployment are shared. -/
namespace Compiler.Validation.SolidityMethodContract
open Contract.Evm

inductive Method where
  | expression (source : SolidityFunction.Source)
  | empty (source : SolidityNoReturn.Source)
  | rawWord (source : SolidityNoReturn.Source) (value : BitVec 256)

def Method.selector : Method → Nat
  | .expression source => source.selector | .empty source => source.selector
  | .rawWord source _ => source.selector

def Method.ValidCall : Method → Input → Prop
  | .expression source => source.ValidCall | .empty source => source.ValidCall
  | .rawWord source _ => source.ValidCall

def Method.outcome : Method → Input → Halt
  | .expression source => SolidityCall.outcome source | .empty source => SolidityNoReturn.outcome source
  | .rawWord source value => SolidityRawReturn.outcome source value

abbrev CallsPreserves := SolidityDispatch.CallsPreserves Method.selector Method.outcome Method.ValidCall
abbrev Preserves := SolidityDispatch.Preserves Method.selector Method.outcome Method.ValidCall
abbrev certifyCalls := SolidityDispatch.certifyCalls Method.selector Method.outcome Method.ValidCall
abbrev certify := SolidityDispatch.certify Method.selector Method.outcome Method.ValidCall

end Compiler.Validation.SolidityMethodContract
