/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityNoReturn
import Compiler.Validation.SolidityStorage

namespace Compiler.Validation.SolidityABI.Tests
open Contract.Evm

set_option maxRecDepth 4096

def setter : Source := { name := "setAcceptEther", parameters := [.boolean] }
def calldata (value : BitVec 256) : List UInt8 :=
  [0x4f, 0xea, 0x12, 0x0c] ++ Contract.Interaction.wordBytes value

-- Independent signature computation matches the retained corpus method.
example : setter.signature = "setAcceptEther(bool)" := rfl
example : setter.selector = 0x4fea120c := by decide +kernel
example : setter.ValidCall ⟨calldata 0, 0⟩ := by decide +kernel
example : setter.ValidCall ⟨calldata 1, 0⟩ := by decide +kernel
example : ¬setter.Accepts ⟨calldata 2, 0⟩ := by decide +kernel
example : ¬setter.Accepts ⟨calldata 256, 0⟩ := by decide +kernel
example : ¬setter.Accepts ⟨calldata (2^255), 0⟩ := by decide +kernel
example : ¬setter.Accepts ⟨(calldata 1).take 35, 0⟩ := by decide +kernel
example : ¬setter.Accepts ⟨[0, 0, 0, 0] ++ Contract.Interaction.wordBytes 1, 0⟩ := by decide +kernel
example : ¬setter.Accepts ⟨calldata 1, 7⟩ := by decide +kernel
example : ({ setter with payable := true } : Source).Accepts ⟨calldata 1, 7⟩ := by decide +kernel
example : setter.Accepts ⟨calldata 1 ++ [0xff], 0⟩ := by decide +kernel

-- Canonical checks apply to every argument and keep fixed-byte alignment.
def mixed : Source := { name := "mixed", parameters := [.bytes4, .boolean, .word] }
def arguments (tag flag word : BitVec 256) : Input :=
  ⟨[0, 0, 0, 0] ++ Contract.Interaction.wordBytes tag ++
    Contract.Interaction.wordBytes flag ++ Contract.Interaction.wordBytes word, 0⟩
example : mixed.Arguments (arguments (0x12345678 * 2^224) 1 (2^256 - 1)) := by decide +kernel
example : ¬mixed.Arguments (arguments (0x12345678 * 2^224 + 1) 1 0) := by decide +kernel
example : ¬mixed.Arguments (arguments (0x12345678 * 2^224) 2 0) := by decide +kernel

-- The old expression ABI retains exactly its existing admission predicate.
example (source : SolidityFunction.Source) (input : Input) :
    (Source.ofFunction source).Accepts input ↔ SolidityCall.Accepts source input :=
  Source.ofFunction_accepts source input

-- The storage consumer deliberately retains its nonpayable source scope.
example (source : SolidityFunction.Source) (input : Input) :
    (Source.ofFunction { source with payable := false }).Accepts input ↔
      SolidityStorage.Accepts source input := by
  rw [Source.ofFunction_accepts]
  rfl

end Compiler.Validation.SolidityABI.Tests
