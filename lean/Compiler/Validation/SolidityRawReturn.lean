/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Validation.SolidityNoReturn

/-! Closed inline assembly: `mstore(0, literal); return(0, 32)`.
The return terminates the call with raw memory bytes, without Solidity result
cleanup. The source adapter admits exactly these two operations and literal
operands; it does not admit general assembly or access to Solidity variables. -/
namespace Compiler.Validation.SolidityRawReturn
open Contract.Evm SolidityFunction

def bytes (value : BitVec 256) (memory : Contract.Interaction.Memory) : List UInt8 :=
  (memory.write 0 (Contract.Interaction.wordBytes value)).read 0 32

theorem bytes_eq (value : BitVec 256) (memory : Contract.Interaction.Memory) :
    bytes value memory = Contract.Interaction.wordBytes value :=
  return_word memory 0 value

def outcome (source : SolidityNoReturn.Source) (value : BitVec 256) (input : Input) : Halt :=
  SolidityNoReturn.returning source (bytes value (fun _ => 0)) input

end Compiler.Validation.SolidityRawReturn
