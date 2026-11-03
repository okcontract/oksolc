/-
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.
-/
import Compiler.Extraction.Dispatch
import Compiler.Extraction.ConstructorPair

namespace Compiler.Extraction.Dispatch
open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner
open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul

variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]

-- Source SHA-256: 4f77329fcde8c89bb2429491fd7f8545f343c04b6630065c919e558c460fbf6d
-- Opcodes SHA-256: 49798b18d069e27354224c7aa6f551399c2b4bf3612bb7e1b55dacc764751ea2
-- Expression classes SHA-256: d66c002eb6f32b6886bc4c6cb24b33b4551f47a98d95fd5c5ad84a97f64b0603
-- EVM versions SHA-256: 5e84058712718707559b37b4129377fd03a336ef04bd35325060799760c7bcd4
def opADD : Opcode := 1
def opADDMOD : Opcode := 8
def opADDRESS : Opcode := 48
def opAND : Opcode := 22
def opBALANCE : Opcode := 49
def opBYTE : Opcode := 26
def opDIV : Opcode := 4
def opEQ : Opcode := 20
def opEXP : Opcode := 10
def opGT : Opcode := 17
def opISZERO : Opcode := 21
def opLT : Opcode := 16
def opMOD : Opcode := 6
def opMUL : Opcode := 2
def opMULMOD : Opcode := 9
def opNOT : Opcode := 25
def opOR : Opcode := 23
def opSAR : Opcode := 29
def opSDIV : Opcode := 5
def opSELFBALANCE : Opcode := 71
def opSGT : Opcode := 19
def opSHL : Opcode := 27
def opSHR : Opcode := 28
def opSIGNEXTEND : Opcode := 11
def opSLT : Opcode := 18
def opSUB : Opcode := 3
def opXOR : Opcode := 24

def versionRank : Version → Nat
  | .homestead => 0
  | .tangerineWhistle => 1
  | .spuriousDragon => 2
  | .byzantium => 3
  | .constantinople => 4
  | .petersburg => 5
  | .istanbul => 6
  | .berlin => 7
  | .london => 8
  | .paris => 9
  | .shanghai => 10
  | .cancun => 11
  | .prague => 12
  | .osaka => 13
  | .amsterdam => 14
  | .future => 15

def hasBitwiseShifting (version : Version) : Bool := versionRank version >= 4
def hasSelfBalance (version : Version) : Bool := versionRank version >= 6
def defaultOptions : Options := ⟨false, none⟩

def collectConstants (reads : Reads) : List NodeId → Except Storage.ReadError (Option (List Word))
  | [] => .ok (some [])
  | id :: rest => do
    let some value ← reads.constant id | return none
    let some values ← collectConstants reads rest | return none
    return some (value :: values)

def algebraicBuilder (constructors : Constructors Debug m) : Builder m Debug :=
  ⟨constructors.constant, fun op => constructors.operation
    (match op with | .NOT => opNOT | .SUB => opSUB | .ISZERO => opISZERO)⟩

def constantStage (reads : Reads) (constructors : Constructors Debug m) (instruction : Opcode)
    (arguments : List NodeId) (debug : Debug)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  if arguments.length > 3 ∨ arguments.isEmpty then return none
  let some values ← query (fun reads => collectConstants reads arguments) | return none
  let some value ← arithmetic (Folding.run Folding.helpers Folding.clauses instruction values) | return none
  return some (← constructors.constant value debug)

@[reducible] def binaryStageWithInputs (reads : Reads) (constructors : Constructors Debug m) (usizeBits : Nat)
    (instruction : Opcode) (left right : NodeId) (debug : Debug) (options : Options)
    (operand : OperandRead m := logicalOperand)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  let leftConstant ← query (fun reads => reads.constant left)
  let rightConstant ← query (fun reads => reads.constant right)
  if let some replacement := zigSelect instruction .constants ⟨leftConstant, rightConstant, false⟩ then
    return some (← zigApply replacement (algebraicBuilder constructors) left right debug)
  if instruction == opSDIV then
    if rightConstant == some 0 || leftConstant == some 0 then
      return some (← constructors.constant 0 debug)
    if rightConstant == some 1 then return some left
  if instruction == opAND then
    if rightConstant == some 255 then
      if let some inner ← query (fun reads => reads.operation left opBYTE) then
        return some (← constructors.borrowedOperation inner.address opBYTE inner.items debug)
  if instruction == opBYTE then
    if leftConstant == some 31 then
      return some (← ConstructorPair.scalars constructors opAND right (← constructors.constant 255 debug) debug)
  if sameExpression reads left right then
    if let some replacement := zigSelect instruction .equal ⟨none, none, true⟩ then
      return some (← zigApply replacement (algebraicBuilder constructors) left right debug)
    if instruction == opSLT || instruction == opSGT then
      return some (← constructors.constant 0 debug)
  if instruction == opXOR then
    if let some id ← query (fun reads => cancelNestedBinary reads opXOR left right) then return some id
    if let some id ← query (fun reads => cancelNestedBinary reads opXOR right left) then return some id
  if instruction == opOR then
    if (← query (fun reads => absorbedOccurrence reads left right opAND)).isSome then return some left
    if let some first ← query (fun reads => absorbedOccurrence reads right left opAND) then return some first
    if (← query (fun reads => isNegation reads left right)) then
      return some (← constructors.constant (BitVec.allOnes 256) debug)
    if (← query (fun reads => isNegation reads right left)) then
      return some (← constructors.constant (BitVec.allOnes 256) debug)
  if instruction == opAND then
    if (← query (fun reads => absorbedOccurrence reads left right opOR)).isSome then return some left
    if let some first ← query (fun reads => absorbedOccurrence reads right left opOR) then return some first
    if (← query (fun reads => isNegation reads left right)) then return some (← constructors.constant 0 debug)
    if (← query (fun reads => isNegation reads right left)) then return some (← constructors.constant 0 debug)
  if instruction == opAND || instruction == opOR then
    if let some id ← dropRepeatedLocal reads constructors.localOperation instruction left right false debug query then return some id
    if let some id ← dropRepeatedLocal reads constructors.localOperation instruction right left true debug query then return some id
  if instruction == opSIGNEXTEND then
    if let some inner ← query (fun reads => reads.operation right opSIGNEXTEND) then
      if let [index, value] := inner.items then
        if sameExpression reads left index then
          return some (← constructors.operation opSIGNEXTEND [left, ← operand inner 1 value] debug)
        if let some outerByte := leftConstant then
          if let some innerByte ← query (fun reads => reads.constant index) then
            return some (← constructors.operation opSIGNEXTEND
              [← constructors.constant (if outerByte.toNat ≤ innerByte.toNat then outerByte else innerByte) debug, ← operand inner 1 value] debug)
  if instruction == opMOD then
    if options.forYul then
      if let some modulus := rightConstant then
        if (← arithmetic (BinaryLogarithm.binaryLogarithm usizeBits modulus)).isSome then
          if let some nested ← query (fun reads => reads.operation left opMUL) then
            if let [a, b] := nested.items then
              return some (← constructors.operation opMULMOD [← operand nested 0 a, ← operand nested 1 b, right] debug)
          if let some nested ← query (fun reads => reads.operation left opADD) then
            if let [a, b] := nested.items then
              return some (← constructors.operation opADDMOD [← operand nested 0 a, ← operand nested 1 b, right] debug)
    if let some modulus := rightConstant then
      if (← arithmetic (BinaryLogarithm.binaryLogarithm usizeBits modulus)).isSome then
        return some (← ConstructorPair.scalars constructors opAND left (← constructors.constant (← subWord modulus 1) debug) debug)
  if instruction == opSHL || instruction == opSHR then
    if let some amount := leftConstant then
      if amount.toNat ≥ 256 then return some (← constructors.constant 0 debug)
  if instruction == opBYTE then
    if let some index := leftConstant then
      if index.toNat ≥ 32 then return some (← constructors.constant 0 debug)
  if instruction == opSIGNEXTEND then
    if let some index := leftConstant then
      if index.toNat ≥ 31 then return some right
  if instruction == opAND then
    if let some id ← SignExtendMask.stripRedundantSignExtendMaskWithInputs reads constructors left right debug operand query then return some id
    if let some id ← SignExtendMask.stripRedundantSignExtendMaskWithInputs reads constructors right left debug operand query then return some id
    if let some opcode ← query (fun reads => AddressMask.addressInstruction reads left right) then
      return some (← constructors.operation opcode [] debug)
    if let some opcode ← query (fun reads => AddressMask.addressInstruction reads right left) then
      return some (← constructors.operation opcode [] debug)
  if Associative.isAssociative instruction then
    if let some id ← Associative.reassociate reads constructors instruction left right false debug query then return some id
    if let some id ← Associative.reassociate reads constructors instruction right left true debug query then return some id
  if instruction == opSHL || instruction == opSHR then
    if let some outerShift := leftConstant then
      if let some inner ← query (fun reads => reads.operation right instruction) then
        if let [index, value] := inner.items then
          if let some innerShift ← query (fun reads => reads.constant index) then
            if outerShift.toNat ≥ 256 - min innerShift.toNat 256 then
              return some (← constructors.constant 0 debug)
            return some (← constructors.operation instruction
              [← constructors.constant (← addWord outerShift innerShift) debug, ← operand inner 1 value] debug)
      let opposite := if instruction == opSHL then opSHR else opSHL
      if let some inner ← query (fun reads => reads.operation right opposite) then
        if let [index, value] := inner.items then
          if let some innerShift ← query (fun reads => reads.constant index) then
            if outerShift.toNat < 256 ∧ innerShift.toNat < 256 then
              return some (← OppositeShifts.combineOppositeShifts constructors instruction outerShift innerShift value debug)
      if let some inner ← query (fun reads => reads.operation right opAND) then
        if inner.items.length == 2 then
          if let some masked ← query (fun reads => splitConstant reads inner.items) then
            if outerShift.toNat < 256 then
              let shift ← arithmetic (Folding.Zig.narrow 8 outerShift.toNat)
              let mask := if instruction == opSHL then masked.value <<< shift else masked.value >>> shift
              let shifted ← ConstructorPair.scalars constructors instruction left masked.expression debug
              return some (← ConstructorPair.scalars constructors opAND shifted (← constructors.constant mask debug) debug)
  if instruction == opAND then
    if let some id ← AlternatingMask.distributeAlternatingMaskWithInputs reads constructors left right debug operand query then return some id
    if let some id ← ShiftMasks.removeCoveredShiftMask reads constructors left right debug query then return some id
    if let some id ← ShiftMasks.removeCoveredShiftMask reads constructors right left debug query then return some id
    if let some lhs ← query (fun reads => reads.operation left opSHL) then
      if let some rhs ← query (fun reads => reads.operation right opSHL) then
        if let [amount, a] := lhs.items then
          if let [otherAmount, b] := rhs.items then
            if sameExpression reads amount otherAmount then
              let combined ← constructors.operation opAND [← operand lhs 1 a, ← operand rhs 1 b] debug
              return some (← constructors.operation opSHL [← operand lhs 0 amount, combined] debug)
  if instruction == opMUL then
    if let some id ← ShiftMasks.powerOfTwoShiftProductWithInputs reads constructors.operation left right debug operand query then return some id
    if let some id ← ShiftMasks.powerOfTwoShiftProductWithInputs reads constructors.operation right left debug operand query then return some id
  if instruction == opDIV then
    if let some shift ← query (fun reads => reads.operation right opSHL) then
      if let [amount, base] := shift.items then
        if (← query (fun reads => reads.constant base)) == some 1 then
          return some (← constructors.operation opSHR [← operand shift 0 amount, left] debug)
  if instruction == opBYTE then
    if let some index := leftConstant then
      if let some shift ← query (fun reads => reads.operation right opSHL) then
        if let [amountId, value] := shift.items then
          if let some amount ← query (fun reads => reads.constant amountId) then
            if amount.toNat % 8 = 0 ∧ index.toNat ≤ 32 ∧ amount.toNat ≤ 256 then
              return some (← constructors.operation opBYTE
                [← constructors.constant (← addWord index (BitVec.ofNat 256 (amount.toNat / 8))) debug, ← operand shift 1 value] debug)
      if let some shift ← query (fun reads => reads.operation right opSHR) then
        if let [amountId, value] := shift.items then
          if let some amount ← query (fun reads => reads.constant amountId) then
            if index.toNat < amount.toNat / 8 then return some (← constructors.constant 0 debug)
            if amount.toNat % 8 = 0 ∧ index.toNat < 32 ∧ amount.toNat ≤ 256 then
              return some (← constructors.operation opBYTE
                [← constructors.constant (← subWord index (BitVec.ofNat 256 (amount.toNat / 8))) debug, ← operand shift 1 value] debug)
  if instruction == opSHL then
    if let some amount := leftConstant then
      if let some inner ← query (fun reads => reads.operation right opSIGNEXTEND) then
        if let [indexId, value] := inner.items then
          if let some index ← query (fun reads => reads.constant indexId) then
            if amount &&& 7 = 0 ∧ amount.toNat ≤ 256 ∧ index.toNat ≤ 32 then
              let shifted ← constructors.operation opSHL [left, ← operand inner 1 value] debug
              return some (← ConstructorPair.scalars constructors opSIGNEXTEND
                (← constructors.constant (← addWord (amount >>> 3) index) debug) shifted debug)
  if instruction == opSIGNEXTEND then
    if let some index := leftConstant then
      if let some shift ← query (fun reads => reads.operation right opSHR) then
        if let [amountId, value] := shift.items then
          if let some amount ← query (fun reads => reads.constant amountId) then
            if amount.toNat % 8 = 0 ∧ amount.toNat ≤ 256 ∧ index.toNat ≤ 256 then
              let remaining ← subWord 256 amount
              let endIndex ← addWord index 1
              if remaining.toNat / 8 = endIndex.toNat then
                return some (← constructors.operation opSAR [← operand shift 0 amountId, ← operand shift 1 value] debug)
  if instruction == opSUB then
    if let some constant := rightConstant then
      return some (← ConstructorPair.scalars constructors opADD left (← constructors.constant (0 - constant) debug) debug)
    if let some nested ← query (fun reads => reads.operation left opADD) then
      if let some parts ← query (fun reads => splitConstant reads nested.items) then
        let difference ← ConstructorPair.scalars constructors opSUB parts.expression right debug
        return some (← ConstructorPair.scalars constructors opADD
          difference (← constructors.materialize parts.constantExpression parts.value debug) debug)
    if let some nested ← query (fun reads => reads.operation right opADD) then
      if let some parts ← query (fun reads => splitConstant reads nested.items) then
        let difference ← ConstructorPair.scalars constructors opSUB left parts.expression debug
        return some (← ConstructorPair.scalars constructors opADD difference (← constructors.constant (0 - parts.value) debug) debug)
    if let some nested ← query (fun reads => reads.operation left opSUB) then
      if let [a, b] := nested.items then
        if let some constant ← query (fun reads => reads.constant b) then
          let difference ← constructors.operation opSUB [← operand nested 0 a, right] debug
          return some (← constructors.operation opSUB [difference, ← constructors.materialize (← operand nested 1 b) constant debug] debug)
        if let some constant ← query (fun reads => reads.constant a) then
          let sum ← constructors.operation opADD [← operand nested 1 b, right] debug
          return some (← constructors.operation opSUB [← constructors.materialize (← operand nested 0 a) constant debug, sum] debug)
    if let some nested ← query (fun reads => reads.operation right opSUB) then
      if let [a, b] := nested.items then
        if let some constant ← query (fun reads => reads.constant b) then
          let difference ← constructors.operation opSUB [left, ← operand nested 0 a] debug
          return some (← ConstructorPair.scalars constructors opADD difference (← constructors.constant constant debug) debug)
        if let some constant ← query (fun reads => reads.constant a) then
          let sum ← constructors.operation opADD [left, ← operand nested 1 b] debug
          return some (← ConstructorPair.scalars constructors opADD sum (← constructors.constant (0 - constant) debug) debug)
  return none


/-- Logical projection of the same source body. -/
def binaryStage (reads : Reads) (constructors : Constructors Debug m) (usizeBits : Nat)
    (instruction : Opcode) (left right : NodeId) (debug : Debug) (options : Options) : m (Option NodeId) :=
  binaryStageWithInputs reads constructors usizeBits instruction left right debug options

@[reducible] def unaryStageWithInputs (reads : Reads) (constructors : Constructors Debug m) (instruction : Opcode)
    (value : NodeId) (debug : Debug) (operand : OperandRead m := logicalOperand)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  if instruction == opNOT then
    if let some inner ← query (fun reads => reads.operation value opNOT) then
      if let [id] := inner.items then return some id
  if instruction == opISZERO then
    if let some second ← query (fun reads => reads.operation value opISZERO) then
      if let [id] := second.items then
        if let some third ← query (fun reads => reads.operation id opISZERO) then
          if let [inner] := third.items then
            return some (← constructors.operation opISZERO [← operand third 0 inner] debug)
        if let some inner ← query (fun reads => reads.operation id opEQ) then
          return some (← constructors.borrowedOperation inner.address opEQ inner.items debug)
        if let some inner ← query (fun reads => reads.operation id opLT) then
          return some (← constructors.borrowedOperation inner.address opLT inner.items debug)
        if let some inner ← query (fun reads => reads.operation id opSLT) then
          return some (← constructors.borrowedOperation inner.address opSLT inner.items debug)
        if let some inner ← query (fun reads => reads.operation id opGT) then
          return some (← constructors.borrowedOperation inner.address opGT inner.items debug)
        if let some inner ← query (fun reads => reads.operation id opSGT) then
          return some (← constructors.borrowedOperation inner.address opSGT inner.items debug)
    if let some inner ← query (fun reads => reads.operation value opXOR) then
      return some (← constructors.borrowedOperation inner.address opEQ inner.items debug)
    if let some inner ← query (fun reads => reads.operation value opSUB) then
      return some (← constructors.borrowedOperation inner.address opEQ inner.items debug)
  return none


/-- Logical projection of the same source body. -/
def unaryStage (reads : Reads) (constructors : Constructors Debug m) (instruction : Opcode)
    (value : NodeId) (debug : Debug) : m (Option NodeId) :=
  unaryStageWithInputs reads constructors instruction value debug

/-- The max-base EXP constructor sequence is shared with its physical literal
binding. The parity callback evaluates the exponent after constant returns. -/
def maxExponent (constructors : Constructors Debug m) (parity : NodeId → Debug → m NodeId)
    (debug : Debug) : m (Option NodeId) := do
  let one ← constructors.constant 1 debug
  let odd ← parity one debug
  let even ← constructors.operation opISZERO [odd] debug
  return some (← ConstructorPair.scalars constructors opSUB even odd debug)

/-- Shared source literal segment. The operand action runs at its source
position, including after a recursive constant constructor has returned. -/
def shiftInput (constructors : Constructors Debug m) (constantFirst : Bool)
    (instruction : Opcode) (value : Word) (operand : m NodeId) (debug : Debug) : m NodeId := do
  if constantFirst then
    let constant ← constructors.constant value debug
    let id ← operand
    constructors.operation instruction [constant, id] debug
  else
    let id ← operand
    let constant ← constructors.constant value debug
    constructors.operation instruction [id, constant] debug

@[reducible] def evmStageWithInputs (reads : Reads) (constructors : Constructors Debug m) (usizeBits : Nat)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug) (version : Version)
    (operand : OperandRead m := logicalOperand) (address : Nat := 0)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) := do
  if instruction == opBALANCE then
    if let [id] := arguments then
      if hasSelfBalance version then
        if let some address ← query (fun reads => reads.operation id opADDRESS) then
          if address.items.isEmpty then return some (← constructors.operation opSELFBALANCE [] debug)
  if instruction == opEXP then
    if let [baseId, exponent] := arguments then
      let base ← query (fun reads => reads.constant baseId)
      if base == some 0 then return some (← constructors.operation opISZERO [← operand ⟨address, arguments⟩ 1 exponent] debug)
      if base == some 1 then return some (← constructors.constant 1 debug)
      if base == some 2 && hasBitwiseShifting version then
        return some (← shiftInput constructors false opSHL 1 (operand ⟨address, arguments⟩ 1 exponent) debug)
      if base == some (BitVec.allOnes 256) then
        return ← maxExponent constructors (fun one debug => do constructors.operation opAND [← operand ⟨address, arguments⟩ 1 exponent, one] debug) debug
  if hasBitwiseShifting version then
    if let [left, right] := arguments then
      if instruction == opMUL then
        if let some constant ← query (fun reads => reads.constant left) then
          if let some power ← arithmetic (BinaryLogarithm.binaryLogarithm usizeBits constant) then
            return some (← shiftInput constructors true opSHL (BitVec.ofNat 256 power) (operand ⟨address, arguments⟩ 1 right) debug)
        if let some constant ← query (fun reads => reads.constant right) then
          if let some power ← arithmetic (BinaryLogarithm.binaryLogarithm usizeBits constant) then
            return some (← shiftInput constructors true opSHL (BitVec.ofNat 256 power) (operand ⟨address, arguments⟩ 0 left) debug)
      if instruction == opDIV then
        if let some constant ← query (fun reads => reads.constant right) then
          if let some power ← arithmetic (BinaryLogarithm.binaryLogarithm usizeBits constant) then
            return some (← shiftInput constructors true opSHR (BitVec.ofNat 256 power) (operand ⟨address, arguments⟩ 0 left) debug)
  return none


/-- Logical projection of the same source body. -/
def evmStage (reads : Reads) (constructors : Constructors Debug m) (usizeBits : Nat)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug) (version : Version) : m (Option NodeId) :=
  evmStageWithInputs reads constructors usizeBits instruction arguments debug version

@[reducible] def simplifyOptionsWithInputs (reads : Reads) (constructors : Constructors Debug m) (usizeBits : Nat)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug) (options : Options)
    (operand : OperandRead m := logicalOperand) (address : Nat := 0)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) :=
  orNext (constantStage reads constructors instruction arguments debug query) <|
    orNext (match arguments with
      | [left, right] => binaryStageWithInputs reads constructors usizeBits instruction left right debug options operand query
      | _ => pure none) <|
    orNext (match arguments with
      | [value] => unaryStageWithInputs reads constructors instruction value debug operand query
      | _ => pure none) <|
    match options.evmVersion with
    | some version => evmStageWithInputs reads constructors usizeBits instruction arguments debug version operand address query
    | none => pure none


/-- Logical projection of the same source body. -/
def simplifyWithOptions (reads : Reads) (constructors : Constructors Debug m) (usizeBits : Nat)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug) (options : Options) : m (Option NodeId) :=
  simplifyOptionsWithInputs reads constructors usizeBits instruction arguments debug options

def simplifyWithInputs (reads : Reads) (constructors : Constructors Debug m) (usizeBits : Nat)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug)
    (operand : OperandRead m := logicalOperand) (address : Nat := 0)
    (query : QueryRead m := fun action => readAction (action reads)) : m (Option NodeId) :=
  simplifyOptionsWithInputs reads constructors usizeBits instruction arguments debug defaultOptions operand address query

/-- Logical projection of the same source body. -/
def simplify (reads : Reads) (constructors : Constructors Debug m) (usizeBits : Nat)
    (instruction : Opcode) (arguments : List NodeId) (debug : Debug) : m (Option NodeId) :=
  simplifyWithInputs reads constructors usizeBits instruction arguments debug


end Compiler.Extraction.Dispatch
