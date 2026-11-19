#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Closed admission of the entire ordered RuleList dispatcher. This is an executable
source model, not yet a semantic-preservation proof for every inline branch.
"""
import argparse
import hashlib
from extract_storage import function
from extract_cache import opcode_values
from extract_compiler import Unsupported
import extract_nested as nested
import extract_folding
import extract_binary_logarithm
import extract_nested_construction
import extract_associative
import extract_shift_masks
import extract_opposite_shifts
import extract_signextend_mask
import extract_address_mask
import extract_alternating_mask

OUTPUT = nested.ROOT / 'lean/Compiler/Extraction/DispatchProgram.lean'
VERSIONS = nested.ROOT / 'src/liblangutil/evm_version.zig'

# Order here is the independent model's constructor spelling, not the native
# integer tag. The emitted rank function is admitted separately against Zig.
VERSION_NAMES = ['Homestead', 'TangerineWhistle', 'SpuriousDragon', 'Byzantium', 'Constantinople', 'Petersburg', 'Istanbul', 'Berlin', 'London', 'Paris', 'Shanghai', 'Cancun', 'Prague', 'Osaka', 'Amsterdam', 'Future']
OPCODES = ['ADD', 'ADDMOD', 'ADDRESS', 'AND', 'BALANCE', 'BYTE', 'DIV', 'EQ', 'EXP', 'GT', 'ISZERO', 'LT', 'MOD', 'MUL', 'MULMOD', 'NOT', 'OR', 'SAR', 'SDIV', 'SELFBALANCE', 'SGT', 'SHL', 'SHR', 'SIGNEXTEND', 'SLT', 'SUB', 'XOR']

PROGRAM = '''
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

'''


def extract(data, opcodes, storage, versions):
    nested.extract(data, opcodes, storage)
    extract_folding.extract(data, opcodes)
    extract_binary_logarithm.extract(data)
    for helper in [extract_nested_construction, extract_associative, extract_shift_masks,
                   extract_opposite_shifts, extract_signextend_mask, extract_address_mask,
                   extract_alternating_mask]:
        helper.extract(data, opcodes, storage)
    function(data, 'const max_word =').expect('~@as(u256, 0);')
    function(data, 'const Algebraic =').expect('@import("algebraic_rules.zig");')
    function(data, 'const EVMVersion =').expect('@import("../liblangutil/evm_version.zig").EVMVersion;')
    function(data, 'pub const SimplificationOptions = struct').expect('''{
        for_yul_optimizer: bool = false,
        evm_version: ?EVMVersion = null,
    };''')
    function(data, '''pub fn simplify(classes: anytype, instruction: Instruction,
        arguments: []const ExpressionId, debug_data: DebugData,) !?ExpressionId''').expect('''{
        return simplifyWithOptions(classes, instruction, arguments, debug_data, .{});
    }''')
    function(data, '''pub fn simplifyWithOptions(
        classes: anytype, instruction: Instruction, arguments: []const ExpressionId,
        debug_data: DebugData, options: SimplificationOptions,
    ) !?ExpressionId''').expect('''{
    // Part 1: arithmetic on constants.
    var constant_arguments: [3]u256 = undefined;
    var all_constant = arguments.len <= constant_arguments.len and arguments.len != 0;
    if (all_constant) {
        for (arguments, 0..) |id, index| {
            constant_arguments[index] = classes.knownConstantValue(id) orelse {
                all_constant = false;
                break;
            };
        }
    }
    if (all_constant) {
        if (foldConstants(instruction, constant_arguments[0..arguments.len])) |value|
            return try classes.makeConstant(value, debug_data);
    }

    if (arguments.len == 2) {
        const left = arguments[0];
        const right = arguments[1];
        const left_constant = classes.knownConstantValue(left);
        const right_constant = classes.knownConstantValue(right);

        // Part 2: the checked algebraic table, then the remaining nested,
        // signed and byte rules. These cannot preempt a table match for the
        // same opcode; keep them before the equal-expression stage.
        if (Algebraic.select(instruction, .constants, .{ .left = left_constant, .right = right_constant })) |replacement|
            return try Algebraic.apply(replacement, classes, left, right, debug_data);
        switch (instruction) {
            .SDIV => {
                if (right_constant == 0 or left_constant == 0)
                    return try classes.makeConstant(0, debug_data);
                if (right_constant == 1) return left;
            },
            .AND => {
                if (right_constant == 0xff) {
                    if (classes.operationArguments(left, .BYTE)) |byte_args|
                        return try classes.makeOperation(.BYTE, byte_args, debug_data);
                }
            },
            .BYTE => {
                if (left_constant == 31)
                    return try classes.makeOperation(
                        .AND,
                        &.{ right, try classes.makeConstant(0xff, debug_data) },
                        debug_data,
                    );
            },
            else => {},
        }

        // Part 3: operations involving the same stable expression value.
        if (sameExpression(classes, left, right)) {
            if (Algebraic.select(instruction, .equal, .{ .equal = true })) |replacement|
                return try Algebraic.apply(replacement, classes, left, right, debug_data);
            if (instruction == .SLT or instruction == .SGT)
                return try classes.makeConstant(0, debug_data);
        }

        // Part 4: logical combinations.
        if (instruction == .XOR) {
            if (try cancelNestedBinary(classes, .XOR, left, right)) |id| return id;
            if (try cancelNestedBinary(classes, .XOR, right, left)) |id| return id;
        }
        if (instruction == .OR) {
            if (absorbedOccurrence(classes, left, right, .AND) != null) return left;
            if (absorbedOccurrence(classes, right, left, .AND)) |first| return first;
            if (isNegation(classes, left, right) or isNegation(classes, right, left))
                return try classes.makeConstant(max_word, debug_data);
        }
        if (instruction == .AND) {
            if (absorbedOccurrence(classes, left, right, .OR) != null) return left;
            if (absorbedOccurrence(classes, right, left, .OR)) |first| return first;
            if (isNegation(classes, left, right) or isNegation(classes, right, left))
                return try classes.makeConstant(0, debug_data);
        }

        // Part 4.5: idempotent nested AND/OR and SIGNEXTEND.
        if (instruction == .AND or instruction == .OR) {
            if (try dropRepeatedNested(classes, instruction, left, right, false, debug_data)) |id| return id;
            if (try dropRepeatedNested(classes, instruction, right, left, true, debug_data)) |id| return id;
        }
        if (instruction == .SIGNEXTEND) {
            if (classes.operationArguments(right, .SIGNEXTEND)) |inner| {
                if (inner.len == 2) {
                    if (sameExpression(classes, left, inner[0]))
                        return try classes.makeOperation(.SIGNEXTEND, &.{ left, inner[1] }, debug_data);
                    if (left_constant) |outer_byte| if (classes.knownConstantValue(inner[0])) |inner_byte|
                        return try classes.makeOperation(
                            .SIGNEXTEND,
                            &.{ try classes.makeConstant(@min(outer_byte, inner_byte), debug_data), inner[1] },
                            debug_data,
                        );
                }
            }
        }

        // Part 5: dynamic constant families.
        if (instruction == .MOD) {
            // The Yul optimizer can express the three-argument ADDMOD and
            // MULMOD results; libevmasm's stack-expression optimizer cannot.
            // These precede the generic power-of-two MOD rule upstream.
            if (options.for_yul_optimizer and right_constant != null and
                binaryLogarithm(right_constant.?) != null)
            {
                if (classes.operationArguments(left, .MUL)) |nested|
                    if (nested.len == 2)
                        return try classes.makeOperation(
                            .MULMOD,
                            &.{ nested[0], nested[1], right },
                            debug_data,
                        );
                if (classes.operationArguments(left, .ADD)) |nested|
                    if (nested.len == 2)
                        return try classes.makeOperation(
                            .ADDMOD,
                            &.{ nested[0], nested[1], right },
                            debug_data,
                        );
            }
            if (right_constant) |modulus| if (binaryLogarithm(modulus) != null)
                return try classes.makeOperation(
                    .AND,
                    &.{ left, try classes.makeConstant(modulus - 1, debug_data) },
                    debug_data,
                );
        }
        if ((instruction == .SHL or instruction == .SHR) and
            left_constant != null and left_constant.? >= 256)
            return try classes.makeConstant(0, debug_data);
        if (instruction == .BYTE and left_constant != null and left_constant.? >= 32)
            return try classes.makeConstant(0, debug_data);
        if (instruction == .SIGNEXTEND and left_constant != null and left_constant.? >= 31)
            return right;

        if (instruction == .AND) {
            if (try stripRedundantSignExtendMask(classes, left, right, debug_data)) |id| return id;
            if (try stripRedundantSignExtendMask(classes, right, left, debug_data)) |id| return id;
            if (addressInstruction(classes, left, right)) |address_instruction|
                return try classes.makeOperation(address_instruction, &.{}, debug_data);
            if (addressInstruction(classes, right, left)) |address_instruction|
                return try classes.makeOperation(address_instruction, &.{}, debug_data);
        }

        // Part 7: associative normalization and shift/mask combinations.
        if (isAssociative(instruction)) {
            if (try reassociate(classes, instruction, left, right, false, debug_data)) |id| return id;
            if (try reassociate(classes, instruction, right, left, true, debug_data)) |id| return id;
        }

        if (instruction == .SHL or instruction == .SHR) {
            if (left_constant) |outer_shift| {
                if (classes.operationArguments(right, instruction)) |inner| if (inner.len == 2)
                    if (classes.knownConstantValue(inner[0])) |inner_shift| {
                        if (outer_shift >= 256 -| @min(inner_shift, 256))
                            return try classes.makeConstant(0, debug_data);
                        return try classes.makeOperation(
                            instruction,
                            &.{ try classes.makeConstant(outer_shift + inner_shift, debug_data), inner[1] },
                            debug_data,
                        );
                    };

                const opposite: Instruction = if (instruction == .SHL) .SHR else .SHL;
                if (classes.operationArguments(right, opposite)) |inner| if (inner.len == 2)
                    if (classes.knownConstantValue(inner[0])) |inner_shift|
                        if (outer_shift < 256 and inner_shift < 256)
                            return try combineOppositeShifts(
                                classes,
                                instruction,
                                outer_shift,
                                inner_shift,
                                inner[1],
                                debug_data,
                            );

                if (classes.operationArguments(right, .AND)) |inner| if (inner.len == 2)
                    if (splitConstant(classes, inner)) |masked| {
                        if (outer_shift < 256) {
                            const shifted_mask = if (instruction == .SHL)
                                masked.value << @intCast(outer_shift)
                            else
                                masked.value >> @intCast(outer_shift);
                            const shifted = try classes.makeOperation(
                                instruction,
                                &.{ left, masked.expression },
                                debug_data,
                            );
                            return try classes.makeOperation(
                                .AND,
                                &.{ shifted, try classes.makeConstant(shifted_mask, debug_data) },
                                debug_data,
                            );
                        }
                    };
            }
        }

        if (instruction == .AND) {
            if (try distributeAlternatingMask(classes, left, right, debug_data)) |id| return id;

            if (try removeCoveredShiftMask(classes, left, right, debug_data)) |id| return id;
            if (try removeCoveredShiftMask(classes, right, left, debug_data)) |id| return id;

            if (classes.operationArguments(left, .SHL)) |lhs_shift|
                if (classes.operationArguments(right, .SHL)) |rhs_shift|
                    if (lhs_shift.len == 2 and rhs_shift.len == 2 and sameExpression(classes, lhs_shift[0], rhs_shift[0])) {
                        const combined = try classes.makeOperation(.AND, &.{ lhs_shift[1], rhs_shift[1] }, debug_data);
                        return try classes.makeOperation(.SHL, &.{ lhs_shift[0], combined }, debug_data);
                    };
        }

        if (instruction == .MUL) {
            if (try powerOfTwoShiftProduct(classes, left, right, debug_data)) |id| return id;
            if (try powerOfTwoShiftProduct(classes, right, left, debug_data)) |id| return id;
        }
        if (instruction == .DIV)
            if (classes.operationArguments(right, .SHL)) |shift|
                if (shift.len == 2 and classes.knownConstantValue(shift[1]) == 1)
                    return try classes.makeOperation(.SHR, &.{ shift[0], left }, debug_data);

        if (instruction == .BYTE and left_constant != null) {
            if (classes.operationArguments(right, .SHL)) |shift| if (shift.len == 2)
                if (classes.knownConstantValue(shift[0])) |amount|
                    if (amount % 8 == 0 and left_constant.? <= 32 and amount <= 256)
                        return try classes.makeOperation(
                            .BYTE,
                            &.{ try classes.makeConstant(left_constant.? + amount / 8, debug_data), shift[1] },
                            debug_data,
                        );
            if (classes.operationArguments(right, .SHR)) |shift| if (shift.len == 2)
                if (classes.knownConstantValue(shift[0])) |amount| {
                    if (left_constant.? < amount / 8)
                        return try classes.makeConstant(0, debug_data);
                    if (amount % 8 == 0 and left_constant.? < 32 and amount <= 256)
                        return try classes.makeOperation(
                            .BYTE,
                            &.{ try classes.makeConstant(left_constant.? - amount / 8, debug_data), shift[1] },
                            debug_data,
                        );
                };
        }

        if (instruction == .SHL and left_constant != null) {
            if (classes.operationArguments(right, .SIGNEXTEND)) |sign_extend| if (sign_extend.len == 2)
                if (classes.knownConstantValue(sign_extend[0])) |byte_index|
                    if ((left_constant.? & 7) == 0 and left_constant.? <= 256 and byte_index <= 32) {
                        const shifted = try classes.makeOperation(.SHL, &.{ left, sign_extend[1] }, debug_data);
                        return try classes.makeOperation(
                            .SIGNEXTEND,
                            &.{ try classes.makeConstant((left_constant.? >> 3) + byte_index, debug_data), shifted },
                            debug_data,
                        );
                    };
        }

        if (instruction == .SIGNEXTEND and left_constant != null) {
            if (classes.operationArguments(right, .SHR)) |shift| if (shift.len == 2)
                if (classes.knownConstantValue(shift[0])) |amount|
                    if (amount % 8 == 0 and amount <= 256 and left_constant.? <= 256 and
                        (256 - amount) / 8 == left_constant.? + 1)
                        return try classes.makeOperation(.SAR, &.{ shift[0], shift[1] }, debug_data);
        }

        // Part 8: move constants across subtraction.
        if (instruction == .SUB) {
            if (right_constant) |constant|
                return try classes.makeOperation(
                    .ADD,
                    &.{ left, try classes.makeConstant(0 -% constant, debug_data) },
                    debug_data,
                );

            if (classes.operationArguments(left, .ADD)) |nested| if (splitConstant(classes, nested)) |parts| {
                const difference = try classes.makeOperation(.SUB, &.{ parts.expression, right }, debug_data);
                return try classes.makeOperation(.ADD, &.{ difference, try classes.materializeConstant(parts.constant_expression, parts.value, debug_data) }, debug_data);
            };
            if (classes.operationArguments(right, .ADD)) |nested| if (splitConstant(classes, nested)) |parts| {
                const difference = try classes.makeOperation(.SUB, &.{ left, parts.expression }, debug_data);
                return try classes.makeOperation(
                    .ADD,
                    &.{ difference, try classes.makeConstant(0 -% parts.value, debug_data) },
                    debug_data,
                );
            };
            if (classes.operationArguments(left, .SUB)) |nested| if (nested.len == 2) {
                if (classes.knownConstantValue(nested[1])) |constant| {
                    const difference = try classes.makeOperation(.SUB, &.{ nested[0], right }, debug_data);
                    return try classes.makeOperation(.SUB, &.{ difference, try classes.materializeConstant(nested[1], constant, debug_data) }, debug_data);
                }
                if (classes.knownConstantValue(nested[0])) |constant| {
                    const sum = try classes.makeOperation(.ADD, &.{ nested[1], right }, debug_data);
                    return try classes.makeOperation(.SUB, &.{ try classes.materializeConstant(nested[0], constant, debug_data), sum }, debug_data);
                }
            };
            if (classes.operationArguments(right, .SUB)) |nested| if (nested.len == 2) {
                if (classes.knownConstantValue(nested[1])) |constant| {
                    const difference = try classes.makeOperation(.SUB, &.{ left, nested[0] }, debug_data);
                    return try classes.makeOperation(
                        .ADD,
                        &.{ difference, try classes.makeConstant(constant, debug_data) },
                        debug_data,
                    );
                }
                if (classes.knownConstantValue(nested[0])) |constant| {
                    const sum = try classes.makeOperation(.ADD, &.{ left, nested[1] }, debug_data);
                    return try classes.makeOperation(
                        .ADD,
                        &.{ sum, try classes.makeConstant(0 -% constant, debug_data) },
                        debug_data,
                    );
                }
            };
        }
    }

    // Unary rules from parts 4 and 6.
    if (arguments.len == 1) {
        const value = arguments[0];
        if (instruction == .NOT)
            if (classes.operationArguments(value, .NOT)) |inner|
                if (inner.len == 1) return inner[0];

        if (instruction == .ISZERO) {
            if (classes.operationArguments(value, .ISZERO)) |second| if (second.len == 1) {
                if (classes.operationArguments(second[0], .ISZERO)) |third|
                    if (third.len == 1)
                        return try classes.makeOperation(.ISZERO, &.{third[0]}, debug_data);
                if (classes.operationArguments(second[0], .EQ)) |inner|
                    return try classes.makeOperation(.EQ, inner, debug_data);
                if (classes.operationArguments(second[0], .LT)) |inner|
                    return try classes.makeOperation(.LT, inner, debug_data);
                if (classes.operationArguments(second[0], .SLT)) |inner|
                    return try classes.makeOperation(.SLT, inner, debug_data);
                if (classes.operationArguments(second[0], .GT)) |inner|
                    return try classes.makeOperation(.GT, inner, debug_data);
                if (classes.operationArguments(second[0], .SGT)) |inner|
                    return try classes.makeOperation(.SGT, inner, debug_data);
            };
            if (classes.operationArguments(value, .XOR)) |inner|
                return try classes.makeOperation(.EQ, inner, debug_data);
            if (classes.operationArguments(value, .SUB)) |inner|
                return try classes.makeOperation(.EQ, inner, debug_data);
        }
    }

    // `evmRuleList()` is appended after all context-independent rules.
    if (options.evm_version) |evm_version| {
        if (instruction == .BALANCE and arguments.len == 1 and evm_version.hasSelfBalance())
            if (classes.operationArguments(arguments[0], .ADDRESS)) |address_arguments|
                if (address_arguments.len == 0)
                    return try classes.makeOperation(.SELFBALANCE, &.{}, debug_data);

        if (instruction == .EXP and arguments.len == 2) {
            const base = classes.knownConstantValue(arguments[0]);
            if (base == 0)
                return try classes.makeOperation(.ISZERO, &.{arguments[1]}, debug_data);
            if (base == 1)
                return try classes.makeConstant(1, debug_data);
            if (base == 2 and evm_version.hasBitwiseShifting())
                return try classes.makeOperation(
                    .SHL,
                    &.{ arguments[1], try classes.makeConstant(1, debug_data) },
                    debug_data,
                );
            if (base == max_word) {
                const one = try classes.makeConstant(1, debug_data);
                const parity = try classes.makeOperation(.AND, &.{ arguments[1], one }, debug_data);
                const even = try classes.makeOperation(.ISZERO, &.{parity}, debug_data);
                return try classes.makeOperation(.SUB, &.{ even, parity }, debug_data);
            }
        }

        if (evm_version.hasBitwiseShifting() and arguments.len == 2) switch (instruction) {
            .MUL => {
                if (classes.knownConstantValue(arguments[0])) |constant|
                    if (binaryLogarithm(constant)) |power|
                        return try classes.makeOperation(
                            .SHL,
                            &.{ try classes.makeConstant(power, debug_data), arguments[1] },
                            debug_data,
                        );
                if (classes.knownConstantValue(arguments[1])) |constant|
                    if (binaryLogarithm(constant)) |power|
                        return try classes.makeOperation(
                            .SHL,
                            &.{ try classes.makeConstant(power, debug_data), arguments[0] },
                            debug_data,
                        );
            },
            .DIV => if (classes.knownConstantValue(arguments[1])) |constant|
                if (binaryLogarithm(constant)) |power|
                    return try classes.makeOperation(
                        .SHR,
                        &.{ try classes.makeConstant(power, debug_data), arguments[0] },
                        debug_data,
                    ),
            else => {},
        };
    }

    return null;
}''')
    function(versions, 'pub const Version = enum(c_int)').expect(
        '{ ' + ', '.join(VERSION_NAMES) + ', };')
    function(versions, 'pub fn atLeast(self: EVMVersion, version: Version) bool').expect('''{
        return @backingInt(self.version) >= @backingInt(version);
    }''')
    function(versions, 'pub fn hasBitwiseShifting(self: EVMVersion) bool').expect('''{
        return self.atLeast(.Constantinople);
    }''')
    function(versions, 'pub fn hasSelfBalance(self: EVMVersion) bool').expect('''{
        return self.atLeast(.Istanbul);
    }''')
    bindings = opcode_values(opcodes)
    # The switch-to-ordered-tests translation relies on distinct enum tags.
    if len(set(bindings.values())) != len(bindings):
        raise Unsupported('duplicate native instruction tags')
    opening = ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.Dispatch\nimport Compiler.Extraction.ConstructorPair\n\nnamespace Compiler.Extraction.Dispatch\n'
        'open Compiler.Algebraic Compiler.Extraction.Cache Compiler.Extraction.Interner\n'
        'open Compiler.Extraction.Nested Compiler.Extraction.Associative Contract.Yul\n\n'
        'variable {m : Type → Type} [Monad m] [MonadLift (Except Interner.Error) m]\n\n')
    for name, content in [('Source', data), ('Opcodes', opcodes), ('Expression classes', storage), ('EVM versions', versions)]:
        opening += '-- ' + name + ' SHA-256: ' + hashlib.sha256(content).hexdigest() + '\n'
    opening += '\n'.join('def op' + name + ' : Opcode := ' + str(bindings[name]) for name in OPCODES) + '\n\n'
    opening += 'def versionRank : Version → Nat\n' + ''.join(
        '  | .' + name[0].lower() + name[1:] + ' => ' + str(i) + '\n' for i, name in enumerate(VERSION_NAMES))
    opening += ('\ndef hasBitwiseShifting (version : Version) : Bool := versionRank version >= 4\n'
        'def hasSelfBalance (version : Version) : Bool := versionRank version >= 6\n'
        'def defaultOptions : Options := ⟨false, none⟩\n')
    return (opening + PROGRAM + '\nend Compiler.Extraction.Dispatch\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    emitted = extract(nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes(), VERSIONS.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != emitted:
            raise SystemExit('stale dispatcher extraction')
    else:
        OUTPUT.write_bytes(emitted)


if __name__ == '__main__':
    main()
