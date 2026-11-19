#!/usr/bin/env python3
"""Connect the remaining RuleList literals, retaining native indexed reads.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
import extract_rule_pair_input as pairs
import extract_rule_shift_input as shifts
from extract_compiler import ROOT, Unsupported
from extract_storage import lex

OUTPUT = ROOT / 'lean/Compiler/Extraction/RuleLiteralInputProgram.lean'
# Source-local views keep their allocation, offset and length. Every indexed
# expression is an actual load in its initializer position, even an ID passed
# to materializeConstant (which discards that ID only after evaluating it).
# name, parameters, opcode, ordered elements, exact admitted source call
SITES = (
 ('sameSignextend', '(left : NodeId) (inner : View)', 'Dispatch.opSIGNEXTEND', 'left, ← read inner 1',
  'classes.makeOperation(.SIGNEXTEND, &.{ left, inner[1] }, debug_data)'),
 ('minimumSignextend', '(outerByte innerByte : Word) (inner : View)', 'Dispatch.opSIGNEXTEND',
  '← c.constant (if outerByte.toNat ≤ innerByte.toNat then outerByte else innerByte) debug, ← read inner 1',
  'classes.makeOperation(.SIGNEXTEND, &.{ try classes.makeConstant(@min(outer_byte, inner_byte), debug_data), inner[1] }, debug_data,)'),
 ('modularMultiply', '(nested : View) (right : NodeId)', 'Dispatch.opMULMOD', '← read nested 0, ← read nested 1, right',
  'classes.makeOperation(.MULMOD, &.{ nested[0], nested[1], right }, debug_data,)'),
 ('modularAdd', '(nested : View) (right : NodeId)', 'Dispatch.opADDMOD', '← read nested 0, ← read nested 1, right',
  'classes.makeOperation(.ADDMOD, &.{ nested[0], nested[1], right }, debug_data,)'),
 ('sameDirectionShift', '(instruction : Opcode) (outerShift innerShift : Word) (inner : View)', 'instruction',
  '← c.constant (← Dispatch.addWord outerShift innerShift) debug, ← read inner 1',
  'classes.makeOperation(instruction, &.{ try classes.makeConstant(outer_shift + inner_shift, debug_data), inner[1] }, debug_data,)'),
 ('andShifted', '(lhs rhs : View)', 'Dispatch.opAND', '← read lhs 1, ← read rhs 1',
  'classes.makeOperation(.AND, &.{ lhs_shift[1], rhs_shift[1] }, debug_data)'),
 ('restoreShift', '(lhs : View) (combined : NodeId)', 'Dispatch.opSHL', '← read lhs 0, combined',
  'classes.makeOperation(.SHL, &.{ lhs_shift[0], combined }, debug_data)'),
 ('divideShift', '(shift : View) (left : NodeId)', 'Dispatch.opSHR', '← read shift 0, left',
  'classes.makeOperation(.SHR, &.{ shift[0], left }, debug_data)'),
 ('byteLeftShift', '(index amount : Word) (shift : View)', 'Dispatch.opBYTE',
  '← c.constant (← Dispatch.addWord index (amount / 8)) debug, ← read shift 1',
  'classes.makeOperation(.BYTE, &.{ try classes.makeConstant(left_constant.? + amount / 8, debug_data), shift[1] }, debug_data,)'),
 ('byteRightShift', '(index amount : Word) (shift : View)', 'Dispatch.opBYTE',
  '← c.constant (← Dispatch.subWord index (amount / 8)) debug, ← read shift 1',
  'classes.makeOperation(.BYTE, &.{ try classes.makeConstant(left_constant.? - amount / 8, debug_data), shift[1] }, debug_data,)'),
 ('shiftSignextend', '(left : NodeId) (signExtend : View)', 'Dispatch.opSHL', 'left, ← read signExtend 1',
  'classes.makeOperation(.SHL, &.{ left, sign_extend[1] }, debug_data)'),
 ('arithmeticShift', '(shift : View)', 'Dispatch.opSAR', '← read shift 0, ← read shift 1',
  'classes.makeOperation(.SAR, &.{ shift[0], shift[1] }, debug_data)'),
 ('leftSubtractRightConstant', '(nested : View) (right : NodeId)', 'Dispatch.opSUB', '← read nested 0, right',
  'classes.makeOperation(.SUB, &.{ nested[0], right }, debug_data)'),
 ('subtractMaterializedRight', '(difference : NodeId) (nested : View) (constant : Word)', 'Dispatch.opSUB',
  'difference, ← c.materialize (← read nested 1) constant debug',
  'classes.makeOperation(.SUB, &.{ difference, try classes.materializeConstant(nested[1], constant, debug_data) }, debug_data)'),
 ('leftSubtractLeftConstant', '(nested : View) (right : NodeId)', 'Dispatch.opADD', '← read nested 1, right',
  'classes.makeOperation(.ADD, &.{ nested[1], right }, debug_data)'),
 ('subtractMaterializedLeft', '(nested : View) (constant : Word) (sum : NodeId)', 'Dispatch.opSUB',
  '← c.materialize (← read nested 0) constant debug, sum',
  'classes.makeOperation(.SUB, &.{ try classes.materializeConstant(nested[0], constant, debug_data), sum }, debug_data)'),
 ('rightSubtractRightConstant', '(left : NodeId) (nested : View)', 'Dispatch.opSUB', 'left, ← read nested 0',
  'classes.makeOperation(.SUB, &.{ left, nested[0] }, debug_data)'),
 ('rightSubtractLeftConstant', '(left : NodeId) (nested : View)', 'Dispatch.opADD', 'left, ← read nested 1',
  'classes.makeOperation(.ADD, &.{ left, nested[1] }, debug_data)'),
 ('tripleIszero', '(third : View)', 'Dispatch.opISZERO', '← read third 0',
  'classes.makeOperation(.ISZERO, &.{third[0]}, debug_data)'),
 ('exponentZero', '(arguments : View)', 'Dispatch.opISZERO', '← read arguments 1',
  'classes.makeOperation(.ISZERO, &.{arguments[1]}, debug_data)'),
 ('exponentTwo', '(arguments : View)', 'Dispatch.opSHL', '← read arguments 1, ← c.constant 1 debug',
  'classes.makeOperation(.SHL, &.{ arguments[1], try classes.makeConstant(1, debug_data) }, debug_data,)'),
 ('exponentParity', '(arguments : View) (one : NodeId)', 'Dispatch.opAND', '← read arguments 1, one',
  'classes.makeOperation(.AND, &.{ arguments[1], one }, debug_data)'),
 ('exponentEven', '(parity : NodeId)', 'Dispatch.opISZERO', 'parity',
  'classes.makeOperation(.ISZERO, &.{parity}, debug_data)'),
 ('multiplyLeft', '(power : Nat) (arguments : View)', 'Dispatch.opSHL', '← c.constant (BitVec.ofNat 256 power) debug, ← read arguments 1',
  'classes.makeOperation(.SHL, &.{ try classes.makeConstant(power, debug_data), arguments[1] }, debug_data,)'),
 ('multiplyRight', '(power : Nat) (arguments : View)', 'Dispatch.opSHL', '← c.constant (BitVec.ofNat 256 power) debug, ← read arguments 0',
  'classes.makeOperation(.SHL, &.{ try classes.makeConstant(power, debug_data), arguments[0] }, debug_data,)'),
 ('divide', '(power : Nat) (arguments : View)', 'Dispatch.opSHR', '← c.constant (BitVec.ofNat 256 power) debug, ← read arguments 0',
  'classes.makeOperation(.SHR, &.{ try classes.makeConstant(power, debug_data), arguments[0] }, debug_data,)'),
 ('doubleIszeroFirst', '(value : NodeId)', 'Dispatch.opISZERO', 'value',
  'classes.makeOperation(.ISZERO, &.{value}, debug_data)'),
 ('doubleIszeroSecond', '(inner : NodeId)', 'Dispatch.opISZERO', 'inner',
  'classes.makeOperation(.ISZERO, &.{inner}, debug_data)'),
 ('signextendMask', '(materializedMask : NodeId) (signExtend : View)', 'Dispatch.opAND', 'materializedMask, ← read signExtend 1',
  'classes.makeOperation(.AND, &.{ materialized_mask, sign_extend[1] }, debug_data)'),
 ('alternatingLeft', '(inner : View) (expressionIndex : Nat) (innerMask outerMask : Word)', 'Dispatch.opAND',
  '← read inner expressionIndex, ← c.constant (innerMask &&& outerMask) debug',
  'classes.makeOperation(.AND, &.{ inner[expression_index], try classes.makeConstant(inner_mask & outer_mask, debug_data) }, debug_data,)'),
 ('alternatingRight', '(alternatives : View) (innerIndex : Nat) (materializedMask : NodeId)', 'Dispatch.opAND',
  '← read alternatives (← Dispatch.arithmetic (Folding.Zig.checkedSub 1 innerIndex)), materializedMask',
  'classes.makeOperation(.AND, &.{ alternatives[1 - inner_index], materialized_outer_mask }, debug_data,)'),
 ('shiftProduct', '(shift : View) (value : NodeId)', 'Dispatch.opSHL', '← read shift 0, value',
  'classes.makeOperation(.SHL, &.{ shift[0], value }, debug_data)'),
)


def admitted(source, opcodes, storage, versions):
    scalar = pairs.admitted(source, opcodes, storage, versions)
    covered = {site['startByte'] for site in scalar}
    calls = [site for site in pairs.constructor_inventory.sites(source)
             if site['storage'] == 'temporary' and site['arity'] and site['startByte'] not in covered]
    result = []
    for name, parameters, opcode, elements, expression in SITES:
        matches = [site for site in calls if lex(source[site['startByte']:site['endByte']].decode()) == lex(expression)]
        if len(matches) != 1:
            raise Unsupported('native literal input binding changed: ' + name)
        result.append({**matches[0], 'site': name, 'parameters': parameters, 'opcode': opcode, 'elements': elements})
    if len(calls) != len(result) or len({site['startByte'] for site in result}) != len(result):
        raise Unsupported('remaining RuleList literal closure changed')
    return result


def extract(source, opcodes, storage, versions):
    admitted(source, opcodes, storage, versions)
    hashes = ''.join('-- ' + name + ' SHA-256: ' + hashlib.sha256(value).hexdigest() + '\n'
        for name, value in zip(('Source', 'Opcodes', 'Expression classes', 'EVM versions'), (source, opcodes, storage, versions)))
    definitions = []
    shift_names = {site[0] for site in shifts.SITES}
    for name, parameters, opcode, elements, _ in SITES:
        signature = (f'def {name} (context : PairInput.Context σ) {parameters}\n'
                     '    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := ')
        if name in shift_names:
            # These four complete native routes already share their admitted
            # source segment with the dispatcher. Keep one implementation.
            power = '0' if name == 'exponentTwo' else 'power'
            body = f'ShiftInput.zigLiteral context .{name} {power} arguments debug'
        else:
            body = f'do\n  let c := PairInput.constructors context\n  c.operation {opcode} [{elements}] debug'
        definitions.append(signature + body)
    return ('''/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPairInput
import Compiler.Extraction.RuleShiftInputProgram

''' + hashes + '''
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.LiteralInput
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul Compiler.ZigAir.Memory.WordArray

private abbrev read := @ShiftInput.operand

/-- Exact literal segments after their enclosing source queries and guards.
Native views are read in source order through the reached world. Scalar locals
and successful guard/query selection still require their native correspondence.
Together with RulePairInputProgram this covers all 53 nonempty RuleList literals;
it does not cover local arrays or borrowed/forwarded constructor arguments. -/
''' + '\n\n'.join(definitions) + '''

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.LiteralInput
''').encode()


def check():
    values = pairs.owner.inputs()
    scalar = pairs.check()
    shift = shifts.check()
    if extract(*values) != OUTPUT.read_bytes():
        raise ValueError('native RuleList literal admission is stale; review and regenerate')
    sites = admitted(*values)
    return {'sourceSha256': hashlib.sha256(values[0]).hexdigest(),
            'programSha256': hashlib.sha256(OUTPUT.read_bytes()).hexdigest(), 'sites': sites,
            'scalarPairs': scalar, 'delegatedShiftInputs': shift,
            'nonemptyLiteralCount': len(sites) + len(scalar['sites']),
            'scope': 'all nonempty RuleList literal segments, following enclosing queries and guards',
            'completeNativeQueryAndGuardConnectionVerified': False,
            'completeCallSiteClosureVerified': False, 'recursiveInductionVerified': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    if parser.parse_args().check:
        check()
    else:
        OUTPUT.write_bytes(extract(*pairs.owner.inputs()))
