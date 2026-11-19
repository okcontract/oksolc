#!/usr/bin/env python3
"""Bind every scalar-only RuleList pair literal to native constructor inputs.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
import constructor_inventory
import extract_rule_unary as owner
from extract_compiler import ROOT, Unsupported
from extract_storage import lex

OUTPUT = ROOT / 'lean/Compiler/Extraction/RulePairInputProgram.lean'
# Full owner admission precedes these exact literal bindings. Parameters are
# source-local scalar values, not snapshots of borrowed elements. Checked
# arithmetic inside a child initializer remains an effect before that child.
# name, parameters, opcode, first, second, exact source expression
SITES = (
 ('byteLast', '(right : NodeId)', 'Dispatch.opAND', 'right', '(← c.constant 255 debug)',
  'classes.makeOperation(.AND, &.{ right, try classes.makeConstant(0xff, debug_data) }, debug_data,)'),
 ('modPower', '(left : NodeId) (modulus : Word)', 'Dispatch.opAND', 'left', '(← c.constant (← Dispatch.subWord modulus 1) debug)',
  'classes.makeOperation(.AND, &.{ left, try classes.makeConstant(modulus - 1, debug_data) }, debug_data,)'),
 ('maskedShift', '(instruction : Opcode) (left expression : NodeId)', 'instruction', 'left', 'expression',
  'classes.makeOperation(instruction, &.{ left, masked.expression }, debug_data,)'),
 ('shiftedMask', '(shifted : NodeId) (mask : Word)', 'Dispatch.opAND', 'shifted', '(← c.constant mask debug)',
  'classes.makeOperation(.AND, &.{ shifted, try classes.makeConstant(shifted_mask, debug_data) }, debug_data,)'),
 ('shiftedSignextend', '(amount index : Word) (shifted : NodeId)', 'Dispatch.opSIGNEXTEND', '(← c.constant (← Dispatch.addWord (amount >>> 3) index) debug)', 'shifted',
  'classes.makeOperation(.SIGNEXTEND, &.{ try classes.makeConstant((left_constant.? >> 3) + byte_index, debug_data), shifted }, debug_data,)'),
 ('subtractConstant', '(left : NodeId) (constant : Word)', 'Dispatch.opADD', 'left', '(← c.constant (0 - constant) debug)',
  'classes.makeOperation(.ADD, &.{ left, try classes.makeConstant(0 -% constant, debug_data) }, debug_data,)'),
 ('subtractLeftAdd', '(expression right : NodeId)', 'Dispatch.opSUB', 'expression', 'right',
  'classes.makeOperation(.SUB, &.{ parts.expression, right }, debug_data)'),
 ('addMaterializedDifference', '(difference original : NodeId) (value : Word)', 'Dispatch.opADD', 'difference', '(← c.materialize original value debug)',
  'classes.makeOperation(.ADD, &.{ difference, try classes.materializeConstant(parts.constant_expression, parts.value, debug_data) }, debug_data)'),
 ('subtractRightAdd', '(left expression : NodeId)', 'Dispatch.opSUB', 'left', 'expression',
  'classes.makeOperation(.SUB, &.{ left, parts.expression }, debug_data)'),
 ('addNegatedDifference', '(difference : NodeId) (value : Word)', 'Dispatch.opADD', 'difference', '(← c.constant (0 - value) debug)',
  'classes.makeOperation(.ADD, &.{ difference, try classes.makeConstant(0 -% parts.value, debug_data) }, debug_data,)'),
 ('addDifference', '(difference : NodeId) (constant : Word)', 'Dispatch.opADD', 'difference', '(← c.constant constant debug)',
  'classes.makeOperation(.ADD, &.{ difference, try classes.makeConstant(constant, debug_data) }, debug_data,)'),
 ('addNegatedSum', '(sum : NodeId) (constant : Word)', 'Dispatch.opADD', 'sum', '(← c.constant (0 - constant) debug)',
  'classes.makeOperation(.ADD, &.{ sum, try classes.makeConstant(0 -% constant, debug_data) }, debug_data,)'),
 ('maxParity', '(even parity : NodeId)', 'Dispatch.opSUB', 'even', 'parity',
  'classes.makeOperation(.SUB, &.{ even, parity }, debug_data)'),
 ('reassociateConstants', '(instruction : Opcode) (expression : NodeId) (value other : Word)', 'instruction', 'expression', '(← c.constant (← Nested.readAction (Associative.combineConstants instruction value other)) debug)',
  'classes.makeOperation(instruction, &.{ parts.expression, try classes.makeConstant(combineConstants(instruction, parts.value, other_constant), debug_data), }, debug_data,)'),
 ('reassociateRight', '(instruction : Opcode) (other expression : NodeId)', 'instruction', 'other', 'expression',
  'classes.makeOperation(instruction, &.{ other, parts.expression }, debug_data)'),
 ('reassociateLeft', '(instruction : Opcode) (expression other : NodeId)', 'instruction', 'expression', 'other',
  'classes.makeOperation(instruction, &.{ parts.expression, other }, debug_data)'),
 ('reassociateMaterialized', '(instruction : Opcode) (inner original : NodeId) (value : Word)', 'instruction', 'inner', '(← c.materialize original value debug)',
  'classes.makeOperation(instruction, &.{ inner, try classes.materializeConstant(parts.constant_expression, parts.value, debug_data) }, debug_data,)'),
 ('oppositeInner', '(opcode : Opcode) (inner outer : Word) (value : NodeId)', '(OppositeShifts.oppositeOpcode opcode)', '(← c.constant (← Nested.readAction (OppositeShifts.checkedDifference inner outer)) debug)', 'value',
  'classes.makeOperation(if (outer_instruction == .SHR) .SHL else .SHR, &.{ try classes.makeConstant(inner_shift - outer_shift, debug_data), value }, debug_data,)'),
 ('oppositeOuter', '(opcode : Opcode) (outer inner : Word) (value : NodeId)', 'opcode', '(← c.constant (← Nested.readAction (OppositeShifts.checkedDifference outer inner)) debug)', 'value',
  'classes.makeOperation(outer_instruction, &.{ try classes.makeConstant(outer_shift - inner_shift, debug_data), value }, debug_data,)'),
 ('oppositeMask', '(shifted : NodeId) (mask : Word)', 'Dispatch.opAND', 'shifted', '(← c.constant mask debug)',
  'classes.makeOperation(.AND, &.{ shifted, try classes.makeConstant(mask, debug_data) }, debug_data,)'),
 ('alternatingOr', '(left right : NodeId)', 'Dispatch.opOR', 'left', 'right',
  'classes.makeOperation(.OR, &.{ left, right }, debug_data)'),
)


def admitted(source, opcodes, storage, versions):
    owner.dispatch.extract(source, opcodes, storage, versions)
    calls = constructor_inventory.sites(source)
    selected = [call for call in calls if call['storage'] == 'temporary' and call['arity'] == 2
                and '[' not in lex(source[call['startByte']:call['endByte']].decode())]
    result = []
    for name, parameters, opcode, first, second, expression in SITES:
        matches = [call for call in selected if lex(source[call['startByte']:call['endByte']].decode()) == lex(expression)]
        if len(matches) != 1:
            raise Unsupported('scalar pair literal source binding changed: ' + name)
        result.append({**matches[0], 'site': name, 'parameters': parameters, 'opcode': opcode,
                       'first': first, 'second': second})
    if len(selected) != len(result) or len({call['startByte'] for call in result}) != len(result):
        raise Unsupported('scalar pair literal dependency closure changed')
    return result


def extract(source, opcodes, storage, versions):
    admitted(source, opcodes, storage, versions)
    hashes = ''.join('-- ' + name + ' SHA-256: ' + hashlib.sha256(value).hexdigest() + '\n'
        for name, value in zip(('Source', 'Opcodes', 'Expression classes', 'EVM versions'), (source, opcodes, storage, versions)))
    definitions = '\n\n'.join(
        f'def {name} (context : Context σ) {parameters}\n'
        '    (debug : AssemblyItem.Fields.Values) : GraphAction σ NodeId := do\n'
        '  let c := constructors context\n'
        f'  ConstructorPair.scalars c {opcode} {first} {second} debug'
        for name, parameters, opcode, first, second, _ in SITES)
    return ('''/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerPairInput

''' + hashes + '''
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.PairInput
open Compiler.Algebraic Compiler.Extraction.Cache Contract.Yul

/-- Source literal segments following their enclosing queries and guards.
These typed arguments are the source's evaluated scalar locals. Native query
correspondence and guard selection are separate recursive obligations. -/
''' + definitions + '''

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.PairInput
''').encode()


def check():
    values = owner.inputs()
    if extract(*values) != OUTPUT.read_bytes():
        raise ValueError('scalar pair input admission is stale; review and regenerate')
    if owner.dispatch.extract(*values) != owner.dispatch.OUTPUT.read_bytes():
        raise ValueError('shared dispatcher extraction is stale')
    helpers = (owner.dispatch.extract_associative, owner.dispatch.extract_opposite_shifts,
               owner.dispatch.extract_alternating_mask)
    for helper in helpers:
        if helper.extract(*values[:3]) != helper.OUTPUT.read_bytes():
            raise ValueError('shared pair helper extraction is stale: ' + helper.__name__)
    return {'sourceSha256': hashlib.sha256(values[0]).hexdigest(),
            'programSha256': hashlib.sha256(OUTPUT.read_bytes()).hexdigest(),
            'sharedPrograms': {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                               for path in (owner.dispatch.OUTPUT, *(helper.OUTPUT for helper in helpers))},
            'sites': admitted(*values), 'scope': 'all 21 scalar-only RuleList pair literal segments',
            'completeNativeQueryAndGuardConnectionVerified': False,
            'completeRecursiveConstructorsVerified': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    if parser.parse_args().check:
        check()
    else:
        OUTPUT.write_bytes(extract(*owner.inputs()))
