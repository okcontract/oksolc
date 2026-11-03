#!/usr/bin/env python3
"""Bind the four EVM shift literals to their ordered native input execution.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
import constructor_inventory
import extract_rule_unary as owner
from extract_compiler import ROOT, Unsupported
from extract_storage import lex

OUTPUT = ROOT / 'lean/Compiler/Extraction/RuleShiftInputProgram.lean'
# Source expressions are matched only after complete owner admission. Each
# borrowed expression remains an action, at its position relative to the child.
SITES = (
    ('exponentTwo', 'SHL', False, 1, '1',
     'classes.makeOperation(.SHL, &.{ arguments[1], try classes.makeConstant(1, debug_data) }, debug_data,)'),
    ('multiplyLeft', 'SHL', True, 1, '(BitVec.ofNat 256 power)',
     'classes.makeOperation(.SHL, &.{ try classes.makeConstant(power, debug_data), arguments[1] }, debug_data,)'),
    ('multiplyRight', 'SHL', True, 0, '(BitVec.ofNat 256 power)',
     'classes.makeOperation(.SHL, &.{ try classes.makeConstant(power, debug_data), arguments[0] }, debug_data,)'),
    ('divide', 'SHR', True, 0, '(BitVec.ofNat 256 power)',
     'classes.makeOperation(.SHR, &.{ try classes.makeConstant(power, debug_data), arguments[0] }, debug_data,)'),
)


def admitted(source, opcodes, storage, versions):
    owner.dispatch.extract(source, opcodes, storage, versions)
    calls = constructor_inventory.sites(source, {'simplifyWithOptions'})
    result = []
    for name, opcode, first, index, value, expression in SITES:
        matches = [call for call in calls if lex(source[call['startByte']:call['endByte']].decode()) == lex(expression)]
        if len(matches) != 1 or matches[0]['arity'] != 2 or len(matches[0]['children']) != 1:
            raise Unsupported('shift literal source binding changed: ' + name)
        result.append({**matches[0], 'site': name, 'opcode': opcode, 'constantFirst': first, 'operandIndex': index})
    return result


def extract(source, opcodes, storage, versions):
    admitted(source, opcodes, storage, versions)
    hashes = ''.join('-- ' + name + ' SHA-256: ' + hashlib.sha256(value).hexdigest() + '\n'
        for name, value in zip(('Source', 'Opcodes', 'Expression classes', 'EVM versions'), (source, opcodes, storage, versions)))
    arms = '\n'.join(f'  | .{name} => run context {str(first).lower()} Dispatch.op{opcode} {value} source {index} debug'
        for name, opcode, first, index, value, _ in SITES)
    return ('''/-
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
-/
import Compiler.Extraction.InternerShiftInput

''' + hashes + '''
namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ShiftInput
open Contract.Yul

inductive Site where
  | exponentTwo | multiplyLeft | multiplyRight | divide
  deriving DecidableEq, Repr

/-- The selected source segment, after its enclosing queries and guards.
`power` is the already evaluated local binary-logarithm result; the argument
element itself is loaded from native memory at its source evaluation position. -/
def zigLiteral (context : Context σ) (site : Site) (power : Nat)
    (source : Compiler.ZigAir.Memory.WordArray.View) (debug : AssemblyItem.Fields.Values) : GraphAction σ Compiler.Algebraic.NodeId :=
  match site with
''' + arms + '''

end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.ConstructorItem.ShiftInput
''').encode()


def check():
    values = owner.inputs()
    if extract(*values) != OUTPUT.read_bytes():
        raise ValueError('shift literal input admission is stale; review and regenerate')
    if owner.dispatch.extract(*values) != owner.dispatch.OUTPUT.read_bytes():
        raise ValueError('shared dispatcher extraction is stale')
    return {'sourceSha256': hashlib.sha256(values[0]).hexdigest(),
            'programSha256': hashlib.sha256(OUTPUT.read_bytes()).hexdigest(),
            'dispatcherSha256': hashlib.sha256(owner.dispatch.OUTPUT.read_bytes()).hexdigest(),
            'sites': admitted(*values), 'scope': 'four shift-literal segments following their enclosing guards',
            'completeNativeQueryAndGuardConnectionVerified': False,
            'completeRecursiveConstructorsVerified': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    if parser.parse_args().check:
        check()
    else:
        OUTPUT.write_bytes(extract(*owner.inputs()))
