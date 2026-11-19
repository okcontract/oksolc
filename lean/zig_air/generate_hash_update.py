#!/usr/bin/env python3
"""Decode the complete captured Wyhash update and its finite assert callee.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Keep every supported-body instruction, source-slice guard and loop back edge.
The length-slice profile retains start+length arithmetic and its overflow fault
as well as the resulting bounds check. No call or dead-result access is erased.
Decoding does not establish update preservation or source/backend refinement.
"""
import generate as scalar
import generate_aggregate as aggregate
import generate_memory as memory
from generate import fields
from generate_hash_byte_views import expect, require

BYTE = ('int', False, 8)
WORD = ('int', False, 64)


class AssertDecoder(aggregate.Decoder):
    def extra_primitive(self, inst, ty, env):
        if inst['tag'] == 'not':
            fields(inst, 'index tag payloadVisited type operand')
            source, operand = self.ref(inst['operand'], env)
            require(source == ty == ('bool',), 'assert not must be boolean')
            return f'(.booleanNot {operand})'
        return super().extra_primitive(inst, ty, env)

    def extra_terminator(self, inst, ty, env):
        if inst['tag'] != 'unreach':
            return None
        fields(inst, 'index tag payloadVisited type')
        require(ty == ('noreturn',), 'unreachable has a result')
        # The unreachable primitive faults before the synthetic continuation.
        return (f"(.bind {inst['index']} (.scalar .unit) .unreachable "
                '(.ret (.constant (.value (.scalar .unit)))))')


class UpdateDecoder(aggregate.Decoder):
    allow_loops = True
    allow_length_slices = True
    instruction_limit = 1024

    def __init__(self, record, assertion):
        self.assertion = assertion
        super().__init__(record)
        require(len(self.parameters) == 2 and self.parameters[0][:3] == ('ptr', True, False) and
                self.parameters[1] == ('slice', False, BYTE) and self.result == ('void',),
                'update signature changed')
        require(self.parameters[0][3][0] == 'struct' and
                self.parameters[0][3][1] == (record['name'].removesuffix('.update'),
                                            record['sourceFile'], record['sourceSha256']),
                'update receiver identity changed')

    def read_validity(self, record):
        memory.Decoder.read_validity(self, record)

    def before(self, index, env):
        return [(kind, register, ty, f'(.primitive (.memory {prim}))')
                for kind, register, ty, prim in memory.Decoder.before(self, index, env)]

    def finish(self):
        memory.Decoder.finish(self)

    def scalar_primitive(self, text):
        return f'(.primitive (.memory (.scalar {text})))'

    def argument_primitive(self, index):
        return f'(.primitive (.argument {index}))'

    def extra_primitive(self, inst, ty, env):
        tag, base = inst['tag'], 'index tag payloadVisited type '
        if tag == 'memcpy':
            fields(inst, base + 'lhs rhs')
            target, left = self.ref(inst['lhs'], env)
            source, right = self.ref(inst['rhs'], env)
            dest = (target == ('slice', True, BYTE) or
                    (target[:3] == ('ptr', True, False) and target[3][0] == 'array' and target[3][2] == BYTE))
            src = (source == ('ptr', False, True, BYTE) or source == ('ptr', True, True, BYTE) or
                   (source[0] == 'ptr' and not source[2] and source[3][0] == 'array' and source[3][2] == BYTE))
            require(dest and src and ty == ('void',), 'unsupported memcpy operands')
            return f'(.copyBytes {left} {right})'
        if tag == 'call':
            fields(inst, base + 'callee arguments')
            fields(inst['callee'], 'kind identity')
            require(inst['callee']['kind'] == 'function', 'update call is not direct')
            expect(inst['callee']['identity'], {k: self.assertion[k]
                   for k in ('name', 'sourceFile', 'sourceSha256')}, 'update callee identity changed')
            require(isinstance(inst['arguments'], list) and len(inst['arguments']) == 1 and ty == ('void',),
                    'assert call shape changed')
            arg_type, arg = self.ref(inst['arguments'][0], env)
            require(arg_type == ('bool',), 'assert argument is not boolean')
            return f'(.invoke assertion [{arg}])'
        if tag == 'load' and ty[0] == 'array':
            fields(inst, base + 'operand')
            source, operand = self.ref(inst['operand'], env)
            require(ty == ('array', 8, BYTE) and source[0] == 'ptr' and not source[2] and source[3] == ty,
                    'unsupported byte-array load')
            return f'(.primitive (.loadBytes {operand}))'
        if tag == 'bit_cast':
            fields(inst, base + 'operand')
            source, operand = self.ref(inst['operand'], env)
            if source[0] == 'array':
                require(source == ('array', 8, BYTE) and ty == WORD, 'byte-array bitcast changed width')
                return f'(.primitive (.bytesToWord {operand}))'
        if tag == 'array_to_slice':
            fields(inst, base + 'operand')
            source, operand = self.ref(inst['operand'], env)
            require(source[0] == 'ptr' and not source[2] and source[3][0] == 'array' and
                    ty == ('slice', source[1], source[3][2]), 'array-to-slice changes type')
            return f'(.primitive (.arrayToSlice {operand}))'
        prim = super().extra_primitive(inst, ty, env)
        return None if prim is None else f'(.primitive {prim})'


def render(record, assertion):
    require(record['name'] == 'hash.wyhash.Wyhash.update' and record['sourceFile'] == 'hash/wyhash.zig',
            'unexpected update body')
    require(assertion['name'] == 'debug.assert' and assertion['sourceFile'] == 'debug.zig',
            'unexpected assertion body')
    expect(record['configuration'], assertion['configuration'], 'callee capture configuration differs')
    check = AssertDecoder(assertion)
    require(check.parameters == [('bool',)] and check.result == ('void',), 'assert signature changed')
    assertion_program = check.program(assertion)
    decoder = UpdateDecoder(record, assertion)
    update = decoder.program(record)
    lines = ['/-', '// Copyright (C) 2026 OKcontract Pte. Ltd.', '// SPDX-License-Identifier: GPL-3.0',
             'Generated from complete captured Wyhash update and debug.assert AIR.',
             'Update preservation and source/backend correspondence remain open.', '-/',
             'import Compiler.ZigAir.AggregateExecution', '',
             'set_option maxRecDepth 4096', '', 'namespace Compiler.ZigAir.GeneratedWyhashUpdate',
             '', 'def assertion : AggregateAir.Program :=', assertion_program, '',
             'def update : AggregateCall.Program :=', update, '',
             'end Compiler.ZigAir.GeneratedWyhashUpdate', '']
    return '\n'.join(lines), {'instructions': len(decoder.visited), 'sourceGuards': len(decoder.guards_seen),
                             'loops': sorted(decoder.loop_ids), 'assertInstructions': len(check.visited)}
