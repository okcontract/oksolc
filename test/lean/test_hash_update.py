"""Complete-body decoding controls for the captured update profile.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest

from test_zig_air_generate import fixture, inst, ref, const, U8, VOID, NEVER
from test_zig_air_aggregate_generate import aggregate_fixture
from check_zig_air_memory import pointer, layout, uint
from generate_hash_update import render, UpdateDecoder
from generate_memory import Decoder as MemoryDecoder

BOOL = {'kind': 'bool'}


def records():
    assertion = fixture()
    assertion.update(name='debug.assert', sourceFile='debug.zig', sourceSha256='b' * 64)
    assertion['configuration'].update(arch='aarch64', os='macos', pointerBits=64, endianness='little')
    assertion['signature'].update(parameters=[BOOL], returnType=VOID)
    assertion['instructions'] = [inst(0, 'arg', BOOL, zirParameterIndex=0),
        inst(1, 'not', BOOL, operand=ref(0)),
        inst(2, 'cond_br', NEVER, condition=ref(1), thenBody=[3], elseBody=[4]),
        inst(3, 'unreach', NEVER), inst(4, 'ret', NEVER, operand={'kind': 'unit'})]
    assertion['body'] = [0, 1, 2]
    record = aggregate_fixture()
    record.update(name='hash.wyhash.Wyhash.update', sourceFile='hash/wyhash.zig')
    owner = record['signature']['returnType']
    owner['identity'].update(name='hash.wyhash.Wyhash', sourceFile=record['sourceFile'])
    receiver = pointer(owner, owner['layout'])
    view = pointer(U8, layout(1, 1), size='slice', const=True)
    many = pointer(U8, layout(1, 1), size='many', const=True)
    array = {'kind': 'array', 'length': 8, 'child': U8, 'layout': layout(8, 1), 'sentinel': None}
    record['signature'].update(parameters=[receiver, view], returnType=VOID)
    record['instructions'] = [inst(0, 'arg', receiver, zirParameterIndex=0),
        inst(1, 'arg', view, zirParameterIndex=1),
        inst(2, 'add', uint(64), lhs=const(0, uint(64)), rhs=const(8, uint(64))),
        inst(3, 'slice_ptr', many, operand=ref(1)),
        inst(4, 'ptr_cast', pointer(array, layout(8, 1), const=True), operand=ref(3)),
        inst(5, 'load', array, operand=ref(4)),
        inst(6, 'bit_cast', uint(64), operand=ref(5)),
        inst(7, 'alloc', pointer(array, layout(8, 1)), allocationKind='stack'),
        inst(8, 'memcpy', VOID, lhs=ref(7), rhs=ref(3)),
        inst(9, 'array_to_slice', pointer(U8, layout(1, 1), size='slice'), operand=ref(7)),
        inst(10, 'call', VOID, callee={'kind': 'function', 'identity':
            {k: assertion[k] for k in ('name', 'sourceFile', 'sourceSha256')}}, arguments=[const(1, BOOL)]),
        inst(11, 'ret', NEVER, operand={'kind': 'unit'})]
    record['body'] = list(range(12))
    record['sourceOperationTags'] = ['slice_length']
    record['sourceValidity']['slices'] = [{
        'source': {'file': record['sourceFile'], 'sha256': record['sourceSha256'],
                   'span': {'start': 0, 'main': 1, 'end': 2}},
        'anchor': {'kind': 'beforeInstruction', 'index': 4, 'inSupportedBody': True},
        'start': const(0, uint(64)), 'end': ref(2),
        'upperBound': {'kind': 'sliceLength', 'original': ref(1)}, 'unsupportedReason': None}]
    return copy.deepcopy((record, assertion))


class HashUpdateTests(unittest.TestCase):
    def test_byte_access_copy_guard_and_assert_callee_are_retained(self):
        args = records()
        original = copy.deepcopy(args)
        text, scope = render(*args)
        self.assertEqual(args, original)
        self.assertEqual(scope, {'instructions': 12, 'sourceGuards': 1, 'loops': [], 'assertInstructions': 5})
        for token in ('.loadBytes', '.bytesToWord', '.copyBytes', '.arrayToSlice', '.booleanNot',
                      '.unreachable', '.invoke assertion', '.arithmetic .add .unchecked', '.checkBounds'):
            self.assertIn(token, text)
        self.assertLess(text.index('.arithmetic .add .unchecked'), text.index('.checkBounds'))
        self.assertLess(text.index('.checkBounds'), text.index('.loadBytes'))
        with self.assertRaisesRegex(ValueError, 'length-based slice'):
            MemoryDecoder(args[0]).program(args[0])

    def test_unsupported_operands_and_incomplete_bodies_reject(self):
        edits = [lambda r: r['instructions'][8].update(lhs=ref(3)),
                 lambda r: r['instructions'][8].update(rhs=ref(0)),
                 lambda r: r['instructions'][6].update(type=uint(32)),
                 lambda r: r['instructions'][5].update(operand=ref(7)),
                 lambda r: r['instructions'][10].update(arguments=[const(1)]),
                 lambda r: r['instructions'][10]['callee']['identity'].update(sourceSha256='c' * 64),
                 lambda r: r['body'].remove(8),
                 lambda r: r['instructions'][8].update(unsupportedPayload=True),
                 lambda r: r['signature'].update(parameters=[])]
        for edit in edits:
            args = records()
            edit(args[0])
            with self.subTest(edit=edit), self.assertRaises(ValueError):
                render(*args)

    def test_assert_terminator_and_source_guard_cannot_disappear(self):
        edits = [lambda r, a: a['instructions'][2].update(thenBody=[]),
                 lambda r, a: a['instructions'][3].update(type=VOID),
                 lambda r, a: a['instructions'][1].update(operand=const(1)),
                 lambda r, a: a['instructions'][3].update(operand=const(1)),
                 lambda r, a: a['body'].append(4),
                 lambda r, a: r['sourceValidity']['slices'][0].update(end=ref(5)),
                 lambda r, a: r['sourceValidity']['slices'][0]['source'].update(sha256='c' * 64),
                 lambda r, a: r['sourceValidity']['slices'][0].update(unsupportedReason='sentinel')]
        for edit in edits:
            args = records()
            edit(*args)
            with self.subTest(edit=edit), self.assertRaises(ValueError):
                render(*args)

    def test_larger_instruction_limit_stays_scoped_and_bounded(self):
        record, assertion = records()
        for i in range(len(record['instructions']), 600):
            record['instructions'].append({'index': i, 'tag': 'unused', 'payloadVisited': False,
                'unsupportedPayload': True, 'reason': 'outside-decoded-body-closure'})
        self.assertIn('.copyBytes', UpdateDecoder(record, assertion).program(record))
        record['instructions'] += record['instructions']
        with self.assertRaisesRegex(ValueError, 'instruction resource limit'):
            UpdateDecoder(record, assertion)


if __name__ == '__main__':
    unittest.main()
