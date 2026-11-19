"""Source-bound scalar-view admission and corruption controls.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest

from test_expression_hash_air import fixture as caller_fixture, key_fixture
from test_zig_air_aggregate_generate import aggregate_fixture
from test_zig_air_generate import inst, ref, NEVER
from generate_hash_byte_views import render, pointer, PRODUCTION, CALLER


def fixture():
    caller = caller_fixture()
    key, sources, item_source = key_fixture()
    caller.update(name=CALLER, sourceFile=PRODUCTION, sourceSha256=sources[PRODUCTION], signature=key['signature'])
    sources['mem.zig'] = '2' * 64
    records = {}
    for field, position, bits, alignment in ((0, 7, 32, 4), (1, 11, 8, 1), (2, 15, 256, 16), (4, 24, 32, 4)):
        record = aggregate_fixture()
        selected, call, converted = caller['instructions'][position:position + 3]
        child = key['signature']['parameters'][1]['fields'][field]['type']
        source = pointer(child, bits // 8, alignment)
        byte = {'kind': 'int', 'bits': 8, 'signedness': 'unsigned'}
        array = {'kind': 'array', 'length': bits // 8, 'child': byte,
                 'layout': {'kind': 'abi', 'bytes': bits // 8, 'alignment': 1}, 'sentinel': None}
        result = pointer(array, bits // 8, 1, explicit=alignment if alignment > 1 else None)
        record.update(name=call['callee']['identity']['name'], sourceFile='mem.zig', sourceSha256=sources['mem.zig'])
        record['signature'] = {'callingConvention': {'auto': {}}, 'genericInstance': True,
                               'varArgs': False, 'noaliasBits': 0, 'parameters': [source], 'returnType': result}
        record['specialization'] = {'schema': 'oksolc.generic-instance.v1',
            'owner': {'name': 'mem.asBytes', 'sourceFile': 'mem.zig', 'sourceSha256': sources['mem.zig']},
            'sourceNoaliasBits': 0, 'sourceComptimeBits': 0, 'sourceParameterCount': 1,
            'arguments': [{'kind': 'runtime', 'runtimeIndex': 0}]}
        record['instructions'] = [inst(0, 'arg', source, zirParameterIndex=0),
            inst(1, 'ptr_cast', result, operand=ref(0)), inst(2, 'ret', NEVER, operand=ref(1))]
        record['body'] = [0, 1, 2]
        for name in ('configuration', 'schema', 'capturePoint', 'bodyTraversal'):
            caller[name] = copy.deepcopy(record[name])
        selected['type'], call['type'] = source, result
        converted['type'] = pointer(byte, 1, 1, slice=True)
        call['callee']['identity'] = {k: record[k] for k in ('name', 'sourceFile', 'sourceSha256')}
        records[record['name']] = record
    return copy.deepcopy((caller, records, sources, item_source))


class HashByteViewsTests(unittest.TestCase):
    def test_complete_scalar_bodies_keep_remaining_scope_explicit(self):
        args = fixture()
        original = copy.deepcopy(args)
        text, scope = render(*args)
        self.assertEqual([v['representationBits'] for v in scope['scalarViews']], [32, 8, 256, 32])
        self.assertTrue(all(v['calleeInstructions'] == 3 for v in scope['scalarViews']))
        self.assertEqual(text.count('ScalarBytesAir.viewCode'), 4)
        self.assertEqual(text.count('.scalarByteArray'), 4)
        self.assertFalse(scope['argumentSliceHelperTranslated'])
        self.assertFalse(scope['completeCallerTranslated'])
        self.assertFalse(scope['sourceAdapterFormallyVerified'])
        self.assertEqual(args, original)

    def test_caller_identity_operand_extent_and_permission_corruption_reject(self):
        edits = [
            lambda c: c.update(sourceSha256='3' * 64),
            lambda c: c['instructions'][7].update(fieldIndex=4),
            lambda c: c['instructions'][7]['operand'].update(index=1),
            lambda c: c['instructions'][8]['arguments'][0].update(index=3),
            lambda c: c['instructions'][9]['operand'].update(index=7),
            lambda c: c['instructions'][9]['type']['flags'].update(isConst=False),
            lambda c: c['instructions'][8]['type']['child'].update(length=8),
            lambda c: c['instructions'][8]['callee']['identity'].update(sourceSha256='3' * 64),
            lambda c: c['instructions'][8].update(unsupportedPayload=True),
            lambda c: c['body'].__setitem__(slice(7, 9), [8, 7]),
        ]
        for edit in edits:
            args = fixture()
            edit(args[0])
            with self.subTest(edit=edit), self.assertRaises(ValueError):
                render(*args)

    def test_specialization_alignment_and_complete_callee_corruption_reject(self):
        edits = [
            lambda r: r['specialization']['owner'].update(name='mem.other'),
            lambda r: r['specialization']['arguments'][0].update(runtimeIndex=1),
            lambda r: r['specialization'].update(sourceComptimeBits=1),
            lambda r: r['signature'].update(genericInstance=False),
            lambda r: r['signature']['returnType']['flags'].update(alignment=8),
            lambda r: r['instructions'][1]['operand'].update(index=1),
            lambda r: r['instructions'][2]['operand'].update(index=0),
            lambda r: r['instructions'][1].update(unsupportedPayload=True),
            lambda r: r['instructions'].append(copy.deepcopy(r['instructions'][2])),
            lambda r: r['body'].pop(),
            lambda r: r['configuration'].update(endianness='big'),
        ]
        for edit in edits:
            args = fixture()
            edit(next(iter(args[1].values())))
            with self.subTest(edit=edit), self.assertRaises(ValueError):
                render(*args)


if __name__ == '__main__':
    unittest.main()
