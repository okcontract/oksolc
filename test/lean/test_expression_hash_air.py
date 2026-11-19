#!/usr/bin/env python3
"""Reject caller-order corruption without promoting capture into a proof.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import hashlib
import unittest

import check_expression_hash_air as gate
from check_zig_air_memory import layout, pointer, uint


def key_fixture():
    item_source = b'pub const AssemblyItemType = enum(c_int) { UndefinedItem, Operation, };'
    sources = {gate.PRODUCTION: '1' * 64,
               'src/libevmasm/assembly_item.zig': hashlib.sha256(item_source).hexdigest()}
    tag = {'kind': 'enum', 'identity': {'name': 'src.' + gate.key_layout.FIELDS['item_type'][0],
            'sourceFile': 'src/libevmasm/assembly_item.zig',
            'sourceSha256': sources['src/libevmasm/assembly_item.zig']},
           'backingType': {'kind': 'int', 'bits': 32, 'signedness': 'signed'},
           'layout': layout(4, 4), 'nonexhaustive': False,
           'fields': [{'index': i, 'name': name, 'value': i}
                      for i, name in enumerate(('UndefinedItem', 'Operation'))]}
    types = (tag, uint(8), uint(256), pointer(uint(32), layout(4, 4), size='slice', const=True), uint(32))
    key = {'kind': 'struct', 'identity': {'name': 'src.' + gate.key_layout.KEY,
             'sourceFile': gate.PRODUCTION, 'sourceSha256': sources[gate.PRODUCTION]},
           'containerLayout': 'auto', 'layout': layout(64, 16),
           'fields': [{'index': i, 'name': name, 'offset': offset, 'explicitAlignment': None, 'type': ty}
                      for i, (name, offset, ty) in enumerate(zip(gate.key_layout.FIELDS, (48, 56, 0, 32, 52), types))]}
    return {'signature': {'parameters': [None, key]}}, sources, item_source


def fixture():
    instructions = []

    def add(tag, **fields):
        inst = {'index': len(instructions), 'tag': tag, 'payloadVisited': True, **fields}
        instructions.append(inst)
        return inst

    def call(name, arguments):
        return add('call', callee={'kind': 'function', 'identity': {'name': name}}, arguments=arguments)

    key = add('arg', zirParameterIndex=1)
    stored = add('alloc', allocationKind='stack')
    add('store', lhs=gate.ref(stored), rhs=gate.ref(key))
    key_pointer = add('ptr_cast', operand=gate.ref(stored))
    hasher = add('alloc', allocationKind='stack')
    initialized = call(gate.WYHASH + 'init', [{'kind': 'constant',
        'type': {'kind': 'int', 'bits': 64, 'signedness': 'unsigned'}, 'value': 0}])
    add('store', lhs=gate.ref(hasher), rhs=gate.ref(initialized))
    for field in range(5):
        pointer = add('struct_field_ptr_index_' + str(field) if field < 4 else 'struct_field_ptr',
                      operand=gate.ref(key_pointer), fieldIndex=field)
        if field == 3:
            value = add('load', operand=gate.ref(pointer))
            view = call('mem.sliceAsBytes__func_4', [gate.ref(value)])
            converted = add('ptr_cast', operand=gate.ref(view))
        else:
            view = call('mem.asBytes__func_' + str(field + 1), [gate.ref(pointer)])
            converted = add('array_to_slice', operand=gate.ref(view))
        call(gate.WYHASH + 'update', [gate.ref(hasher), gate.ref(converted)])
    finished = call(gate.WYHASH + 'final', [gate.ref(hasher)])
    add('ret', operand=gate.ref(finished))
    return {'instructions': instructions, 'body': list(range(len(instructions)))}


class ExpressionHashAirTests(unittest.TestCase):
    def test_captured_key_reuses_existing_complete_layout(self):
        record, sources, source = key_fixture()
        before = copy.deepcopy(record)
        result = gate.caller_key_layout(record, sources, source)
        self.assertEqual(record, before)
        self.assertEqual(result['existingKeyLayoutSha256'], gate.digest(gate.key_layout.KEY_OUTPUT))
        self.assertEqual(result['enumFields'], 2)
        self.assertFalse(result['enumSemanticsVerified'])

    def test_key_identity_representation_and_field_corruption_reject(self):
        edits = [
            lambda k: k['identity'].update(name='other.ExpressionKey'),
            lambda k: k['identity'].update(sourceSha256='2' * 64),
            lambda k: k['layout'].update(bytes=63),
            lambda k: k['fields'].pop(),
            lambda k: k['fields'][0].update(index=False),
            lambda k: k['fields'][0].update(offset=52),
            lambda k: k['fields'][1]['type'].update(bits=32),
            lambda k: k['fields'][3]['type']['flags'].update(isConst=False),
            lambda k: k['fields'][0]['type']['identity'].update(sourceSha256='2' * 64),
            lambda k: k['fields'][0]['type']['backingType'].update(signedness='unsigned'),
            lambda k: k['fields'][0]['type']['layout'].update(alignment=1),
            lambda k: k['fields'][0]['type'].update(nonexhaustive=True),
            lambda k: k['fields'][0]['type']['fields'][0].update(value=False),
            lambda k: k['fields'][0]['type']['fields'][1].update(value=7),
            lambda k: k['fields'][0]['type']['fields'][1].update(name='Renamed'),
        ]
        for index, edit in enumerate(edits):
            with self.subTest(index=index), self.assertRaises(ValueError):
                record, sources, source = key_fixture()
                edit(record['signature']['parameters'][1])
                gate.caller_key_layout(record, sources, source)

    def test_complete_order_keeps_unproved_views_explicit(self):
        record = fixture()
        before = copy.deepcopy(record)
        result = gate.caller_order(record)
        self.assertEqual(record, before)
        self.assertLess(result['hasherAllocation'], result['initializerCall'])
        self.assertLess(result['initializerCall'], result['initializerStore'])
        self.assertEqual([view['fieldIndex'] for view in result['byteViews']], list(range(5)))
        self.assertEqual(len(result['updateCalls']), 5)
        self.assertFalse(result['byteViewSemanticsVerified'])
        self.assertFalse(result['callerExecutionVerified'])

    def test_materialization_seed_updates_and_return_corruption_reject(self):
        edits = [
            lambda r: r['body'].__setitem__(slice(4, 6), [5, 4]),
            lambda r: r['instructions'][4].update(allocationKind='heap'),
            lambda r: r['instructions'][5]['arguments'][0].update(value=1),
            lambda r: r['instructions'][6].update(lhs={'kind': 'instruction', 'index': 1}),
            lambda r: r['instructions'][7].update(fieldIndex=1),
            lambda r: r['instructions'][10]['arguments'].__setitem__(0, {'kind': 'instruction', 'index': 1}),
            lambda r: r['instructions'][10]['arguments'].__setitem__(1, {'kind': 'instruction', 'index': 8}),
            lambda r: r['instructions'][28]['callee']['identity'].update(name=gate.WYHASH + 'update'),
            lambda r: r['instructions'][29].update(operand={'kind': 'instruction', 'index': 5}),
            lambda r: r['instructions'][10].update(payloadVisited=False),
            lambda r: r['instructions'][9].update(operand={'kind': 'instruction', 'index': 7}),
            lambda r: r['instructions'][9].pop('operand'),
            lambda r: r['instructions'][9].update(unsupportedPayload=True),
        ]
        for index, edit in enumerate(edits):
            with self.subTest(index=index), self.assertRaises(ValueError):
                record = fixture()
                edit(record)
                gate.caller_order(record)

    def test_indirect_and_nonordinary_call_reject(self):
        for call in ({'tag': 'call', 'callee': {'kind': 'unsupported'}},
                     {'tag': 'call_never_tail', 'callee': {'kind': 'function', 'identity': {'name': 'f'}}}):
            with self.subTest(call=call), self.assertRaises(ValueError):
                gate.target(call)

    def test_safe_modes_retain_safe_store_and_return(self):
        for mode in ('Debug', 'ReleaseSafe'):
            record = fixture()
            with self.assertRaises(ValueError):
                gate.caller_order(record, mode)
            record['instructions'][2]['tag'] = 'store_safe'
            record['instructions'][29]['tag'] = 'ret_safe'
            self.assertFalse(gate.caller_order(record, mode)['callerExecutionVerified'])


if __name__ == '__main__':
    unittest.main()
