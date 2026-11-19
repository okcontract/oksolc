"""Complete sliceAsBytes admission, stateful control and corruption checks.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest

from test_hash_byte_views import fixture as scalar_fixture
from test_zig_air_aggregate_generate import aggregate_fixture
from test_zig_air_generate import inst, ref, const, NEVER, VOID
from generate_hash_slice import render, pointer, WORD, BYTE, INPUT, OUTPUT


def fixture():
    caller, records, sources, _ = scalar_fixture()
    record = aggregate_fixture()
    name = 'mem.sliceAsBytes__func_4'
    record.update(name=name, sourceFile='mem.zig', sourceSha256=sources['mem.zig'])
    record['signature'] = {'callingConvention': {'auto': {}}, 'genericInstance': True,
        'varArgs': False, 'noaliasBits': 0, 'parameters': [INPUT], 'returnType': OUTPUT}
    record['specialization'] = {'schema': 'oksolc.generic-instance.v1',
        'owner': {'name': 'mem.sliceAsBytes', 'sourceFile': 'mem.zig', 'sourceSha256': sources['mem.zig']},
        'sourceNoaliasBits': 0, 'sourceComptimeBits': 0, 'sourceParameterCount': 1,
        'arguments': [{'kind': 'runtime', 'runtimeIndex': 0}]}
    size = {'kind': 'int', 'bits': 64, 'signedness': 'unsigned'}
    boolean = {'kind': 'bool'}
    word_pointer = pointer(WORD, 4, 4)
    word_pointer['flags']['size'] = 'many'
    byte_pointer = pointer(BYTE, 1, 1, explicit=4)
    byte_pointer['flags']['size'] = 'many'

    def mutable(ty):
        result = copy.deepcopy(ty)
        result['flags']['isConst'] = False
        return result

    empty = {'kind': 'array', 'length': 0, 'child': BYTE,
        'layout': {'kind': 'abi', 'bytes': 0, 'alignment': 1}, 'sentinel': None}
    empty_value = {'kind': 'emptySlice', 'type': OUTPUT, 'length': 0,
        'origin': {'kind': 'unnamedConstant', 'byteOffset': 0, 'objectType': empty,
                   'pointerType': pointer(empty, 0, 1)}}
    # Preserve the full structured body, including the two allocations and
    # dead instruction slots. This synthetic fixture is not capture evidence.
    instructions = [dict(index=i, tag='block', payloadVisited=False,
        unsupportedPayload=True, reason='outside-decoded-body-closure') for i in range(43)]
    active = [
        inst(0, 'arg', INPUT, zirParameterIndex=0),
        inst(1, 'alloc', mutable(pointer(INPUT, 16, 8)), allocationKind='stack'),
        inst(2, 'store', VOID, lhs=ref(1), rhs=ref(0)),
        inst(3, 'ptr_cast', pointer(INPUT, 16, 8), operand=ref(1)),
        inst(9, 'block', VOID, body=[10, 11, 12, 13, 14, 27]),
        inst(10, 'ptr_slice_len_ptr', pointer(size, 8, 8), operand=ref(3)),
        inst(11, 'load', size, operand=ref(10)),
        inst(12, 'bit_cast', size, operand=ref(11)),
        inst(13, 'cmp_eq', boolean, lhs=ref(12), rhs=const(0, size)),
        inst(14, 'block', boolean, body=[24]),
        inst(15, 'br', NEVER, target=14, operand=const(0, boolean)),
        inst(23, 'br', NEVER, target=14, operand=const(1, boolean)),
        inst(24, 'cond_br', NEVER, condition=ref(13), thenBody=[23], elseBody=[15]),
        inst(25, 'ret', NEVER, operand=empty_value),
        inst(26, 'br', NEVER, target=9, operand={'kind': 'unit'}),
        inst(27, 'cond_br', NEVER, condition=ref(14), thenBody=[25], elseBody=[26]),
        inst(30, 'slice_ptr', word_pointer, operand=ref(0)),
        inst(31, 'ptr_cast', byte_pointer, operand=ref(30)),
        inst(32, 'alloc', mutable(pointer(byte_pointer, 8, 8)), allocationKind='stack'),
        inst(33, 'store', VOID, lhs=ref(32), rhs=ref(31)),
        inst(34, 'ptr_cast', pointer(byte_pointer, 8, 8), operand=ref(32)),
        inst(35, 'ptr_slice_len_ptr', pointer(size, 8, 8), operand=ref(3)),
        inst(36, 'load', size, operand=ref(35)),
        inst(37, 'mul', size, lhs=ref(36), rhs=const(4, size)),
        inst(38, 'load', byte_pointer, operand=ref(34)),
        inst(39, 'ptr_add', byte_pointer, lhs=ref(38), rhs=const(0, size)),
        inst(40, 'sub', size, lhs=ref(37), rhs=const(0, size)),
        inst(41, 'slice', OUTPUT, lhs=ref(39), rhs=ref(40)),
        inst(42, 'ret', NEVER, operand=ref(41)),
    ]
    for item in active:
        instructions[item['index']] = item
    record['instructions'] = instructions
    record['body'] = [0, 1, 2, 3, 9, *range(30, 43)]
    record['sourceOperationTags'] = ['mul', 'slice_end', 'ret_node']
    record['sourceValidity']['slices'] = [{
        'source': {'file': 'mem.zig', 'sha256': sources['mem.zig'], 'span': {'start': 1, 'main': 2, 'end': 3}},
        'anchor': {'kind': 'beforeInstruction', 'index': 41, 'inSupportedBody': True},
        'start': const(0, size), 'end': ref(37),
        'upperBound': {'kind': 'unboundedPointer', 'requiresMemoryValidity': True},
        'unsupportedReason': None}]
    selected, loaded, called, converted = caller['instructions'][19:23]
    selected['type'], loaded['type'] = pointer(INPUT, 16, 8), INPUT
    called.update(type=OUTPUT, callee={'kind': 'function',
        'identity': {k: record[k] for k in ('name', 'sourceFile', 'sourceSha256')}})
    converted['type'] = pointer(BYTE, 1, 1, slice=True)
    records[name] = record
    return copy.deepcopy((caller, records, sources))


class HashSliceTests(unittest.TestCase):
    def test_complete_body_retains_branches_allocations_and_guard(self):
        args = fixture()
        before = copy.deepcopy(args)
        text, scope = render(*args)
        self.assertEqual(args, before)
        self.assertEqual(scope['calleeInstructions'], 29)
        self.assertEqual(scope['sourceGuards'], 1)
        self.assertEqual(scope['emptyReturns'], 1)
        self.assertEqual(text.count('(.memory (.alloc '), 2)
        for operation in ('.emptyBytes', '.wordByteCast false true 4', '.checkBounds',
                          '.arithmetic .mul .unchecked', '.arithmetic .sub .unchecked',
                          '.invoke arguments', '.primitive (.copy', '.branch (.local 14)'):
            self.assertIn(operation, text)
        self.assertTrue(scope['argumentSliceHelperTranslated'])
        self.assertFalse(scope['completeCallerTranslated'])
        self.assertFalse(scope['sourceAdapterFormallyVerified'])

    def test_empty_origin_cannot_hide_storage_or_pointer_capabilities(self):
        edits = [lambda v: v.update(length=1), lambda v: v.update(length=False),
            lambda v: v['origin'].update(kind='null'), lambda v: v['origin'].update(byteOffset=1),
            lambda v: v['origin']['objectType'].update(length=1),
            lambda v: v['origin']['objectType'].update(sentinel=const(0, BYTE)),
            lambda v: v['origin']['pointerType']['flags'].update(isConst=False),
            lambda v: v['origin']['pointerType']['flags'].update(alignment=4),
            lambda v: v['type']['flags'].update(alignment=8)]
        for index, edit in enumerate(edits):
            args = fixture()
            edit(args[1]['mem.sliceAsBytes__func_4']['instructions'][25]['operand'])
            with self.subTest(index=index), self.assertRaises(ValueError):
                render(*args)

    def test_body_type_specialization_and_source_obligations_fail_closed(self):
        edits = [lambda r: r['sourceValidity']['slices'].clear(),
            lambda r: r['sourceValidity']['slices'][0]['source'].update(sha256='3' * 64),
            lambda r: r['sourceValidity']['slices'][0]['anchor'].update(index=42),
            lambda r: r['sourceValidity']['slices'][0]['upperBound'].update(requiresMemoryValidity=False),
            lambda r: r['specialization']['owner'].update(name='mem.other'),
            lambda r: r['specialization']['arguments'][0].update(runtimeIndex=1),
            lambda r: r['signature'].update(genericInstance=False),
            lambda r: r['configuration'].update(endianness='big'),
            lambda r: r['instructions'][31]['type']['flags'].update(alignment=8),
            lambda r: r['instructions'][32].update(allocationKind='heap'),
            lambda r: r['instructions'][31].update(unsupportedPayload=True),
            lambda r: r['body'].remove(33), lambda r: r['body'].pop(),
            lambda r: r['instructions'][27].update(thenBody=[26]),
            lambda r: r['instructions'][42].update(operand=ref(25))]
        for index, edit in enumerate(edits):
            args = fixture()
            edit(args[1]['mem.sliceAsBytes__func_4'])
            with self.subTest(index=index), self.assertRaises(ValueError):
                render(*args)

    def test_caller_cut_cannot_change_identity_layout_or_data_flow(self):
        edits = [lambda c: c.update(sourceSha256='3' * 64),
            lambda c: c['instructions'][19].update(fieldIndex=4),
            lambda c: c['instructions'][20]['operand'].update(index=3),
            lambda c: c['instructions'][21]['arguments'][0].update(index=19),
            lambda c: c['instructions'][21]['callee']['identity'].update(sourceSha256='3' * 64),
            lambda c: c['instructions'][22]['operand'].update(index=20),
            lambda c: c['instructions'][22]['type']['flags'].update(isConst=False),
            lambda c: c['signature']['parameters'][1]['fields'][3].update(offset=40)]
        for index, edit in enumerate(edits):
            args = fixture()
            edit(args[0])
            with self.subTest(index=index), self.assertRaises(ValueError):
                render(*args)

    def test_semantic_changes_cannot_match_the_accepted_program(self):
        original, _ = render(*fixture())
        edits = [lambda r: r['instructions'][37]['rhs'].update(value=8),
            lambda r: r['instructions'][13].update(tag='cmp_neq'),
            lambda r: r['instructions'][39]['rhs'].update(value=4),
            lambda r: r['instructions'][40]['rhs'].update(value=1),
            lambda r: r['sourceValidity']['slices'][0]['end'].update(index=36)]
        for index, edit in enumerate(edits):
            args = fixture()
            edit(args[1]['mem.sliceAsBytes__func_4'])
            with self.subTest(index=index):
                self.assertNotEqual(render(*args)[0], original)


if __name__ == '__main__':
    unittest.main()
