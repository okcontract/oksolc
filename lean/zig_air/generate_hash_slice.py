#!/usr/bin/env python3
"""Decode the complete captured u32 sliceAsBytes body and its caller cut.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Keep the empty constant, stack slots, both branches and source slice guard.
Reuse aggregate control, primitive memory and checked u32 byte access. Pointer
identity of anonymous empty storage is outside the admitted observations.
"""
import generate_aggregate as aggregate
import generate_memory as memory
from generate import fields
from generate_byte_memory import erase
from generate_hash_byte_views import CALLER, PRODUCTION, expect, pointer, require

WORD = {'kind': 'int', 'bits': 32, 'signedness': 'unsigned'}
BYTE = {'kind': 'int', 'bits': 8, 'signedness': 'unsigned'}
INPUT = pointer(WORD, 4, 4, slice=True)
OUTPUT = pointer(BYTE, 1, 1, explicit=4, slice=True)


class SliceViewDecoder(aggregate.Decoder):
    record_fields = aggregate.Decoder.record_fields + ' specialization'
    type_of = staticmethod(lambda record, depth=0: erase(memory.type_of(record, depth, byte_alignment=True)))

    def __init__(self, record, sources):
        expect({k: record[k] for k in ('sourceFile', 'sourceSha256')},
               {'sourceFile': 'mem.zig', 'sourceSha256': sources['mem.zig']}, 'slice-view source identity changed')
        expect(record['specialization'], {'schema': 'oksolc.generic-instance.v1',
            'owner': {'name': 'mem.sliceAsBytes', 'sourceFile': 'mem.zig', 'sourceSha256': sources['mem.zig']},
            'sourceNoaliasBits': 0, 'sourceComptimeBits': 0, 'sourceParameterCount': 1,
            'arguments': [{'kind': 'runtime', 'runtimeIndex': 0}]}, 'unreviewed sliceAsBytes specialization')
        require(record['name'].startswith('mem.sliceAsBytes__func_'), 'unexpected slice-view callee')
        self.empty_constants = 0
        super().__init__(record)

    def parameter_mapping(self, record):
        expect(record['signature'], {'callingConvention': {'auto': {}}, 'genericInstance': True,
            'varArgs': False, 'noaliasBits': 0, 'parameters': [INPUT], 'returnType': OUTPUT},
            'sliceAsBytes specialization signature changed')
        return [0]

    def read_validity(self, record):
        memory.Decoder.read_validity(self, record)
        require(len(self.guards) == 1, 'sliceAsBytes must retain its source slice guard')

    def before(self, index, env):
        return [(kind, register, ty, f'(.memory {prim})') for kind, register, ty, prim
                in memory.Decoder.before(self, index, env)]

    def finish(self):
        memory.Decoder.finish(self)
        require(self.empty_constants == 1, 'sliceAsBytes must retain its empty return')

    def constant(self, value):
        if not isinstance(value, dict) or value.get('kind') != 'emptySlice':
            return aggregate.constant(value)
        fields(value, 'kind type length origin')
        expect(value['type'], OUTPUT, 'empty slice changes result type or attributes')
        require(type(value['length']) is int and value['length'] == 0, 'empty slice has data')
        origin = value['origin']
        fields(origin, 'kind byteOffset objectType pointerType')
        require(origin['kind'] == 'unnamedConstant' and type(origin['byteOffset']) is int and
                origin['byteOffset'] == 0, 'empty slice lacks anonymous zero-offset storage')
        empty = {'kind': 'array', 'length': 0, 'child': BYTE,
                 'layout': {'kind': 'abi', 'bytes': 0, 'alignment': 1}, 'sentinel': None}
        expect(origin['objectType'], empty, 'empty slice origin is not a zero-byte array')
        expect(origin['pointerType'], pointer(empty, 0, 1), 'empty slice origin pointer changed')
        self.empty_constants += 1
        return ('slice', False, ('int', False, 8)), '(.constant .emptyBytes)'

    def extra_primitive(self, inst, ty, env):
        if inst['tag'] == 'ptr_cast':
            fields(inst, 'index tag payloadVisited type operand')
            source, operand = self.ref(inst['operand'], env)
            if source == ('ptr', False, True, ('int', False, 32)):
                expect(inst['type'], {**OUTPUT, 'flags': {**OUTPUT['flags'], 'size': 'many'},
                    'layout': {'kind': 'abi', 'bytes': 8, 'alignment': 8}}, 'word-to-byte pointer contract changed')
                return f'(.memory (.wordByteCast false true 4 {operand}))'
        return super().extra_primitive(inst, ty, env)


def render(caller, records, sources):
    require(caller['name'] == CALLER and caller['sourceFile'] == PRODUCTION and
            caller['sourceSha256'] == sources[PRODUCTION], 'unexpected slice-view caller')
    require(len(caller['body']) == 30, 'slice-view caller body changed')
    selected_ids = caller['body'][19:23]
    selected, loaded, called, converted = [caller['instructions'][index] for index in selected_ids]
    require(all(i['payloadVisited'] is True and not i.get('unsupportedPayload', False)
                for i in (selected, loaded, called, converted)), 'slice-view cut is incomplete')
    fields(selected, 'index tag payloadVisited type operand fieldIndex')
    fields(loaded, 'index tag payloadVisited type operand')
    fields(called, 'index tag payloadVisited type callee arguments')
    fields(converted, 'index tag payloadVisited type operand')
    field_reg, load_reg, call_reg, slice_reg = selected_ids
    expect(selected['tag'], 'struct_field_ptr_index_3', 'slice-view field operation changed')
    expect(selected['operand'], {'kind': 'instruction', 'index': 3}, 'slice-view key pointer changed')
    expect(selected['fieldIndex'], 3, 'slice-view field changed')
    expect(selected['type'], pointer(INPUT, 16, 8), 'slice-view field pointer changed')
    expect(loaded['tag'], 'load', 'slice-view field load changed')
    expect(loaded['operand'], {'kind': 'instruction', 'index': field_reg}, 'slice-view load operand changed')
    expect(loaded['type'], INPUT, 'slice-view argument type changed')
    require(called['tag'] == 'call' and called['callee']['kind'] == 'function', 'slice-view invocation changed')
    callee = records[called['callee']['identity']['name']]
    expect(called['callee']['identity'], {k: callee[k] for k in ('name', 'sourceFile', 'sourceSha256')},
           'slice-view body identity changed')
    for key in ('configuration', 'schema', 'capturePoint', 'bodyTraversal'):
        expect(callee[key], caller[key], 'slice-view capture configuration differs')
    expect(called['arguments'], [{'kind': 'instruction', 'index': load_reg}], 'slice-view argument changed')
    expect(called['type'], OUTPUT, 'slice-view result changed')
    expect(converted['tag'], 'ptr_cast', 'slice-view alignment conversion changed')
    expect(converted['operand'], {'kind': 'instruction', 'index': call_reg}, 'slice-view conversion operand changed')
    expect(converted['type'], pointer(BYTE, 1, 1, slice=True), 'slice-view weakened type changed')
    decoder = SliceViewDecoder(callee, sources)
    program = decoder.program(callee)
    slot = caller['signature']['parameters'][1]['fields'][3]
    require(slot['name'] == 'arguments' and slot['offset'] == 32, 'slice-view key layout changed')
    lines = ['/-', '// Copyright (C) 2026 OKcontract Pte. Ltd.', '// SPDX-License-Identifier: GPL-3.0',
        'Generated from complete captured sliceAsBytes AIR and its caller cut.',
        'Source/backend correspondence and complete caller execution remain open.', '-/',
        'import Compiler.ZigAir.AggregateCall', '', 'namespace Compiler.ZigAir.GeneratedExpressionHashSlice',
        'open Compiler.ZigAir.Memory', '', 'def arguments : AggregateAir.Program :=', program, '',
        'def argumentsView (next : AggregateCall.Code) : AggregateCall.Code :=',
        f'  .bind {field_reg} (.pointer false false (.slice false (.scalar (.int false 32))))',
        '    (.primitive (.fieldPointer (.local 3) 32))',
        f'    (.bind {load_reg} (.slice false (.scalar (.int false 32))) (.primitive (.load (.local {field_reg})))',
        f'      (.bind {call_reg} (.slice false (.scalar (.int false 8))) (.invoke arguments [(.local {load_reg})])',
        f'        (.bind {slice_reg} (.slice false (.scalar (.int false 8))) (.primitive (.copy (.local {call_reg}))) next)))',
        '', 'end Compiler.ZigAir.GeneratedExpressionHashSlice', '']
    return '\n'.join(lines), {'callee': callee['name'], 'selectedInstructions': selected_ids,
        'calleeInstructions': len(decoder.visited), 'sourceGuards': len(decoder.guards),
        'emptyReturns': decoder.empty_constants, 'argumentSliceHelperTranslated': True,
        'completeCallerTranslated': False, 'sourceAdapterFormallyVerified': False}
