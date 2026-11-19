#!/usr/bin/env python3
"""Bind hash scalar byte views to concrete captured AIR programs.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Enum metadata is mapped only to its existing 32-bit storage representation;
no enum operations or complete hash-caller execution are admitted here.
"""
import json
import re

from build_toolchain import digest
from generate import fields
from generate_memory import type_of, layout
from generate_aggregate import Decoder as AggregateDecoder
from extract_storage import function
import generate_map_bucket_layout as key_layout

PRODUCTION = 'src/libevmasm/expression_classes.zig'
CALLER = 'src.libevmasm.expression_classes.ExpressionKeyContext.hash'


def require(value, message):
    if not value:
        raise ValueError(message)


def expect(actual, expected, message):
    require(json.dumps(actual, sort_keys=True) == json.dumps(expected, sort_keys=True), message)


def caller_key_layout(record, sources, item_source):
    """Bind captured enum/struct metadata to the existing complete key model.

    Enum representations are inspected here, not admitted to the AIR interpreter.
    The source-bound c_int tag is encoded by its existing 32-bit storage model.
    """
    key = record['signature']['parameters'][1]
    fields(key, 'kind identity containerLayout layout fields')
    expected_identity = {'name': 'src.' + key_layout.KEY, 'sourceFile': PRODUCTION,
                         'sourceSha256': sources[PRODUCTION]}
    require(key['kind'] == 'struct' and key['identity'] == expected_identity and key['containerLayout'] == 'auto',
            'captured key identity changed')
    require(json.dumps(key['layout'], sort_keys=True) == json.dumps({'kind': 'abi', 'bytes': 64, 'alignment': 16}, sort_keys=True),
            'captured key layout changed')
    require(len(key['fields']) == len(key_layout.FIELDS), 'incomplete captured key fields')
    native, tags = [], []
    for index, (field, name) in enumerate(zip(key['fields'], key_layout.FIELDS)):
        fields(field, 'index name offset explicitAlignment type')
        require(type(field['index']) is int and field['index'] == index and field['name'] == name and
                field['explicitAlignment'] is None, 'captured key field identity changed')
        ty = field['type']
        native_name, _, _, _ = key_layout.FIELDS[name]
        if name == 'item_type':
            fields(ty, 'kind identity backingType layout nonexhaustive fields')
            require(ty['kind'] == 'enum' and ty['identity'] == {'name': 'src.' + native_name,
                'sourceFile': 'src/libevmasm/assembly_item.zig', 'sourceSha256': sources['src/libevmasm/assembly_item.zig']} and
                ty['nonexhaustive'] is False and type_of(ty['backingType']) == ('int', True, 32), 'captured item enum changed')
            require(json.dumps(ty['layout'], sort_keys=True) == json.dumps({'kind': 'abi', 'bytes': 4, 'alignment': 4}, sort_keys=True),
                    'captured enum layout changed')
            require(isinstance(ty['fields'], list) and 0 < len(ty['fields']) <= 64, 'incomplete enum fields')
            for i, tag in enumerate(ty['fields']):
                fields(tag, 'index name value')
                require(type(tag['index']) is int and tag['index'] == i and type(tag['value']) is int and tag['value'] == i and
                        isinstance(tag['name'], str) and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', tag['name']), 'enum ordinal changed')
                tags.append(tag['name'])
            function(item_source, 'pub const AssemblyItemType = enum(c_int)').expect('{ ' + ', '.join(tags) + ', };')
            size, alignment = 4, 4
        else:
            decoded = type_of(ty)
            expected = ('slice', False, ('int', False, 32)) if name == 'arguments' else ('int', False, int(native_name[1:]))
            require(decoded == expected, 'captured key field type changed')
            size, alignment = layout(decoded)
        native.append({'name': name, 'type': native_name, 'offset': field['offset'], 'bytes': size, 'alignment': alignment})
    require(key_layout.key_layout_fields(native) == key_layout.KEY_OUTPUT.read_bytes(), 'captured key differs from existing key model')
    return {'existingKeyLayoutSha256': digest(key_layout.KEY_OUTPUT), 'enumFields': len(tags),
            'keyBytes': 64, 'keyAlignment': 16, 'enumSemanticsVerified': False}


def pointer(child, size, alignment, *, explicit=None, slice=False):
    return {'kind': 'pointer', 'flags': {'size': 'slice' if slice else 'one', 'alignment': explicit,
        'isConst': True, 'isVolatile': False, 'allowZero': False, 'addressSpace': 'generic',
        'vectorIndex': None, 'hostSizeBytes': 0, 'bitOffset': 0}, 'child': child,
        'layout': {'kind': 'abi', 'bytes': 16 if slice else 8, 'alignment': 8},
        'pointeeLayout': {'kind': 'abi', 'bytes': size, 'alignment': alignment}, 'sentinel': None}


class ScalarViewDecoder(AggregateDecoder):
    record_fields = AggregateDecoder.record_fields + ' specialization'

    def __init__(self, record, child, bits, alignment, sources):
        self.bits, self.alignment, self.count = bits, alignment, bits // 8
        self.input = pointer(child, self.count, alignment)
        byte = {'kind': 'int', 'bits': 8, 'signedness': 'unsigned'}
        array = {'kind': 'array', 'length': self.count, 'child': byte,
                 'layout': {'kind': 'abi', 'bytes': self.count, 'alignment': 1}, 'sentinel': None}
        self.output = pointer(array, self.count, 1, explicit=alignment if alignment > 1 else None)
        self.source_type = ('ptr', False, False, ('int', False, bits))
        self.result_type = ('ptr', False, False, ('array', self.count, ('int', False, 8)))
        expect({k: record[k] for k in ('sourceFile', 'sourceSha256')},
               {'sourceFile': 'mem.zig', 'sourceSha256': sources['mem.zig']}, 'byte-view source identity changed')
        expect(record['specialization'], {'schema': 'oksolc.generic-instance.v1',
            'owner': {'name': 'mem.asBytes', 'sourceFile': 'mem.zig', 'sourceSha256': sources['mem.zig']},
            'sourceNoaliasBits': 0, 'sourceComptimeBits': 0, 'sourceParameterCount': 1,
            'arguments': [{'kind': 'runtime', 'runtimeIndex': 0}]}, 'unreviewed asBytes specialization')
        require(record['name'].startswith('mem.asBytes__func_'), 'unexpected byte-view callee')
        super().__init__(record)
        expect(record['body'], [0, 1, 2], 'asBytes body changed')
        require(len(record['instructions']) == 3, 'asBytes has unreviewed instructions')
        expect([i['tag'] for i in record['instructions']], ['arg', 'ptr_cast', 'ret'], 'asBytes operations changed')

    def type_of(self, record, depth=0):
        # Only the source-bound enum byte representation is erased; the ordinary
        # decoder still rejects arbitrary enum operations and pointer casts.
        if record == self.input:
            expect(record, self.input, 'asBytes parameter representation changed')
            return self.source_type
        if record == self.output:
            expect(record, self.output, 'asBytes return representation changed')
            return self.result_type
        return type_of(record, depth)

    def parameter_mapping(self, record):
        expect(record['signature'], {'callingConvention': {'auto': {}}, 'genericInstance': True,
            'varArgs': False, 'noaliasBits': 0, 'parameters': [self.input], 'returnType': self.output},
            'asBytes specialization signature changed')
        return [0]

    def extra_primitive(self, inst, ty, env):
        if inst['tag'] == 'ptr_cast':
            fields(inst, 'index tag payloadVisited type operand')
            argument_type, argument = self.ref(inst['operand'], env)
            require(argument_type == self.source_type and ty == self.result_type, 'asBytes cast changed')
            return f'(.scalarByteArray false {self.alignment} {self.count} {argument})'
        return super().extra_primitive(inst, ty, env)


def render(caller, records, sources, item_source):
    binding = caller_key_layout(caller, sources, item_source)
    require(caller['name'] == CALLER and caller['sourceFile'] == PRODUCTION and
            caller.get('sourceSha256') == sources[PRODUCTION], 'unexpected or unbound byte-view caller')
    selections = ((0, 'kind', 7, 32, 4), (1, 'instruction', 11, 8, 1),
                  (2, 'data', 15, 256, 16), (4, 'sequence', 24, 32, 4))
    lines = ['/-', '// Copyright (C) 2026 OKcontract Pte. Ltd.', '// SPDX-License-Identifier: GPL-3.0',
        'Generated from the four complete scalar asBytes specializations and their caller cuts.',
        'The argument-slice helper and complete hash-caller execution remain separate obligations.', '-/',
        'import Compiler.ZigAir.ScalarBytesAir', '', 'namespace Compiler.ZigAir.GeneratedExpressionHashBytes',
        'open Compiler.ZigAir.Memory', '']
    scope = []
    key = caller['signature']['parameters'][1]
    require(len(caller['body']) == 30 and
        [i['index'] for i in caller['instructions'] if i.get('payloadVisited') is True] == caller['body'],
        'caller visited instruction order changed')
    for field, name, first, bits, alignment in selections:
        selected_ids = caller['body'][first:first + 3]
        selected, called, converted = [caller['instructions'][index] for index in selected_ids]
        fields(selected, 'index tag payloadVisited type operand fieldIndex')
        fields(called, 'index tag payloadVisited type callee arguments')
        fields(converted, 'index tag payloadVisited type operand')
        field_reg, call_reg, slice_reg = selected_ids
        expect([i['index'] for i in (selected, called, converted)], selected_ids, 'byte-view cut changed')
        require(all(i['payloadVisited'] is True and not i.get('unsupportedPayload', False)
                    for i in (selected, called, converted)), 'byte-view cut is incomplete')
        expect(selected['operand'], {'kind': 'instruction', 'index': 3}, 'byte-view key pointer changed')
        expect(selected['fieldIndex'], field, 'byte-view field changed')
        expect(selected['tag'], 'struct_field_ptr_index_' + str(field) if field < 4 else 'struct_field_ptr',
               'byte-view field operation changed')
        require(called['tag'] == 'call' and called['callee']['kind'] == 'function', 'byte-view invocation changed')
        callee = records[called['callee']['identity']['name']]
        expect(called['callee']['identity'], {k: callee[k] for k in ('name', 'sourceFile', 'sourceSha256')},
               'byte-view body identity changed')
        for key_name in ('configuration', 'schema', 'capturePoint', 'bodyTraversal'):
            expect(callee[key_name], caller[key_name], 'byte-view capture configuration differs')
        decoder = ScalarViewDecoder(callee, key['fields'][field]['type'], bits, alignment, sources)
        expect(selected['type'], decoder.input, 'byte-view field pointer type changed')
        expect(called['arguments'], [{'kind': 'instruction', 'index': field_reg}], 'byte-view argument changed')
        expect(called['type'], decoder.output, 'byte-view call result changed')
        expect(converted['tag'], 'array_to_slice', 'byte-view conversion changed')
        expect(converted['operand'], {'kind': 'instruction', 'index': call_reg}, 'byte-view conversion operand changed')
        expect(converted['type'], pointer({'kind': 'int', 'bits': 8, 'signedness': 'unsigned'}, 1, 1, slice=True),
               'byte-view slice type changed')
        program = decoder.program(callee)
        lines += [f'def {name} : AggregateAir.Program :=', program, '',
            f'def {name}View (next : AggregateCall.Code) : AggregateCall.Code :=',
            f'  .bind {field_reg} (.pointer false false (.scalar (.int false {bits})))',
            f'    (.primitive (.fieldPointer (.local 3) {key["fields"][field]["offset"]}))',
            f'    (ScalarBytesAir.viewCode {name} (.local {field_reg}) {call_reg} {slice_reg} {bits // 8} next)', '']
        scope.append({'fieldIndex': field, 'callee': callee['name'], 'selectedInstructions': selected_ids,
                      'calleeInstructions': len(decoder.visited), 'representationBits': bits})
    lines += ['end Compiler.ZigAir.GeneratedExpressionHashBytes', '']
    return '\n'.join(lines), {'keyLayoutBinding': binding, 'scalarViews': scope,
        'argumentSliceHelperTranslated': False, 'completeCallerTranslated': False, 'sourceAdapterFormallyVerified': False}
