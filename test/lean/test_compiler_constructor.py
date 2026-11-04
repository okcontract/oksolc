#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Production constructor extraction, independent opcode bindings and mutations.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_constructor as extract
from extract_compiler import Unsupported

MUTATIONS = {
    'wrong_constant': ('source', 'AssemblyItem.initPush(value, debug_data);',
        'AssemblyItem.initPush(0, debug_data);', '(constructorCode.constantRequest 7).item.data = 7'),
    'wrong_operation': ('source', 'AssemblyItem.initInstruction(instruction, debug_data);',
        'AssemblyItem.initInstruction(.SUB, debug_data);',
        '(constructorCode.operationRequest (buildOpcode .NOT) [0]).item.instruction = some 25'),
    'wrong_sequence': ('source', 'self.find(item, arguments, true, 0);',
        'self.find(item, arguments, true, 1);', '(constructorCode.constantRequest 7).sequence = 0'),
    'wrong_opcode': ('opcodes', 'ISZERO = 0x15,', 'ISZERO = 0x0c,',
        'buildOpcode .ISZERO = specifiedOpcode .ISZERO'),
}


def inputs():
    return {name: path.read_bytes() for name, path in
            [('source', extract.SOURCE), ('items', extract.ITEMS), ('opcodes', extract.OPCODES)]}


def generate(values):
    return extract.extract(values['source'], values['items'], values['opcodes'])


def mutated(name):
    values = inputs()
    target, before, after, claim = MUTATIONS[name]
    if values[target].count(before.encode()) != 1:
        raise ValueError('mutation must target exactly one source span: ' + name)
    values[target] = values[target].replace(before.encode(), after.encode())
    return generate(values), claim


class ConstructorTests(unittest.TestCase):
    def test_complete_constructor_defaults_and_debug_forwarding(self):
        for target, before, after in [
            ('source', 'AssemblyItem.initInstruction(instruction, debug_data);', 'AssemblyItem.initInstruction(instruction, .{});'),
            ('items', 'data_value: u256 = 0,', 'data_value: u256 = 1,'),
            ('items', 'verbatim: ?VerbatimBytecode = null,', 'verbatim: ?VerbatimBytecode = undefined,'),
            ('items', 'debug_data: DebugData = .{},', 'debug_data: DebugData = undefined,'),
            ('items', 'jump_type: JumpType = .Ordinary,', 'jump_type: JumpType = .OutOfFunction,'),
            ('items', 'pushed_value: ?u256 = null,', 'pushed_value: ?u256 = 0,'),
            ('items', 'immutable_occurrences: ?usize = null,', 'immutable_occurrences: ?usize = 0,'),
            ('items', 'modifier_depth: usize = 0,', 'modifier_depth: usize = 19,'),
            ('items', '.debug_data = debug_data,', '.debug_data = .{},'),
        ]:
            values = inputs()
            self.assertIn(before.encode(), values[target])
            values[target] = values[target].replace(before.encode(), after.encode(), 1)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                generate(values)

    def test_freshness(self):
        self.assertEqual(generate(inputs()), extract.OUTPUT.read_bytes())

    def test_physical_argument_view_binding(self):
        import constructor_frame_checks
        binding = constructor_frame_checks.bindings()
        self.assertEqual(binding['argumentStorage'], 'original caller view forwarded unchanged')
        self.assertEqual([c['name'] for c in binding['controls']], ['empty-arguments', 'shifted-view', 'invented-copy'])
        self.assertTrue(all(c['admitted'] is False for c in binding['controls']))

    def test_semantic_mutations_are_executable_data(self):
        baseline = generate(inputs()).split(b'def constructorCode', 1)[1]
        for name in MUTATIONS:
            with self.subTest(name=name):
                self.assertNotEqual(mutated(name)[0].split(b'def constructorCode', 1)[1], baseline)

    def test_types_defaults_and_primitive_rejections(self):
        for target, before, after in [
            ('source', 'pub const Id = u32;', 'pub const Id = u64;'),
            ('source', 'return self.findDefault(&item, arguments);', 'return self.findDefault(&item, &.{});'),
            ('source', 'AssemblyItem.initPush(value, debug_data);', 'AssemblyItem.initPush(value, .{});'),
            ('source', 'self.find(item, arguments, true, 0);', 'self.find(item, arguments, true, 4294967296);'),
            ('items', 'instruction_value: ?InstructionModule.Instruction = null,',
                'instruction_value: ?InstructionModule.Instruction = .ADD,'),
            ('items', 'data_value: u256 = 0,', 'data_value: u128 = 0,'),
            ('items', 'initType(.Push, value, debug_data);', 'initType(.Operation, value, debug_data);'),
            ('items', '.data_value = value,', '.data_value = 0,'),
            ('items', '.instruction_value = opcode,', '.instruction_value = .SUB,'),
            ('items', 'UndefinedItem,\n    Operation,', 'Operation,\n    UndefinedItem,'),
            ('opcodes', 'enum(u8)', 'enum(u16)'),
            ('opcodes', 'NOT = 0x19,', 'NOT = (0x19), // NOT = 0x19,'),
        ]:
            values = inputs()
            self.assertIn(before.encode(), values[target])
            values[target] = values[target].replace(before.encode(), after.encode())
            with self.subTest(before=before), self.assertRaises(Unsupported):
                generate(values)

    def test_trivia_is_not_semantic(self):
        values = inputs()
        baseline = generate(values).split(b'def constructorCode', 1)[1]
        values['opcodes'] += b'\n// NOT = 3,\n'
        self.assertEqual(generate(values).split(b'def constructorCode', 1)[1], baseline)

    def test_fields_after_methods_are_reviewed(self):
        for marker in ('    pub fn initInstruction(', '    pub fn initType(', '    pub fn clone('):
            values = inputs()
            self.assertEqual(values['items'].count(marker.encode()), 1)
            values['items'] = values['items'].replace(marker.encode(), b'    unreviewed_field: u8 = 0,\n\n' + marker.encode())
            with self.subTest(marker=marker), self.assertRaises(Unsupported):
                generate(values)

    def test_complete_initializer_bodies(self):
        for name, tail in (('initPush', b'return initType(.Push, value, debug_data);'),
                           ('initType', b'.data_value = value,\n                .debug_data = debug_data,\n            };'),
                           ('initInstruction', b'.instruction_value = opcode,\n            .debug_data = debug_data,\n        };')):
            values = inputs()
            self.assertEqual(values['items'].count(tail), 1)
            values['items'] = values['items'].replace(tail, tail + b'\n        comptime {}')
            with self.subTest(name=name), self.assertRaises(Unsupported):
                generate(values)


if __name__ == '__main__':
    unittest.main()
