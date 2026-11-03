#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Source admission and materialization boundaries for recursive reassociation.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_associative as extract
from extract_compiler import Unsupported


def opcode_mutation():
    opcodes = extract.nested.OPCODES.read_bytes()
    before, after = b'ADD = 0x01,', b'ADD = 0x0c,'
    if opcodes.count(before) != 1:
        raise ValueError('opcode mutation must target exactly one binding')
    return extract.extract(extract.nested.SOURCE.read_bytes(), opcodes.replace(before, after),
                           extract.nested.STORAGE.read_bytes())


class AssociativeTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                        extract.nested.STORAGE.read_bytes()), extract.OUTPUT.read_bytes())

    def test_semantic_mutations_reject(self):
        for before, after in [
            ('.ADD, .MUL, .AND, .OR, .XOR => true,', '.ADD, .MUL, .AND, .OR, .SUB => true,'),
            ('.ADD => left +% right,', '.ADD => left + right,'),
            ('.MUL => left *% right,', '.MUL => left +% right,'),
            ('.AND => left & right,', '.AND => left | right,'),
            ('else => unreachable,', 'else => 0,'),
            ('const parts = splitConstant(classes, nested) orelse return null;',
             'const parts = splitConstant(classes, nested) orelse unreachable;'),
            ('combineConstants(instruction, parts.value, other_constant)',
             'combineConstants(instruction, parts.value, parts.value)'),
            ('const inner = if (nested_is_right)', 'const inner = if (!nested_is_right)'),
            ('&.{ other, parts.expression }, debug_data)', '&.{ parts.expression, other }, debug_data)'),
            ('&.{ parts.expression, other }, debug_data)', '&.{ other, parts.expression }, debug_data)'),
            ('classes.materializeConstant(parts.constant_expression, parts.value, debug_data)',
             'classes.materializeConstant(parts.expression, parts.value, debug_data)'),
            ('&.{ inner, try classes.materializeConstant', '&.{ other, try classes.materializeConstant'),
            ('return left == right;', 'return left != right;'),
        ]:
            source = extract.nested.SOURCE.read_bytes()
            self.assertIn(before.encode(), source)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(source.replace(before.encode(), after.encode()), extract.nested.OPCODES.read_bytes(),
                                extract.nested.STORAGE.read_bytes())

    def test_materialization_is_bound(self):
        source, storage = extract.nested.SOURCE.read_bytes(), extract.nested.STORAGE.read_bytes()
        before = b'return self.makeConstant(value, debug_data);'
        self.assertEqual(storage.count(before), 1)
        for after in [b'return self.makeConstant(0, debug_data);', b'return self.makeConstant(value, .{});', b'return 0;']:
            with self.subTest(after=after), self.assertRaises(Unsupported):
                extract.extract(source, extract.nested.OPCODES.read_bytes(), storage.replace(before, after))

    def test_opcode_is_executable(self):
        self.assertIn(b'if instruction == 12 then .ok (left + right)', opcode_mutation())

    def test_trivia(self):
        source, opcodes, storage = (extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                    extract.nested.STORAGE.read_bytes())
        self.assertEqual(extract.extract(source, opcodes, storage).split(b'def isAssociative', 1)[1],
                         extract.extract(source + b'\n// inert comment\n', opcodes, storage).split(b'def isAssociative', 1)[1])


if __name__ == '__main__':
    unittest.main()
