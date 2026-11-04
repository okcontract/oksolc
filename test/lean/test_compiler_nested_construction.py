#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admission and dependency mutations for complete nested construction helpers.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_nested_construction as extract
from extract_compiler import Unsupported


def opcode_mutation():
    opcodes = extract.nested.OPCODES.read_bytes()
    before, after = b'ISZERO = 0x15,', b'ISZERO = 0x0c,'
    if opcodes.count(before) != 1:
        raise ValueError('opcode mutation must target exactly one binding')
    return extract.extract(extract.nested.SOURCE.read_bytes(), opcodes.replace(before, after),
                           extract.nested.STORAGE.read_bytes())


class ConstructionTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                        extract.nested.STORAGE.read_bytes()), extract.OUTPUT.read_bytes())

    def test_body_mutations_reject(self):
        for before, after in [
            ('const inner = try classes.makeOperation(.ISZERO, &.{value}, debug_data);',
             'const inner = try classes.makeOperation(.NOT, &.{value}, debug_data);'),
            ('return classes.makeOperation(.ISZERO, &.{inner}, debug_data);',
             'return classes.makeOperation(.ISZERO, &.{value}, debug_data);'),
            ('if (sameExpression(classes, nested[1], repeated)) 1',
             'if (sameExpression(classes, nested[1], repeated)) 0'),
            ('if (sameExpression(classes, nested[0], repeated)) 0',
             'if (sameExpression(classes, nested[0], repeated)) 1'),
            ('var operands = [2]ExpressionId{ nested[0], nested[1] };',
             'var operands = [2]ExpressionId{ nested[1], nested[0] };'),
            ('if (repeated_is_first) operands[repeated_index] = repeated;',
             'if (!repeated_is_first) operands[repeated_index] = repeated;'),
            ('operands[repeated_index] = repeated;', 'operands[repeated_index] = nested_id;'),
            ('return try classes.makeOperation(instruction, &operands, debug_data);',
             'return try classes.makeOperation(instruction, &operands, .{});'),
            ('return try classes.makeOperation(instruction, &operands, debug_data);',
             'return classes.makeOperation(instruction, &operands, debug_data) catch null;'),
            ('nested.len != 2', 'nested.len > 2'),
            ('return left == right;', 'return left != right;'),
        ]:
            source = extract.nested.SOURCE.read_bytes()
            self.assertIn(before.encode(), source)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(source.replace(before.encode(), after.encode()), extract.nested.OPCODES.read_bytes(),
                                extract.nested.STORAGE.read_bytes())

    def test_opcode_is_executable(self):
        self.assertIn(b'def nestedIszeroOpcode : Opcode := 12', opcode_mutation())

    def test_trivia(self):
        source, opcodes, storage = (extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                    extract.nested.STORAGE.read_bytes())
        self.assertEqual(extract.extract(source, opcodes, storage).split(b'def nestedIszeroOpcode', 1)[1],
                         extract.extract(source + b'\n// inert comment\n', opcodes, storage).split(b'def nestedIszeroOpcode', 1)[1])


if __name__ == '__main__':
    unittest.main()
