#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Complete admission boundaries of the nested matching helpers.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_nested as extract
from extract_compiler import Unsupported


def opcode_mutation():
    source, opcodes = extract.SOURCE.read_bytes(), extract.OPCODES.read_bytes()
    before, after = b'NOT = 0x19,', b'NOT = 0x0c,'
    if opcodes.count(before) != 1:
        raise ValueError('opcode mutation must target exactly one binding')
    return extract.extract(source, opcodes.replace(before, after), extract.STORAGE.read_bytes())


class NestedTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.SOURCE.read_bytes(), extract.OPCODES.read_bytes(), extract.STORAGE.read_bytes()),
                         extract.OUTPUT.read_bytes())

    def test_semantic_mutations_reject(self):
        for before, after in [
            ('return left == right;', 'return left != right;'),
            ('classes.sameExpression(left, right);', 'classes.sameExpression(right, left);'),
            ('arguments.len != 2', 'arguments.len < 2'),
            ('classes.knownConstantValue(arguments[1])', 'classes.knownConstantValue(arguments[0])'),
            ('.constant_expression = arguments[1],', '.constant_expression = arguments[0],'),
            ('classes.operationArguments(nested_id, instruction)', 'classes.operationArguments(single, instruction)'),
            ('nested.len != 2', 'nested.len != 1'),
            ('sameExpression(classes, nested[0], single)) return nested[1];',
             'sameExpression(classes, nested[0], single)) return nested[0];'),
            ('sameExpression(classes, nested[1], single)) return nested[0];',
             'sameExpression(classes, nested[1], single)) return nested[1];'),
            ('if (sameExpression(classes, operand, single)) return operand;',
             'if (sameExpression(classes, operand, single)) return single;'),
            ('classes.operationArguments(possible_not, .NOT)', 'classes.operationArguments(possible_not, .ISZERO)'),
            ('arguments.len == 1 and sameExpression', 'arguments.len == 1 or sameExpression'),
            ('sameExpression(classes, arguments[0], value);', 'sameExpression(classes, arguments[1], value);'),
            ('pub const ExpressionId = u32;', 'pub const ExpressionId = u64;'),
            ('constant_expression: ExpressionId,', 'constant_expression: u64,'),
            ('const Instruction = @import("instruction.zig").Instruction;',
             'const Instruction = @import("fake.zig").Instruction;'),
        ]:
            source = extract.SOURCE.read_bytes()
            self.assertIn(before.encode(), source)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(source.replace(before.encode(), after.encode()), extract.OPCODES.read_bytes(), extract.STORAGE.read_bytes())

    def test_equality_specialization_is_bound(self):
        storage = extract.STORAGE.read_bytes().replace(b'pub const ExpressionClasses = struct {',
            b'pub const ExpressionClasses = struct {\n'
            b'pub fn sameExpression(_: *const ExpressionClasses, _: Id, _: Id) bool { return true; }')
        with self.assertRaises(Unsupported):
            extract.extract(extract.SOURCE.read_bytes(), extract.OPCODES.read_bytes(), storage)

    def test_opcode_mutation_is_executable(self):
        self.assertIn(b'def nestedNotOpcode : Opcode := 12', opcode_mutation())

    def test_trivia(self):
        source, opcodes = extract.SOURCE.read_bytes(), extract.OPCODES.read_bytes()
        baseline = extract.extract(source, opcodes, extract.STORAGE.read_bytes()).split(b'def nestedNotOpcode', 1)[1]
        changed = extract.extract(source + b'\n// return nested[7];\n', opcodes, extract.STORAGE.read_bytes())
        self.assertEqual(changed.split(b'def nestedNotOpcode', 1)[1], baseline)


if __name__ == '__main__':
    unittest.main()
