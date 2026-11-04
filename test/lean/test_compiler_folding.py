#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Complete constant-folder admission and semantic mutation controls.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_folding as extract
from extract_compiler import Unsupported

MUTATIONS = {
    'operator': ('source', 'arguments[0] +% arguments[1] else null,',
        'arguments[0] -% arguments[1] else null,', '1 [7, 2]', '9'),
    'arity': ('source', '.ADD => if (arguments.len == 2)',
        '.ADD => if (arguments.len == 1)', '1 [7, 2]', '9'),
    'index': ('source', 'arguments[0] -% arguments[1] else null,',
        'arguments[1] -% arguments[0] else null,', '3 [7, 2]', '5'),
    'bounds': ('source', 'arguments[0] +% arguments[1] else null,',
        'arguments[0] +% arguments[2] else null,', '1 [7, 2]', '9'),
    'guard_value': ('source', 'if (arguments[1] == 0) 0 else arguments[0] /',
        'if (arguments[1] == 0) 1 else arguments[0] /', '4 [7, 0]', '0'),
    'guard_index': ('source', 'if (arguments[1] == 0) 0 else arguments[0] /',
        'if (arguments[0] == 0) 0 else arguments[0] /', '4 [7, 0]', '0'),
    'helper_order': ('source', 'byteValue(arguments[0], arguments[1])',
        'byteValue(arguments[1], arguments[0])', '26 [31, 7]', '7'),
    'opcode': ('opcodes', 'ADD = 0x01,', 'ADD = 0x0c,', '1 [7, 2]', '9'),
}


def inputs():
    return {'source': extract.SOURCE.read_bytes(), 'opcodes': extract.OPCODES.read_bytes()}


def generate(values):
    return extract.extract(values['source'], values['opcodes'])


def mutated(name):
    values = inputs()
    target, before, after, call, result = MUTATIONS[name]
    if values[target].count(before.encode()) != 1:
        raise ValueError('mutation must target exactly one source span: ' + name)
    values[target] = values[target].replace(before.encode(), after.encode())
    return generate(values), 'run helpers clauses ' + call + ' = .ok (some ' + result + ')'


class FoldingTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(generate(inputs()), extract.OUTPUT.read_bytes())

    def test_semantic_mutations_are_executable_data(self):
        baseline = generate(inputs()).split(b'def clauses', 1)[1]
        for name in MUTATIONS:
            with self.subTest(name=name):
                self.assertNotEqual(mutated(name)[0].split(b'def clauses', 1)[1], baseline)

    def test_trivia_is_not_semantic(self):
        values = inputs()
        baseline = generate(values).split(b'def signedDivision', 1)[1]
        values['source'] += b'\n// fn signExtend is not a declaration\n'
        values['opcodes'] += b'\n// ADD = 12,\n'
        self.assertEqual(generate(values).split(b'def signedDivision', 1)[1], baseline)

    def test_entire_helper_bodies_are_bound(self):
        for before, after in [
            ('@bitCast(value);', '@intCast(value);'),
            ('if (right == 0) return 0;', 'if (right == 1) return 0;'),
            ('if (lhs == std.math.minInt(i256) and rhs == -1) return left;', ''),
            ('if (rhs == 1 or rhs == -1) return 0;', ''),
            ('exponent >>= 1', 'exponent >>= 2'),
            ('result *%= base;', 'result *= base;'),
            ('base *%= base;', 'base +%= base;'),
            ('if (index >= 32) return 0;', 'if (index > 32) return 0;'),
            ('const shift: u8', 'const shift: u7'),
            ('@as(u257, left)', '@as(u256, left)'),
            ('@as(u512, right)', '@as(u511, right)'),
            ('byte_index >= 31', 'byte_index >= 32'),
            ('byte_index * 8 + 7', 'byte_index * 8 + 8'),
            ('(@as(u256, 1) << test_bit) - 1', '(@as(u256, 1) << test_bit) - 2'),
            ('amount >= 256', 'amount > 256'),
            ('else value >> @intCast(amount);', 'else value << @intCast(amount);'),
        ]:
            values = inputs()
            self.assertIn(before.encode(), values['source'])
            values['source'] = values['source'].replace(before.encode(), after.encode())
            with self.subTest(before=before), self.assertRaises(Unsupported):
                generate(values)

    def test_dispatch_rejects_unmodeled_language(self):
        for before, after in [
            ('const std = @import("std");', 'const std = @import("fake.zig");'),
            ('const Instruction = @import("instruction.zig").Instruction;',
                'const Instruction = @import("fake.zig").Instruction;'),
            ('arguments[0] +% arguments[1]', 'arguments[0] + arguments[1]'),
            ('arguments.len == 2', 'arguments.len >= 2'),
            ('~arguments[0] else null', '~arguments[0] else 0'),
            ('arguments: []const u256) ?u256', 'arguments: []const u128) ?u256'),
        ]:
            values = inputs()
            self.assertIn(before.encode(), values['source'])
            values['source'] = values['source'].replace(before.encode(), after.encode())
            with self.subTest(before=before), self.assertRaises(Unsupported):
                generate(values)


if __name__ == '__main__':
    unittest.main()
