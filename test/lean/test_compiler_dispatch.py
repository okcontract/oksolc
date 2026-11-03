#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admission boundaries for the entire ordered dispatcher and its revision gates.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_dispatch as extract
from extract_compiler import Unsupported


def opcode_mutation():
    opcodes = extract.nested.OPCODES.read_bytes()
    before, after = b'SAR = 0x1d,', b'SAR = 0x0c,'
    if opcodes.count(before) != 1:
        raise ValueError('opcode mutation must target exactly one binding')
    return extract.extract(extract.nested.SOURCE.read_bytes(), opcodes.replace(before, after),
                           extract.nested.STORAGE.read_bytes(), extract.VERSIONS.read_bytes())


class DispatchTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
            extract.nested.STORAGE.read_bytes(), extract.VERSIONS.read_bytes()), extract.OUTPUT.read_bytes())

    def test_entire_dispatcher_mutations_reject(self):
        source = extract.nested.SOURCE.read_bytes()
        start = source.index(b'pub fn simplifyWithOptions(')
        end = source.index(b'\nconst ConstantOperand', start)
        body = source[start:end]
        mutations = [
            ('[3]u256 = undefined', '[4]u256 = undefined'),
            ('arguments.len != 0', 'arguments.len == 0'),
            ('constant_arguments[index] =', 'constant_arguments[0] ='),
            ('all_constant = false;', 'all_constant = true;'),
            ('Algebraic.select(instruction, .constants', 'Algebraic.select(instruction, .equal'),
            ('right_constant == 0 or left_constant == 0', 'right_constant == 0 and left_constant == 0'),
            ('right_constant == 0xff', 'left_constant == 0xff'),
            ('left_constant == 31', 'left_constant == 30'),
            ('sameExpression(classes, left, right)', 'sameExpression(classes, left, left)'),
            ('cancelNestedBinary(classes, .XOR, left, right)', 'cancelNestedBinary(classes, .OR, left, right)'),
            ('dropRepeatedNested(classes, instruction, right, left, true,', 'dropRepeatedNested(classes, instruction, right, left, false,'),
            ('@min(outer_byte, inner_byte)', '@max(outer_byte, inner_byte)'),
            ('options.for_yul_optimizer and', '!options.for_yul_optimizer and'),
            ('modulus - 1', 'modulus -% 1'),
            ('left_constant.? >= 31', 'left_constant.? >= 32'),
            ('addressInstruction(classes, right, left)', 'addressInstruction(classes, right, right)'),
            ('reassociate(classes, instruction, left, right, false,', 'reassociate(classes, instruction, left, right, true,'),
            ('256 -| @min(inner_shift, 256)', '256 - @min(inner_shift, 256)'),
            ('outer_shift + inner_shift', 'outer_shift +% inner_shift'),
            ('outer_shift < 256 and inner_shift < 256', 'outer_shift < 256 or inner_shift < 256'),
            ('distributeAlternatingMask(classes, left, right,', 'distributeAlternatingMask(classes, right, left,'),
            ('sameExpression(classes, lhs_shift[0], rhs_shift[0])', 'sameExpression(classes, lhs_shift[1], rhs_shift[1])'),
            ('&.{ shift[0], left }', '&.{ left, shift[0] }'),
            ('left_constant.? + amount / 8', 'left_constant.? + amount / 4'),
            ('left_constant.? - amount / 8', 'left_constant.? -% amount / 8'),
            ('(left_constant.? >> 3) + byte_index', '(left_constant.? >> 2) + byte_index'),
            ('(256 - amount) / 8 == left_constant.? + 1', '(256 - amount) / 8 == left_constant.?'),
            ('0 -% parts.value', '0 - parts.value'),
            ('if (third.len == 1)', 'if (third.len == 2)'),
            ('if (options.evm_version)', 'if (null)'),
            ('evm_version.hasSelfBalance()', 'evm_version.hasBitwiseShifting()'),
            ('&.{ even, parity }', '&.{ parity, even }'),
            ('return null;', 'return 0;'),
        ]
        for before, after in mutations:
            self.assertEqual(body.count(before.encode()), 1)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                changed = source[:start] + body.replace(before.encode(), after.encode()) + source[end:]
                extract.extract(changed, extract.nested.OPCODES.read_bytes(),
                    extract.nested.STORAGE.read_bytes(), extract.VERSIONS.read_bytes())

    def test_options_aliases_and_versions_reject(self):
        data, ops, storage, versions = (extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
            extract.nested.STORAGE.read_bytes(), extract.VERSIONS.read_bytes())
        for before, after in [
            (b'for_yul_optimizer: bool = false', b'for_yul_optimizer: bool = true'),
            (b'debug_data, .{});', b'debug_data, .{ .for_yul_optimizer = true });'),
            (b'@import("algebraic_rules.zig")', b'@import("different_rules.zig")'),
        ]:
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(data.replace(before, after), ops, storage, versions)
        for before, after in [
            (b'Constantinople,\n    Petersburg,', b'Petersburg,\n    Constantinople,'),
            (b'return self.atLeast(.Constantinople);', b'return self.atLeast(.Byzantium);'),
            (b'return self.atLeast(.Istanbul);', b'return self.atLeast(.Berlin);'),
            (b'>= @backingInt(version)', b'> @backingInt(version)'),
        ]:
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(data, ops, storage, versions.replace(before, after))

    def test_opcode_is_executable(self):
        self.assertIn(b'def opSAR : Opcode := 12', opcode_mutation())

    def test_opcode_alias_rejects(self):
        opcodes = extract.nested.OPCODES.read_bytes().replace(b'SAR = 0x1d,', b'SAR = 0x1c,')
        with self.assertRaises(Unsupported):
            extract.extract(extract.nested.SOURCE.read_bytes(), opcodes,
                extract.nested.STORAGE.read_bytes(), extract.VERSIONS.read_bytes())


if __name__ == '__main__':
    unittest.main()
