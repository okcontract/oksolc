#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Complete opposite-shift body admission and opcode/dependency mutations.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_opposite_shifts as extract
from extract_compiler import Unsupported


def opcode_mutation():
    opcodes = extract.nested.OPCODES.read_bytes()
    before, after = b'AND = 0x16,', b'AND = 0x0c,'
    if opcodes.count(before) != 1:
        raise ValueError('opcode mutation must target exactly one binding')
    return extract.extract(extract.nested.SOURCE.read_bytes(), opcodes.replace(before, after),
                           extract.nested.STORAGE.read_bytes())


class OppositeShiftTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                        extract.nested.STORAGE.read_bytes()), extract.OUTPUT.read_bytes())

    def test_semantic_mutations_reject(self):
        for before, after in [
            ('const max_word = ~@as(u256, 0);', 'const max_word = ~@as(u128, 0);'),
            ('const mask = if (outer_instruction == .SHR)', 'const mask = if (outer_instruction == .SHL)'),
            ('(max_word << @intCast(inner_shift)) >> @intCast(outer_shift)',
             '(max_word << @intCast(outer_shift)) >> @intCast(inner_shift)'),
            ('(max_word >> @intCast(inner_shift)) << @intCast(outer_shift)',
             '(max_word << @intCast(inner_shift)) >> @intCast(outer_shift)'),
            ('@intCast(outer_shift)', '@truncate(outer_shift)'),
            ('const shifted = if (inner_shift > outer_shift)', 'const shifted = if (inner_shift >= outer_shift)'),
            ('if (outer_instruction == .SHR) .SHL else .SHR', 'if (outer_instruction == .SHR) .SHR else .SHL'),
            ('classes.makeConstant(inner_shift - outer_shift, debug_data)', 'classes.makeConstant(inner_shift -% outer_shift, debug_data)'),
            ('classes.makeConstant(outer_shift - inner_shift, debug_data)', 'classes.makeConstant(inner_shift - outer_shift, debug_data)'),
            ('else\n        value;', 'else\n        0;'),
            ('&.{ shifted, try classes.makeConstant(mask, debug_data) }', '&.{ value, try classes.makeConstant(mask, debug_data) }'),
            ('classes.makeConstant(mask, debug_data)', 'classes.makeConstant(mask, .{})'),
            ('outer_shift: u256,', 'outer_shift: u8,'),
        ]:
            source = extract.nested.SOURCE.read_bytes()
            self.assertIn(before.encode(), source)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(source.replace(before.encode(), after.encode()), extract.nested.OPCODES.read_bytes(),
                                extract.nested.STORAGE.read_bytes())

    def test_opcode_is_executable(self):
        self.assertIn(b'def andOpcode : Opcode := 12', opcode_mutation())

    def test_trivia(self):
        source, opcodes, storage = (extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                    extract.nested.STORAGE.read_bytes())
        self.assertEqual(extract.extract(source, opcodes, storage).split(b'def shlOpcode', 1)[1],
                         extract.extract(source + b'\n// inert comment\n', opcodes, storage).split(b'def shlOpcode', 1)[1])


if __name__ == '__main__':
    unittest.main()
