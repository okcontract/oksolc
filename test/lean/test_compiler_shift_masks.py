#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admission boundaries for the shift-product and covered-mask helpers.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_shift_masks as extract
from extract_compiler import Unsupported


def opcode_mutation():
    opcodes = extract.nested.OPCODES.read_bytes()
    before, after = b'SHR = 0x1c,', b'SHR = 0x0c,'
    if opcodes.count(before) != 1:
        raise ValueError('opcode mutation must target exactly one binding')
    return extract.extract(extract.nested.SOURCE.read_bytes(), opcodes.replace(before, after),
                           extract.nested.STORAGE.read_bytes())


class ShiftMaskTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                        extract.nested.STORAGE.read_bytes()), extract.OUTPUT.read_bytes())

    def test_semantic_mutations_reject(self):
        for before, after in [
            ('const max_word = ~@as(u256, 0);', 'const max_word = ~@as(u128, 0);'),
            ('classes.knownConstantValue(mask_id) orelse return null', 'classes.knownConstantValue(shifted_id) orelse return null'),
            ('classes.operationArguments(shifted_id, .SHR)', 'classes.operationArguments(shifted_id, .SHL)'),
            ('shifted.len != 2', 'shifted.len < 2'),
            ('classes.knownConstantValue(shifted[0])', 'classes.knownConstantValue(shifted[1])'),
            ('if (amount > 256) return null;', 'if (amount >= 256) return null;'),
            ('if (amount == 256) @as(u256, 0)', 'if (amount == 256) @as(u256, 1)'),
            ('max_word >> @intCast(amount)', 'max_word << @intCast(amount)'),
            ('(mask & coverage) == coverage', '(mask & coverage) == mask'),
            ('classes.makeOperation(.SHR, shifted, debug_data)', 'classes.makeOperation(.SHL, shifted, debug_data)'),
            ('classes.knownConstantValue(shift[1]) != 1', 'classes.knownConstantValue(shift[0]) != 1'),
            ('shift.len != 2 or', 'shift.len != 2 and'),
            ('&.{ shift[0], value }, debug_data', '&.{ value, shift[0] }, debug_data'),
        ]:
            source = extract.nested.SOURCE.read_bytes()
            self.assertIn(before.encode(), source)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(source.replace(before.encode(), after.encode()), extract.nested.OPCODES.read_bytes(),
                                extract.nested.STORAGE.read_bytes())

    def test_opcode_is_executable(self):
        self.assertIn(b'def shrOpcode : Opcode := 12', opcode_mutation())

    def test_trivia(self):
        source, opcodes, storage = (extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                    extract.nested.STORAGE.read_bytes())
        self.assertEqual(extract.extract(source, opcodes, storage).split(b'def shlOpcode', 1)[1],
                         extract.extract(source + b'\n// inert comment\n', opcodes, storage).split(b'def shlOpcode', 1)[1])


if __name__ == '__main__':
    unittest.main()
