#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admission boundaries for ordered mask distribution and retained failure state.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_alternating_mask as extract
from extract_compiler import Unsupported


def opcode_mutation():
    opcodes = extract.nested.OPCODES.read_bytes()
    before, after = b'OR = 0x17,', b'OR = 0x18,'
    if opcodes.count(before) != 1:
        raise ValueError('opcode mutation must target exactly one binding')
    return extract.extract(extract.nested.SOURCE.read_bytes(), opcodes.replace(before, after),
                           extract.nested.STORAGE.read_bytes())


class AlternatingMaskTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                        extract.nested.STORAGE.read_bytes()), extract.OUTPUT.read_bytes())

    def test_semantic_mutations_reject(self):
        source = extract.nested.SOURCE.read_bytes()
        start = source.index(b'fn distributeAlternatingMask(')
        end = source.index(b'\nfn removeCoveredShiftMask(', start)
        helper = source[start:end]
        for before, after in [
            ('[_]bool{ false, true }', '[_]bool{ true, false }'),
            ('|inner_index|', '|second_index|'),
            ('outer_arguments[1 - second_index]', 'outer_arguments[second_index]'),
            ('operationArguments(second_id, .OR)', 'operationArguments(second_id, .XOR)'),
            ('alternatives.len != 2', 'alternatives.len != 1'),
            ('operationArguments(alternatives[inner_index], .AND)', 'operationArguments(alternatives[inner_index], .OR)'),
            ('inner.len != 2', 'inner.len != 3'),
            ('constant_first == false', 'constant_first == true'),
            ('inner_mask & outer_mask', 'inner_mask | outer_mask'),
            ('inner[expression_index]', 'inner[constant_index]'),
            ('outer_mask_id,\n                    outer_mask,', 'second_id,\n                    outer_mask,'),
            ('alternatives[1 - inner_index]', 'alternatives[inner_index]'),
            ('&.{ left, right }', '&.{ right, left }'),
            ('try classes.makeConstant', 'classes.makeConstant'),
            ('return null;', 'return outer_left;'),
        ]:
            self.assertEqual(helper.count(before.encode()), 1)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                changed = helper.replace(before.encode(), after.encode())
                extract.extract(source[:start] + changed + source[end:], extract.nested.OPCODES.read_bytes(),
                                extract.nested.STORAGE.read_bytes())

    def test_opcode_is_executable(self):
        self.assertIn(b'def orOpcode : Opcode := 24', opcode_mutation())

    def test_trivia(self):
        source, opcodes, storage = (extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                    extract.nested.STORAGE.read_bytes())
        self.assertEqual(extract.extract(source, opcodes, storage).split(b'def andOpcode', 1)[1],
                         extract.extract(source + b'\n// inert comment\n', opcodes, storage).split(b'def andOpcode', 1)[1])


if __name__ == '__main__':
    unittest.main()
