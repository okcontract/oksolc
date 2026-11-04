#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admission boundaries for complete native address-mask matching.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_address_mask as extract
from extract_compiler import Unsupported


def opcode_mutation():
    opcodes = extract.nested.OPCODES.read_bytes()
    before, after = b'CALLER = 0x33,', b'CALLER = 0x34,'
    if opcodes.count(before) != 1:
        raise ValueError('opcode mutation must target exactly one binding')
    return extract.extract(extract.nested.SOURCE.read_bytes(), opcodes.replace(before, after),
                           extract.nested.STORAGE.read_bytes())


class AddressMaskTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                        extract.nested.STORAGE.read_bytes()), extract.OUTPUT.read_bytes())

    def test_semantic_mutations_reject(self):
        for before, after in [
            ('classes.knownConstantValue(mask_id) != ((@as(u256, 1) << 160)', 'classes.knownConstantValue(operation_id) != ((@as(u256, 1) << 160)'),
            ('((@as(u256, 1) << 160) - 1)', '((@as(u256, 1) << 159) - 1)'),
            ('((@as(u256, 1) << 160) - 1)', '((@as(u256, 1) << 160) + 1)'),
            ('.ADDRESS, .CALLER, .ORIGIN, .COINBASE', '.ADDRESS, .ORIGIN, .CALLER, .COINBASE'),
            ('.ADDRESS, .CALLER, .ORIGIN, .COINBASE', '.ADDRESS, .CALLER, .ORIGIN'),
            ('.ADDRESS, .CALLER, .ORIGIN, .COINBASE', '.ADDRESS, .CALLER, .ORIGIN, .BALANCE'),
            ('classes.operationArguments(operation_id, instruction)', 'classes.operationArguments(mask_id, instruction)'),
            ('if (arguments.len == 0) return instruction;', 'if (arguments.len == 1) return instruction;'),
            ('if (arguments.len == 0) return instruction;', 'if (arguments.len == 0) return .ADDRESS;'),
        ]:
            source = extract.nested.SOURCE.read_bytes()
            self.assertIn(before.encode(), source)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(source.replace(before.encode(), after.encode()), extract.nested.OPCODES.read_bytes(),
                                extract.nested.STORAGE.read_bytes())

    def test_opcode_is_executable(self):
        self.assertIn(b'def addressOpcodes : List Opcode := [48, 52, 50, 65]', opcode_mutation())

    def test_trivia(self):
        source, opcodes, storage = (extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                    extract.nested.STORAGE.read_bytes())
        self.assertEqual(extract.extract(source, opcodes, storage).split(b'def addressOpcodes', 1)[1],
                         extract.extract(source + b'\n// inert comment\n', opcodes, storage).split(b'def addressOpcodes', 1)[1])


if __name__ == '__main__':
    unittest.main()
