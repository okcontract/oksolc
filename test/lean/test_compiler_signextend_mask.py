#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admission boundaries for complete native sign-extension mask removal.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_signextend_mask as extract
from extract_compiler import Unsupported


def opcode_mutation():
    opcodes = extract.nested.OPCODES.read_bytes()
    before, after = b'SIGNEXTEND = 0x0b,', b'SIGNEXTEND = 0x0c,'
    if opcodes.count(before) != 1:
        raise ValueError('opcode mutation must target exactly one binding')
    return extract.extract(extract.nested.SOURCE.read_bytes(), opcodes.replace(before, after),
                           extract.nested.STORAGE.read_bytes())


class SignExtendMaskTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                        extract.nested.STORAGE.read_bytes()), extract.OUTPUT.read_bytes())

    def test_semantic_mutations_reject(self):
        for before, after in [
            ('classes.knownConstantValue(constant_id)', 'classes.knownConstantValue(sign_extend_id)'),
            ('classes.operationArguments(sign_extend_id, .SIGNEXTEND)', 'classes.operationArguments(sign_extend_id, .SHR)'),
            ('sign_extend.len != 2', 'sign_extend.len < 2'),
            ('classes.knownConstantValue(sign_extend[0])', 'classes.knownConstantValue(sign_extend[1])'),
            ('if (byte_index >= 31)', 'if (byte_index > 31)'),
            ('const bit_count: u8', 'const bit_count: u16'),
            ('@intCast((byte_index + 1) * 8)', '@truncate((byte_index + 1) * 8)'),
            ('(byte_index + 1) * 8', '(byte_index + 1) * 7'),
            ('(byte_index + 1) * 8', '(byte_index +% 1) * 8'),
            ('(@as(u256, 1) << bit_count) - 1', '(@as(u256, 1) >> bit_count) - 1'),
            ('(@as(u256, 1) << bit_count) - 1', '(@as(u256, 1) << bit_count) -% 1'),
            ('(mask & low_mask) != mask', '(mask & low_mask) != low_mask'),
            ('materializeConstant(constant_id, mask, debug_data)', 'materializeConstant(sign_extend_id, mask, debug_data)'),
            ('&.{ materialized_mask, sign_extend[1] }', '&.{ sign_extend[1], materialized_mask }'),
            ('makeOperation(.AND, &.{ materialized_mask', 'makeOperation(.OR, &.{ materialized_mask'),
        ]:
            source = extract.nested.SOURCE.read_bytes()
            self.assertIn(before.encode(), source)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(source.replace(before.encode(), after.encode()), extract.nested.OPCODES.read_bytes(),
                                extract.nested.STORAGE.read_bytes())

    def test_opcode_is_executable(self):
        self.assertIn(b'def signextendOpcode : Opcode := 12', opcode_mutation())

    def test_trivia(self):
        source, opcodes, storage = (extract.nested.SOURCE.read_bytes(), extract.nested.OPCODES.read_bytes(),
                                    extract.nested.STORAGE.read_bytes())
        self.assertEqual(extract.extract(source, opcodes, storage).split(b'def signextendOpcode', 1)[1],
                         extract.extract(source + b'\n// inert comment\n', opcodes, storage).split(b'def signextendOpcode', 1)[1])


if __name__ == '__main__':
    unittest.main()
