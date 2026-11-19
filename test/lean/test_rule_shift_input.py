#!/usr/bin/env python3
"""Source admission controls for ordered shift-literal input connections.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_rule_shift_input as admission
from extract_compiler import Unsupported


class ShiftInputAdmission(unittest.TestCase):
    def test_current_source_and_shared_program(self):
        checked = admission.check()
        self.assertEqual(len(checked['sites']), 4)
        self.assertEqual([site['constantFirst'] for site in checked['sites']], [False, True, True, True])
        self.assertFalse(checked['completeNativeQueryAndGuardConnectionVerified'])
        self.assertFalse(checked['completeRecursiveConstructorsVerified'])

    def test_order_index_opcode_and_children(self):
        source, *rest = admission.owner.inputs()
        for _, _, _, _, _, expression in admission.SITES:
            # Use the hash-bound source span, preserving the owning full body.
            selected = next(site for site in admission.admitted(source, *rest)
                            if admission.lex(source[site['startByte']:site['endByte']].decode()) == admission.lex(expression))
            original = source[selected['startByte']:selected['endByte']]
            operand = b'arguments[1]' if b'arguments[1]' in original else b'arguments[0]'
            for changed in (
                original.replace(operand, b'arguments[2]'),
                original.replace(b'.SHL', b'.SHR') if b'.SHL' in original else original.replace(b'.SHR', b'.SHL'),
                original.replace(b'try classes.makeConstant', b'classes.makeConstant'),
                original.replace(b'debug_data', b'null'),
            ):
                with self.subTest(site=selected['site'], changed=changed), self.assertRaises(Unsupported):
                    admission.extract(source[:selected['startByte']] + changed + source[selected['endByte']:], *rest)

    def test_reversed_initializer_and_guard(self):
        source, *rest = admission.owner.inputs()
        for before, after in (
            (b'arguments[1], try classes.makeConstant(1, debug_data)', b'try classes.makeConstant(1, debug_data), arguments[1]'),
            (b'try classes.makeConstant(power, debug_data), arguments[1]', b'arguments[1], try classes.makeConstant(power, debug_data)'),
            (b'if (base == 2 and evm_version.hasBitwiseShifting())', b'if (base == 2)'),
        ):
            self.assertEqual(source.count(before), 1)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                admission.extract(source.replace(before, after), *rest)

    def test_comment_decoy(self):
        source, *rest = admission.owner.inputs()
        before = b'try classes.makeConstant(power, debug_data), arguments[1]'
        changed = source.replace(before, b'arguments[1], try classes.makeConstant(power, debug_data)')
        with self.assertRaises(Unsupported):
            admission.extract(b'// ' + before + b'\n' + changed, *rest)


if __name__ == '__main__':
    unittest.main()
