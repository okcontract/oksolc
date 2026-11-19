#!/usr/bin/env python3
"""Fail-closed source controls for the scalar pair literal closure.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_rule_pair_input as admission
from extract_compiler import Unsupported
from literal_input_mutations import canonical, variants


class PairInputAdmission(unittest.TestCase):
    def test_complete_scalar_scope(self):
        checked = admission.check()
        self.assertEqual(len(checked['sites']), 21)
        self.assertEqual(sum(bool(site['children']) for site in checked['sites']), 14)
        self.assertFalse(checked['completeNativeQueryAndGuardConnectionVerified'])
        self.assertFalse(checked['completeRecursiveConstructorsVerified'])

    def test_each_site_order_opcode_value_debug_and_try(self):
        source, *rest = admission.owner.inputs()
        sites = admission.admitted(source, *rest)
        for site in sites:
            original = source[site['startByte']:site['endByte']]
            tokens = admission.lex(original.decode())
            # Preserve original trailing commas, so formatting changes cannot
            # explain a negative result. The unchanged rendering must admit.
            admission.extract(source[:site['startByte']] + canonical(original) + source[site['endByte']:], *rest)
            for name, changed in variants(original):
                with self.subTest(site=site['site'], mutation=name):
                    self.assertNotEqual(admission.lex(changed.decode()), tokens)
                    with self.assertRaises(Unsupported):
                        admission.extract(source[:site['startByte']] + changed + source[site['endByte']:], *rest)

    def test_indexed_input_is_not_scalar_and_comments_do_not_admit(self):
        source, *rest = admission.owner.inputs()
        original = b'&.{ left, masked.expression }'
        self.assertEqual(source.count(original), 1)
        changed = source.replace(original, b'&.{ arguments[0], masked.expression }')
        with self.assertRaises(Unsupported):
            admission.extract(b'// ' + original + b'\n' + changed, *rest)


if __name__ == '__main__':
    unittest.main()
