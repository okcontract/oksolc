#!/usr/bin/env python3
"""Source closure and initializer controls for all RuleList literal shapes.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from collections import Counter
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_rule_literal_input as admission
from extract_compiler import Unsupported
from literal_input_mutations import canonical, variants


class LiteralInputAdmission(unittest.TestCase):
    def test_complete_nonempty_literal_inventory(self):
        checked = admission.check()
        self.assertEqual(checked['nonemptyLiteralCount'], 53)
        self.assertEqual(Counter(site['arity'] for site in checked['sites']), {1: 5, 2: 25, 3: 2})
        self.assertEqual(sum(bool(site['children']) for site in checked['sites']), 11)
        both = checked['sites'] + checked['scalarPairs']['sites']
        self.assertEqual(len({site['startByte'] for site in both}), 53)
        self.assertFalse(checked['completeNativeQueryAndGuardConnectionVerified'])
        self.assertFalse(checked['completeCallSiteClosureVerified'])
        self.assertFalse(checked['recursiveInductionVerified'])

    def test_each_site_reads_order_values_opcode_debug_and_try(self):
        source, *rest = admission.pairs.owner.inputs()
        for site in admission.admitted(source, *rest):
            original = source[site['startByte']:site['endByte']]
            admission.extract(source[:site['startByte']] + canonical(original) + source[site['endByte']:], *rest)
            for name, changed in variants(original):
                with self.subTest(site=site['site'], mutation=name), self.assertRaises(Unsupported):
                    admission.extract(source[:site['startByte']] + changed + source[site['endByte']:], *rest)

    def test_ignored_materialization_id_still_requires_its_read(self):
        source, *rest = admission.pairs.owner.inputs()
        for before in (b'materializeConstant(nested[0], constant, debug_data)',
                       b'materializeConstant(nested[1], constant, debug_data)'):
            self.assertEqual(source.count(before), 1)
            changed = source.replace(before, b'materializeConstant(0, constant, debug_data)')
            with self.subTest(before=before), self.assertRaises(Unsupported):
                admission.extract(b'// ' + before + b'\n' + changed, *rest)


if __name__ == '__main__':
    unittest.main()
