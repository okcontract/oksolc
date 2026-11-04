"""Check native key admission and reject corrupted assignment observations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
from pathlib import Path
import unittest
from unittest.mock import patch
import native_map_key_checks as checks
from test_map_bucket_layout import fixture

LIB = Path('/synthetic-zig-lib')


def observation():
    return {'schema': 'oksolc.expression-map-key-assignment.v1', 'item_type': 2, 'instruction': 171,
        'data_words': [3, 5, 7, 11], 'arguments': [5, 17, 4294967295], 'argument_count': 3,
        'argument_pointer_retained': True, 'sequence_number': 305419896, 'value_retained': True,
        'neighbor_retained': True, 'capacity': 8, 'count': 2, 'attempts': 1, 'allocations': 1, 'frees': 1}


class KeyTests(unittest.TestCase):
    def setUp(self):
        # These synthetic captures test rendering, not native source admission.
        # The acceptance harness separately checks the real pinned library.
        binding = patch.object(checks.admission, 'source_binding', return_value={})
        binding.start()
        self.addCleanup(binding.stop)

    def test_complete_assignment(self):
        self.assertEqual(checks.check_observation(observation()), observation())

    def test_fields_and_frames(self):
        for field, value in (('item_type', 1), ('instruction', 0), ('sequence_number', 0), ('data_words', [3, 5, 7, 0]),
                             ('arguments', [5, 17, 0]), ('argument_count', 2), ('argument_pointer_retained', False),
                             ('value_retained', False), ('neighbor_retained', False), ('frees', 0)):
            changed = observation(); changed[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError): checks.check_observation(changed)

    def test_strict_fields(self):
        for field in observation():
            changed = observation(); del changed[field]
            with self.assertRaises(ValueError): checks.check_observation(changed)
        changed = observation(); changed['extra'] = 0
        with self.assertRaises(ValueError): checks.check_observation(changed)

    def test_boolean_numbers_and_nonboolean_flags(self):
        for field in ('instruction', 'count', 'allocations', 'argument_count'):
            changed = observation(); changed[field] = True
            with self.assertRaises(ValueError): checks.check_observation(changed)
        changed = observation(); changed['argument_pointer_retained'] = 1
        with self.assertRaises(ValueError): checks.check_observation(changed)
        changed = observation(); changed['data_words'][0] = True
        with self.assertRaises(ValueError): checks.check_observation(changed)

    def test_key_layout_complete_and_order_independent(self):
        record = fixture(); expected = checks.admission.key_layout(record, LIB)
        self.assertEqual(expected, checks.admission.KEY_OUTPUT.read_bytes())
        record['fields'].reverse()
        self.assertEqual(expected, checks.admission.key_layout(record, LIB))

    def test_valid_layout_change_changes_admission(self):
        record = fixture()
        for field in record['fields']:
            if field['name'] in ('item_type', 'sequence_number'): field['offset'] = 100 - field['offset']
        self.assertNotEqual(checks.admission.key_layout(record, LIB), checks.admission.KEY_OUTPUT.read_bytes())

    def test_key_layout_rejects_corrupt_or_mutable_fields(self):
        source = fixture()
        for name, field, value in (('arguments', 'type', '[]u32'), ('arguments', 'bytes', 8),
                                   ('data', 'offset', 16), ('instruction', 'offset', True)):
            record = copy.deepcopy(source)
            next(f for f in record['fields'] if f['name'] == name)[field] = value
            with self.subTest(name=name, field=field), self.assertRaises(ValueError): checks.admission.key_layout(record, LIB)


if __name__ == '__main__':
    unittest.main()
