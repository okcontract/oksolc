"""Reject corrupt observations of the selected native new-slot route.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import native_map_insertion_checks as checks
from test_native_map_key import observation as key_observation


def observation():
    key = key_observation(); key.update(value_retained=False, count=1)
    return {'schema': 'oksolc.expression-map-new-slot.v1', 'key': key, 'id': 4275878552,
            'lookup_id': 4275878552, 'index': 5, 'fingerprint': 2, 'metadata_before': 0,
            'metadata_after': 130, 'available_before': 6, 'available_after': 5,
            'count_before': 0, 'found_existing': False, 'pointers_retained': True}


class InsertionTests(unittest.TestCase):
    def test_complete_publication(self):
        self.assertEqual(checks.check_observation(observation()), observation())

    def test_exact_counters_metadata_and_entry(self):
        for field, expected in observation().items():
            if type(expected) is not int: continue
            for value in (expected + 1, -1, True, None, str(expected), 2**64):
                changed = observation(); changed[field] = value
                with self.subTest(field=field, value=value), self.assertRaises(ValueError): checks.check_observation(changed)

    def test_result_flags(self):
        for field in ('found_existing', 'pointers_retained'):
            for value in (not observation()[field], 0, 1, None):
                changed = observation(); changed[field] = value
                with self.subTest(field=field, value=value), self.assertRaises(ValueError): checks.check_observation(changed)

    def test_key_frame_and_slice(self):
        for field, value in (('count', 2), ('value_retained', True), ('neighbor_retained', False),
                             ('argument_pointer_retained', False), ('arguments', [5, 17, 0]), ('frees', 0)):
            changed = observation(); changed['key'][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError): checks.check_observation(changed)

    def test_complete_inventory(self):
        for field in observation():
            changed = observation(); del changed[field]
            with self.assertRaises(ValueError): checks.check_observation(changed)
        for field in observation()['key']:
            changed = observation(); del changed['key'][field]
            with self.assertRaises(ValueError): checks.check_observation(changed)
        changed = observation(); changed['extra'] = 0
        with self.assertRaises(ValueError): checks.check_observation(changed)

    def test_strict_schemas(self):
        for target in ('insertion', 'key'):
            changed = observation(); owner = changed if target == 'insertion' else changed['key']; owner['schema'] = 'unknown'
            with self.assertRaises(ValueError): checks.check_observation(changed)

    def test_wrong_nested_type(self):
        for value in (None, [], 'key', 0):
            changed = observation(); changed['key'] = value
            with self.assertRaises(ValueError): checks.check_observation(changed)


if __name__ == '__main__':
    unittest.main()
