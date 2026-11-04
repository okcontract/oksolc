"""Reject corrupt paired key/ID assignment observations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import native_map_entry_checks as checks
from test_native_map_key import observation as key_observation


def observation():
    key = key_observation(); key['value_retained'] = False
    return {'schema': 'oksolc.expression-map-entry-assignment.v1', 'key': key, 'id': 4275878552}


class EntryTests(unittest.TestCase):
    def test_complete_pair(self):
        self.assertEqual(checks.check_observation(observation()), observation())

    def test_id_is_exact_word(self):
        for value in (37, 0, True, -1, 4275878553, 2**32, '4275878552'):
            changed = observation(); changed['id'] = value
            with self.subTest(value=value), self.assertRaises(ValueError): checks.check_observation(changed)

    def test_key_frame_and_slice(self):
        for field, value in (('value_retained', True), ('neighbor_retained', False), ('argument_pointer_retained', False),
                             ('arguments', [5, 17, 0]), ('data_words', [0, 0, 0, 0]), ('sequence_number', 0), ('frees', 0)):
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
        for target in ('entry', 'key'):
            changed = observation(); owner = changed if target == 'entry' else changed['key']; owner['schema'] = 'unknown'
            with self.assertRaises(ValueError): checks.check_observation(changed)

    def test_wrong_nested_type_and_flags(self):
        for value in (None, [], 'key', 0):
            changed = observation(); changed['key'] = value
            with self.assertRaises(ValueError): checks.check_observation(changed)
        for value in (None, 0, 1):
            changed = observation(); changed['key']['value_retained'] = value
            with self.assertRaises(ValueError): checks.check_observation(changed)


if __name__ == '__main__':
    unittest.main()
