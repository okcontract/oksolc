"""Reject corrupt native table observations, including argument-only key changes.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import native_map_table_checks as checks
from test_native_map_key import observation as key_observation


def observation():
    key = key_observation(); key.update(value_retained=False, count=2)
    return {'schema': 'oksolc.expression-map-table.v1', 'first': key, 'first_id': 4275878552, 'second_id': 53,
            'lookup_first': 4275878552, 'lookup_second': 53, 'used_slots': 2, 'available': 4,
            'second_arguments': [5, 17, 4294967294], 'second_key_retained': True, 'second_pointer_retained': True,
            'both_new': True, 'distinct_slots': True}


class TableTests(unittest.TestCase):
    def test_complete_table(self):
        self.assertEqual(checks.check_observation(observation()), observation())

    def test_exact_counts_and_ids(self):
        for field, expected in observation().items():
            if type(expected) is not int: continue
            for value in (expected + 1, -1, True, None, str(expected), 2**64):
                changed = observation(); changed[field] = value
                with self.subTest(field=field, value=value), self.assertRaises(ValueError): checks.check_observation(changed)

    def test_flags(self):
        for field, expected in observation().items():
            if type(expected) is not bool: continue
            for value in (False, 0, 1, None):
                changed = observation(); changed[field] = value
                with self.subTest(field=field, value=value), self.assertRaises(ValueError): checks.check_observation(changed)

    def test_argument_contents(self):
        for value in ([5, 17, 4294967295], [5, 17], [True, 17, 4294967294], None, {}, 'arguments'):
            changed = observation(); changed['second_arguments'] = value
            with self.subTest(value=value), self.assertRaises(ValueError): checks.check_observation(changed)

    def test_first_entry_and_lifetime(self):
        for field, value in (('arguments', [5, 17, 4294967294]), ('argument_pointer_retained', False),
                             ('neighbor_retained', False), ('allocations', 2), ('frees', 0), ('count', 1)):
            changed = observation(); changed['first'][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError): checks.check_observation(changed)

    def test_inventory_and_schema(self):
        for field in observation():
            changed = observation(); del changed[field]
            with self.assertRaises(ValueError): checks.check_observation(changed)
        for field, value in (('extra', 0), ('schema', 'unknown'), ('first', None)):
            changed = observation(); changed[field] = value
            with self.assertRaises(ValueError): checks.check_observation(changed)


if __name__ == '__main__':
    unittest.main()
