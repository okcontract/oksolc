"""Reject corrupted native capacity requests and allocator outcomes.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest
import native_map_capacity_checks as checks


def observation(count):
    capacity = checks.COUNTS[count]
    return {'schema': 'oksolc.expression-map-capacity.v1', 'requested_count': count,
            'outcome': 'OutOfMemory' if count else None,
            'request': {'base': 0, 'bytes': checks.buckets.geometry(capacity)[2] if count else 0, 'alignment': 16 if count else 0},
            'capacity': 0, 'available': 0, 'count': 0, 'metadata_null': True, 'unlocked': True,
            'attempts': int(count != 0), 'allocations': 0, 'frees': 0, 'resizes': 0, 'remaps': 0}


class CapacityRequestTests(unittest.TestCase):
    def test_complete_boundaries(self):
        for count, capacity in checks.COUNTS.items():
            self.assertEqual(checks.check_request(observation(count), count)['capacityFromRequest'], capacity)

    def test_no_growth_is_distinct_from_oom(self):
        record = observation(0); record['outcome'] = 'OutOfMemory'
        with self.assertRaises(ValueError): checks.check_request(record, 0)
        record = observation(1); record['outcome'] = None
        with self.assertRaises(ValueError): checks.check_request(record, 1)

    def test_wrong_extent_or_identity(self):
        for field, value in (('bytes', 1136), ('base', 4096), ('alignment', 8), ('bytes', True)):
            record = observation(1); record['request'][field] = value
            with self.assertRaises(ValueError): checks.check_request(record, 1)

    def test_original_map_and_effects(self):
        for field, value in (('capacity', 8), ('available', 6), ('count', 1), ('metadata_null', False),
                             ('unlocked', False), ('attempts', 0), ('allocations', 1), ('frees', 1), ('resizes', 1), ('remaps', 1)):
            record = observation(1); record[field] = value
            with self.assertRaises(ValueError): checks.check_request(record, 1)

    def test_strict_inventory_and_counts(self):
        source = observation(1)
        for key in source:
            record = copy.deepcopy(source); del record[key]
            with self.assertRaises(ValueError): checks.check_request(record, 1)
        for count in (True, 0, 7):
            record = observation(1); record['requested_count'] = count
            with self.assertRaises(ValueError): checks.check_request(record, 1)
        record = observation(1); record['extra'] = 0
        with self.assertRaises(ValueError): checks.check_request(record, 1)


if __name__ == '__main__':
    unittest.main()
