"""Require complete update observations, strict types and retained suffixes.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest
import native_wyhash_hash_checks as checks


def observation():
    return {'schema': 'oksolc.wyhash-hash.v1', 'endian': 'little', 'usize_bytes': 8,
        'size': 104, 'alignment': 8, 'offsets': [0, 8, 16, 40, 56, 48],
        'cases': [checks.expected_case(sizes, i) for i, sizes in enumerate(checks.LENGTHS)]}


class HashTests(unittest.TestCase):
    def test_complete(self):
        self.assertEqual(checks.check_observation(observation()), observation())

    def test_every_update_required(self):
        for case in range(len(checks.LENGTHS)):
            for step in range(6):
                bad = observation(); del bad['cases'][case]['steps'][step]
                with self.subTest(case=case, step=step), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_initialized_regions_and_lanes(self):
        original = observation()
        for ci, case in enumerate(original['cases']):
            for si, step in enumerate(case['steps']):
                for field in ('state', 'initialized'):
                    for at, value in enumerate(step[field]):
                        bad = copy.deepcopy(original)
                        bad['cases'][ci]['steps'][si][field][at] = 0 if value is None else value ^ 1
                        with self.subTest(case=ci, step=si, field=field, at=at), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_counts_and_types(self):
        for field in ('total', 'length'):
            for value in (True, -1, 2**64, '0'):
                bad = observation(); bad['cases'][0]['steps'][0][field] = value
                with self.subTest(field=field, value=value), self.assertRaises(ValueError): checks.check_observation(bad)
        bad = observation(); bad['cases'][0]['steps'][0]['extra'] = 0
        with self.assertRaises(ValueError): checks.check_observation(bad)

    def test_hash_and_retention(self):
        for ci in range(len(checks.LENGTHS)):
            for field in ('native_hash', 'repeated_hash', 'changed_a_hash', 'changed_b_hash', 'source_retained'):
                bad = observation()
                bad['cases'][ci][field] = False if field == 'source_retained' else bad['cases'][ci][field] ^ 1
                with self.subTest(case=ci, field=field), self.assertRaises(ValueError): checks.check_observation(bad)


if __name__ == '__main__':
    unittest.main()
