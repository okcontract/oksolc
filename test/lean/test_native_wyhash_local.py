"""Reject incomplete or changed partial-local finalization captures.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import native_wyhash_local_checks as checks


def observation():
    return {'schema': 'oksolc.wyhash-local.v1', 'endian': 'little', 'usize_bytes': 8,
            'size': 104, 'alignment': 8, 'offsets': [0, 8, 16, 40, 56, 48],
            'cases': [checks.expected_case(length, index) for index, length in enumerate(checks.LENGTHS)]}


class LocalTests(unittest.TestCase):
    def test_complete(self):
        self.assertEqual(checks.check_observation(observation()), observation())

    def test_profile(self):
        for key, wrong in (('schema', 'wrong'), ('endian', 'big'), ('size', True), ('size', 112),
                           ('alignment', 4), ('usize_bytes', 4), ('offsets', [0, 8, 16, 40, 48, 56])):
            bad = observation(); bad[key] = wrong
            with self.subTest(key=key), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_inventory(self):
        for key in observation():
            bad = observation(); del bad[key]
            with self.subTest(key=key), self.assertRaises(ValueError): checks.check_observation(bad)
        for cases in ([], observation()['cases'][:-1], list(reversed(observation()['cases']))):
            bad = observation(); bad['cases'] = cases
            with self.assertRaises(ValueError): checks.check_observation(bad)
        for key in observation()['cases'][0]:
            bad = observation(); del bad['cases'][0][key]
            with self.subTest(key=key), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_initialization(self):
        for index, wrong in ((0, True), (0, -1), (0, 256), (0, None), (1, 0), (47, None)):
            bad = observation(); bad['cases'][0]['initialized'][index] = wrong
            with self.subTest(index=index, wrong=wrong), self.assertRaises(ValueError): checks.check_observation(bad)
        bad = observation(); bad['cases'][0]['state'][0] ^= 1
        with self.assertRaises(ValueError): checks.check_observation(bad)

    def test_finalization(self):
        for key in ('length', 'total', 'native_hash', 'repeated_hash', 'changed_a_hash', 'changed_b_hash'):
            for wrong in (True, -1, 2**64, 0):
                bad = observation(); bad['cases'][0][key] = wrong
                with self.subTest(key=key, wrong=wrong), self.assertRaises(ValueError): checks.check_observation(bad)
        bad = observation(); bad['cases'][0]['source_retained'] = False
        with self.assertRaises(ValueError): checks.check_observation(bad)


if __name__ == '__main__':
    unittest.main()
