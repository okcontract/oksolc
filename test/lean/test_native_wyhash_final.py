"""Require complete finalization boundaries and their initialized-byte evidence.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import native_wyhash_final_checks as checks


def observation():
    return {'schema': 'oksolc.wyhash-final.v1', 'endian': 'little', 'usize_bytes': 8,
            'size': 104, 'alignment': 8, 'offsets': [0, 8, 16, 40, 56, 48],
            'cases': [checks.local.expected_case(length, length) for length in range(49)]}


class FinalTests(unittest.TestCase):
    def test_complete(self):
        self.assertEqual(checks.check_observation(observation()), observation())

    def test_boundaries_required(self):
        for length in (0, 15, 16, 17, 31, 32, 33, 47, 48):
            bad = observation(); del bad['cases'][length]
            with self.subTest(length=length), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_initialized_regions(self):
        for length, offset, wrong in ((0, 32, None), (1, 0, None), (1, 1, 0), (15, 47, None),
                                      (16, 47, 0), (32, 31, None), (48, 47, None)):
            bad = observation(); bad['cases'][length]['initialized'][offset] = wrong
            with self.subTest(length=length, offset=offset), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_boundary_results(self):
        for length in (0, 16, 32, 48):
            for field in ('native_hash', 'repeated_hash', 'changed_a_hash', 'changed_b_hash'):
                bad = observation(); bad['cases'][length][field] ^= 1
                with self.subTest(length=length, field=field), self.assertRaises(ValueError): checks.check_observation(bad)


if __name__ == '__main__':
    unittest.main()
