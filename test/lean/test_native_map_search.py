"""Reject wrong receiver branches, hidden hash calls and incomplete captures.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import native_map_search_checks as checks


def observation():
    values = (('empty-unallocated', 0, 0, 0, False, 0, 0, None), ('empty-allocated', 8, 0, 6, True, 0, 0, None),
              ('hit', 8, 1, 5, True, 1, 1, 37), ('miss', 8, 1, 5, True, 1, 0, None))
    return dict(schema='oksolc.expression-map-caller.v1', hashes=[7, 1], cases=[
        dict(name=n, capacity=c, size=s, available=a, metadata_present=m, hash_calls=h, comparisons=e, result=r, unchanged=True)
        for n,c,s,a,m,h,e,r in values])


class SearchTests(unittest.TestCase):
    def test_complete(self):
        self.assertEqual(checks.check_observation(observation()), observation())
        value = observation(); value['hashes'] = [7, 15]; value['cases'][3]['comparisons'] = 1
        self.assertEqual(checks.check_observation(value), value)

    def test_inventory(self):
        for key in observation():
            bad = observation(); del bad[key]
            with self.subTest(key=key), self.assertRaises(ValueError): checks.check_observation(bad)
        for cases in ([], observation()['cases'][:-1], list(reversed(observation()['cases']))):
            bad = observation(); bad['cases'] = cases
            with self.assertRaises(ValueError): checks.check_observation(bad)
        for i in range(4):
            for key in observation()['cases'][i]:
                bad = observation(); del bad['cases'][i][key]
                with self.subTest(case=i, key=key), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_counters_and_outcomes(self):
        for i in range(4):
            for key in ('capacity', 'size', 'available', 'hash_calls', 'comparisons'):
                for wrong in (True, -1, 9):
                    bad = observation(); bad['cases'][i][key] = wrong
                    with self.subTest(case=i, key=key), self.assertRaises(ValueError): checks.check_observation(bad)
            for key, wrong in (('unchanged', False), ('unchanged', 1), ('result', 53), ('metadata_present', 1)):
                bad = observation(); bad['cases'][i][key] = wrong
                with self.subTest(case=i, key=key), self.assertRaises(ValueError): checks.check_observation(bad)
        bad = observation(); bad['cases'][0]['hash_calls'] = 1
        with self.assertRaises(ValueError): checks.check_observation(bad)

    def test_hash_profile(self):
        for hashes in ([], [True, 1], [-1, 1], [7, 2**64]):
            bad = observation(); bad['hashes'] = hashes
            with self.assertRaises(ValueError): checks.check_observation(bad)
        bad = observation(); bad['hashes'] = [7, 15]
        with self.assertRaises(ValueError): checks.check_observation(bad)


if __name__ == '__main__':
    unittest.main()
