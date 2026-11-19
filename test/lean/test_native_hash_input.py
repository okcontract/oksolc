"""Check the exact native input-image inventory and reject corrupt captures.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import native_hash_input_checks as checks


def observation():
    return {'schema': 'oksolc.expression-hash-input.v1', 'endian': 'little', 'usize_bytes': 8,
            'scalar_bytes': [4, 1, 32, 4], 'cases': [
                {'length': n, 'inputs': checks.expected_inputs(n), 'native_hash': n, 'replayed_hash': n}
                for n in checks.LENGTHS]}


class HashInputTests(unittest.TestCase):
    def test_complete(self):
        self.assertEqual(checks.check_observation(observation()), observation())

    def test_profile(self):
        for field, wrong in (('schema', 'wrong'), ('endian', 'big'), ('usize_bytes', True),
                             ('usize_bytes', 4), ('scalar_bytes', [1, 1, 32, 4]), ('scalar_bytes', [4, True, 32, 4])):
            bad = observation(); bad[field] = wrong
            with self.subTest(field=field, wrong=wrong), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_inventory(self):
        for field in observation():
            bad = observation(); del bad[field]
            with self.subTest(field=field), self.assertRaises(ValueError): checks.check_observation(bad)
        for cases in ([], observation()['cases'][:-1], list(reversed(observation()['cases']))):
            bad = observation(); bad['cases'] = cases
            with self.assertRaises(ValueError): checks.check_observation(bad)
        for field in observation()['cases'][0]:
            bad = observation(); del bad['cases'][0][field]
            with self.subTest(field=field), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_byte_images(self):
        for chunk in range(5):
            for wrong in (True, -1, 256):
                bad = observation(); bad['cases'][2]['inputs'][chunk][0] = wrong
                with self.subTest(chunk=chunk, wrong=wrong), self.assertRaises(ValueError): checks.check_observation(bad)
            bad = observation(); bad['cases'][2]['inputs'][chunk] = bad['cases'][2]['inputs'][chunk][:-1]
            with self.assertRaises(ValueError): checks.check_observation(bad)
        bad = observation(); bad['cases'][0]['inputs'] = list(reversed(bad['cases'][0]['inputs']))
        with self.assertRaises(ValueError): checks.check_observation(bad)

    def test_hash_observation(self):
        for field in ('native_hash', 'replayed_hash'):
            for wrong in (True, -1, 2**64, 71):
                bad = observation(); bad['cases'][0][field] = wrong
                with self.subTest(field=field, wrong=wrong), self.assertRaises(ValueError): checks.check_observation(bad)
        # Matching observations alone do not certify a hash value or algorithm.
        value = observation(); value['cases'][0]['native_hash'] = value['cases'][0]['replayed_hash'] = 71
        self.assertEqual(checks.check_observation(value), value)


if __name__ == '__main__':
    unittest.main()
