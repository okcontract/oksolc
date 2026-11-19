"""Reject unsupported scan profiles and incomplete native equality observations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import native_map_candidate_checks as checks


def observation():
    return {'schema': 'oksolc.expression-map-equality.v1', 'arch': 'aarch64', 'backend': 'stage2_llvm',
            'endian': 'little', 'scan_bytes': 16, 'usize_bytes': 8, 'unique_u32': True, 'fuzz': False,
            'cases': [{'length': n, 'alias_equal': True, 'copied_equal': True, 'different_length': False,
                       'changed_bytes_rejected': 4*n, 'scalar_changes_rejected': [True]*4} for n in checks.LENGTHS],
            'collision': {'same_start': True, 'same_fingerprint': True, 'first': 37, 'second': 53, 'absent': None, 'size': 2}}


class CandidateTests(unittest.TestCase):
    def test_complete(self):
        self.assertEqual(checks.check_observation(observation()), observation())

    def test_profile(self):
        for field, value in (('schema', 'unknown'), ('arch', 'x86_64'), ('backend', 'stage2_aarch64'),
                             ('endian', 'big'), ('scan_bytes', 32), ('scan_bytes', None), ('scan_bytes', True),
                             ('usize_bytes', 4), ('unique_u32', 1), ('fuzz', True)):
            bad = observation(); bad[field] = value
            with self.subTest(field=field, value=value), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_every_boundary_and_lane(self):
        for i in range(len(checks.LENGTHS)):
            for field, value in (('length', -1), ('length', True), ('changed_bytes_rejected', 4*checks.LENGTHS[i]+1),
                                 ('changed_bytes_rejected', True), ('alias_equal', False), ('copied_equal', 1),
                                 ('different_length', True), ('scalar_changes_rejected', [True, True, False, True]),
                                 ('scalar_changes_rejected', [True]*3)):
                bad = observation(); bad['cases'][i][field] = value
                with self.subTest(case=i, field=field), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_collisions(self):
        for field, value in (('same_start', False), ('same_fingerprint', 1), ('first', 53), ('second', 37),
                             ('absent', 0), ('size', True), ('size', 1)):
            bad = observation(); bad['collision'][field] = value
            with self.subTest(field=field), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_complete_inventory(self):
        for field in observation():
            bad = observation(); del bad[field]
            with self.subTest(field=field), self.assertRaises(ValueError): checks.check_observation(bad)
        for value in ([], observation()['cases'][:-1], list(reversed(observation()['cases'])), None):
            bad = observation(); bad['cases'] = value
            with self.assertRaises(ValueError): checks.check_observation(bad)
        bad = observation(); bad['extra'] = True
        with self.assertRaises(ValueError): checks.check_observation(bad)


if __name__ == '__main__':
    unittest.main()
