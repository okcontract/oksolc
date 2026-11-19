"""Reject incomplete or misleading native probing observations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import native_map_probe_checks as checks


def observation():
    fp = 221
    def snapshot(metadata, size, available):
        return dict(metadata=metadata, size=size, available=available)
    return dict(schema='oksolc.expression-map-probe.v1', arch='aarch64', backend='stage2_llvm',
                hashes=[(93 << 57) + 7 + i*8 for i in range(4)],
                wrapped=snapshot([fp]+[0]*6+[fp], 2, 4), tombstone=snapshot([fp]+[0]*6+[1], 1, 5),
                reused=snapshot([fp]+[0]*6+[fp], 2, 4), exhausted=snapshot([1]*7+[fp], 1, 5),
                recycled=snapshot([fp]+[1]*6+[fp], 2, 4), hit=53, missed=None, hit_comparisons=1,
                miss_comparisons=1, reuse_index=7, recycle_index=0, found_existing=False)


class ProbeTests(unittest.TestCase):
    def test_complete(self):
        self.assertEqual(checks.check_observation(observation()), observation())

    def test_inventory(self):
        for field in observation():
            bad = observation(); del bad[field]
            with self.subTest(field=field), self.assertRaises(ValueError): checks.check_observation(bad)
        bad = observation(); bad['extra'] = True
        with self.assertRaises(ValueError): checks.check_observation(bad)

    def test_profile_and_hash(self):
        for field, value in (('schema', 'unknown'), ('arch', 'x86_64'), ('backend', 'stage2_aarch64'),
                             ('hashes', []), ('hashes', [True]*4), ('hashes', [2**64]*4),
                             ('hashes', [0]*4), ('hashes', [7, (1 << 57)+7, 7, 7])):
            bad = observation(); bad[field] = value
            with self.subTest(field=field), self.assertRaises(ValueError): checks.check_observation(bad)

    def test_every_metadata_byte_and_counter(self):
        for name in ('wrapped', 'tombstone', 'reused', 'exhausted', 'recycled'):
            for i in range(8):
                bad = observation(); bad[name]['metadata'][i] ^= 1
                with self.subTest(name=name, index=i), self.assertRaises(ValueError): checks.check_observation(bad)
            for field in ('size', 'available'):
                for wrong in (True, -1, 9):
                    bad = observation(); bad[name][field] = wrong
                    with self.subTest(name=name, field=field), self.assertRaises(ValueError): checks.check_observation(bad)
            bad = observation(); bad[name]['metadata'].pop()
            with self.assertRaises(ValueError): checks.check_observation(bad)

    def test_outcomes(self):
        for field, wrong in (('hit', None), ('missed', 37), ('found_existing', 0), ('found_existing', True),
                             ('hit_comparisons', True), ('hit_comparisons', 2), ('miss_comparisons', 0),
                             ('miss_comparisons', True), ('reuse_index', 0), ('recycle_index', 7)):
            bad = observation(); bad[field] = wrong
            with self.subTest(field=field), self.assertRaises(ValueError): checks.check_observation(bad)


if __name__ == '__main__':
    unittest.main()
