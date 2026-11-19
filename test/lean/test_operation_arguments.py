#!/usr/bin/env python3
"""Negative admission fixtures for native operation query observations.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest

from check_operation_arguments import check_profile, expected_cases


def fixture():
    cases = []
    for index, (kind, instruction, id, opcode, length, values) in enumerate(expected_cases()):
        pointer = 4096 + (8 if index == 528 else 0)
        cases.append(dict(kind=kind, instruction=instruction, id=id, opcode=opcode, input_pointer=pointer,
                          input_length=length, output_pointer=pointer if values is not None else None, values=values))
    return dict(schema='oksolc.operation-arguments-observations.v1', zigVersion='0.17.0', mode='Debug', backend='stage2_llvm', cases=cases)


class OperationArgumentsTests(unittest.TestCase):
    def test_complete_profiles(self):
        for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
            profile = fixture()
            profile['mode'] = mode
            check_profile(profile, mode)

    def test_metadata(self):
        for key, value in (('schema', 'old'), ('zigVersion', '0.15.0'), ('mode', 'ReleaseFast'), ('backend', 'stage2_aarch64')):
            profile = fixture()
            profile[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                check_profile(profile, 'Debug')
        with self.assertRaises(ValueError):
            check_profile({**fixture(), 'mode': 'ReleaseSmall'}, 'ReleaseSmall')

    def test_complete_ordered_inventory(self):
        for cases in (fixture()['cases'][:-1], list(reversed(fixture()['cases'])), fixture()['cases'] + [fixture()['cases'][0]]):
            with self.assertRaises(ValueError):
                check_profile({**fixture(), 'cases': cases}, 'Debug')

    def test_exact_fields(self):
        for index, key, value in ((0, 'kind', True), (0, 'instruction', None), (1, 'opcode', True),
                                  (0, 'id', 1), (0, 'input_length', True), (0, 'values', [1, 99]),
                                  (0, 'values', [99, True]), (1, 'values', []), (528, 'values', None)):
            profile = fixture()
            profile['cases'][index][key] = value
            with self.subTest(index=index, key=key), self.assertRaises(ValueError):
                check_profile(profile, 'Debug')

    def test_pointer_identity(self):
        for index, key, value in ((0, 'input_pointer', 0), (0, 'input_pointer', True), (0, 'input_pointer', 4097),
                                  (0, 'output_pointer', 4100), (1, 'output_pointer', 4096),
                                  (528, 'input_pointer', 4096), (528, 'output_pointer', None)):
            profile = fixture()
            profile['cases'][index][key] = value
            with self.subTest(index=index, key=key), self.assertRaises(ValueError):
                check_profile(profile, 'Debug')

    def test_missing_and_extra_fields(self):
        for container in ('profile', 'case'):
            profile = fixture()
            row = profile if container == 'profile' else profile['cases'][0]
            extra = copy.deepcopy(profile)
            (extra if container == 'profile' else extra['cases'][0])['extra'] = 0
            row.pop(next(iter(row)))
            for changed in (profile, extra):
                with self.assertRaises(ValueError):
                    check_profile(changed, 'Debug')


if __name__ == '__main__':
    unittest.main()
