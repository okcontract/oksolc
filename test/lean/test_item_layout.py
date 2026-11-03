#!/usr/bin/env python3
"""Admission controls for the captured nominal item allocation type.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest
from capture_item_layout import check_profile
from generate_item_layout import generate, OUTPUT


def fixture():
    version = {'major': 27, 'minor': 0, 'patch': 1, 'pre': None, 'build': None}
    return {'schema': 'oksolc.assembly-item-layout.v1', 'zigVersion': '0.17.0', 'arch': 'aarch64',
            'os': 'macos', 'osVersionRange': {'semver': {'min': dict(version), 'max': dict(version)}},
            'abi': 'none', 'cpu': 'apple_m3', 'cpuFeatures': [0] * 5, 'endianness': 'little',
            'mode': 'ReleaseFast', 'backend': 'stage2_llvm', 'pointerBits': 64,
            'name': 'libevmasm.assembly_item.AssemblyItem', 'bytes': 224, 'alignment': 16}


class LayoutTests(unittest.TestCase):
    def test_current_model_and_modes(self):
        for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
            record = fixture()
            record['mode'] = mode
            check_profile(record, OUTPUT.read_bytes())

    def test_other_types_and_targets_reject(self):
        for key, value in (('name', 'other.AssemblyItem'), ('arch', 'x86_64'), ('os', 'linux'),
                           ('endianness', 'big'), ('pointerBits', 32), ('zigVersion', '0.15.0'),
                           ('backend', 'stage2_aarch64'), ('mode', 'ReleaseSmall'), ('abi', 'gnu')):
            record = fixture()
            record[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                generate(record)

    def test_malformed_extent_rejects(self):
        for size, alignment in ((0, 1), (224, 0), (224, 3), (225, 16), (8, 16), (2**64, 16), (True, 1), (224, True)):
            record = fixture()
            record.update(bytes=size, alignment=alignment)
            with self.subTest(size=size, alignment=alignment), self.assertRaises(ValueError):
                generate(record)

    def test_stale_or_substituted_extent_rejects(self):
        for size, alignment in ((240, 16), (224, 8)):
            record = fixture()
            record.update(bytes=size, alignment=alignment)
            self.assertNotEqual(generate(record), OUTPUT.read_bytes())
            with self.assertRaises(ValueError):
                check_profile(record, OUTPUT.read_bytes())

    def test_metadata_and_unknown_fields_reject(self):
        for key, value in (('cpu', 'injected"name'), ('cpuFeatures', [2**64]), ('cpuFeatures', [False]),
                           ('osVersionRange', {}), ('unknown', 1)):
            record = fixture()
            record[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                generate(record)
        record = copy.deepcopy(fixture())
        record['osVersionRange']['semver']['max']['major'] = 1
        with self.assertRaises(ValueError):
            generate(record)


if __name__ == '__main__':
    unittest.main()
