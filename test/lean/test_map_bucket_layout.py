#!/usr/bin/env python3
"""Reject incomplete or inconsistent native bucket allocation captures.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean/zig_air'))
import generate_map_bucket_layout as admission
from test_item_layout import fixture as target_fixture


def fixture():
    target = {**target_fixture(), 'schema': 'oksolc.expression-key-layout.v1', 'name': admission.KEY,
              'bytes': 64, 'alignment': 16}
    fields = [{'name': name, 'type': native, 'offset': offset, 'bytes': size, 'alignment': alignment}
              for name, native, offset, size, alignment in (
                  ('item_type', 'libevmasm.assembly_item.AssemblyItemType', 48, 4, 4),
                  ('instruction', 'u8', 56, 1, 1), ('data', 'u256', 0, 32, 16),
                  ('arguments', '[]const u32', 32, 16, 8), ('sequence_number', 'u32', 52, 4, 4))]
    cases = []
    for i, (count, capacity, keys, values, total) in enumerate(((1, 8, 32, 544, 576),
            (7, 16, 48, 1072, 1136), (25, 32, 64, 2112, 2240), (100, 128, 160, 8352, 8864))):
        base, index = 4096 * (i + 1), i + 1
        allocation = {'base': base, 'bytes': total, 'alignment': 16}
        cases.append({'requested_count': count, 'oom_error': 'OutOfMemory',
            'oom_request': {'base': 0, 'bytes': total, 'alignment': 16}, 'oom_capacity': 0, 'oom_metadata': 0,
            'reserve_error': None, 'insert_error': None, 'allocation': allocation,
            'capacity': capacity, 'metadata': base + 24, 'metadata_cleared': True, 'available': capacity * 80 // 100, 'empty_lookup': True, 'index': index, 'key_pointer': base + keys + index * 64,
            'value_pointer': base + values + index * 4, 'value': 37, 'attempts': 2, 'allocations': 1,
            'frees': 1, 'resizes': 0, 'remaps': 0, 'released': allocation.copy()})
    return {'schema': 'oksolc.expression-map-buckets.v1', 'target': target, 'fields': fields,
        'metadata': {'name': admission.MAP + '.Metadata', 'bytes': 1, 'alignment': 1, 'bits': 8, 'backing': 'u8', 'fingerprint_offset': 0, 'used_offset': 7},
        'value': {'name': 'u32', 'bytes': 4, 'alignment': 4}, 'cases': cases}


class BucketLayoutTests(unittest.TestCase):
    def test_complete_modes_and_field_order(self):
        for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
            record = fixture(); record['target']['mode'] = mode; record['fields'].reverse()
            self.assertEqual([r['bytes'] for r in admission.check_profile(record)], [576, 1136, 2240, 8864])

    def test_packed_metadata(self):
        for field, changed in (('bits', 16), ('backing', 'i8'), ('fingerprint_offset', 1), ('used_offset', 0), ('bits', True)):
            record = fixture(); record['metadata'][field] = changed
            with self.assertRaises(ValueError): admission.check_profile(record)

    def test_metadata_clearing(self):
        for changed in (False, None, 1):
            record = fixture(); record['cases'][0]['metadata_cleared'] = changed
            with self.assertRaises(ValueError): admission.check_profile(record)

    def test_available_count(self):
        for changed in (0, 5, 7, True):
            record = fixture(); record['cases'][0]['available'] = changed
            with self.assertRaises(ValueError): admission.check_profile(record)

    def test_allocated_empty_lookup(self):
        for changed in (False, None, 1):
            record = fixture(); record['cases'][0]['empty_lookup'] = changed
            with self.assertRaises(ValueError): admission.check_profile(record)

    def test_case_inventory(self):
        for transform in (lambda cases: cases[:-1], lambda cases: cases[::-1], lambda cases: cases + cases[:1]):
            record = fixture(); record['cases'] = transform(record['cases'])
            with self.assertRaises(ValueError): admission.check_profile(record)

    def test_field_inventory(self):
        for field in (None, fixture()['fields'][0], {'name': 'unknown'}):
            record = fixture()
            if field is None: record['fields'].pop()
            else: record['fields'][-1] = field
            with self.assertRaises(ValueError): admission.check_profile(record)

    def test_boolean_and_missing_numeric_values(self):
        for key in ('capacity', 'index', 'value', 'attempts', 'frees', 'metadata'):
            for value in (True, None, -1, 2**64):
                record = fixture(); record['cases'][0][key] = value
                with self.subTest(key=key, value=value), self.assertRaises(ValueError): admission.check_profile(record)

    def test_request_and_release_binding(self):
        for name in ('oom_request', 'allocation', 'released'):
            for key in ('base', 'bytes', 'alignment'):
                record = fixture(); record['cases'][0][name][key] += 1
                with self.subTest(name=name, key=key), self.assertRaises(ValueError): admission.check_profile(record)

    def test_component_offsets(self):
        for key in ('metadata', 'key_pointer', 'value_pointer'):
            record = fixture(); record['cases'][1][key] += 16
            with self.subTest(key=key), self.assertRaises(ValueError): admission.check_profile(record)

    def test_failures_and_lifetime_accounting(self):
        for key, value in (('oom_error', None), ('oom_capacity', 8), ('oom_metadata', 4096),
                           ('reserve_error', 'OutOfMemory'), ('insert_error', 'OutOfMemory'),
                           ('attempts', 3), ('allocations', 2), ('frees', 0), ('resizes', 1), ('remaps', 1)):
            record = fixture(); record['cases'][0][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError): admission.check_profile(record)

    def test_abi_and_element_geometry(self):
        for name, key, value in (('target', 'arch', 'x86_64'), ('target', 'bytes', 48),
                                ('target', 'alignment', 8), ('metadata', 'bytes', 2), ('value', 'bytes', True)):
            record = fixture(); record[name][key] = value
            with self.subTest(name=name, key=key), self.assertRaises(ValueError): admission.check_profile(record)

    def test_extra_fields(self):
        for path in ((), ('target',), ('cases', 0), ('cases', 0, 'allocation')):
            record = copy.deepcopy(fixture()); target = record
            for key in path: target = target[key]
            target['unreviewed'] = True
            with self.subTest(path=path), self.assertRaises(ValueError): admission.check_profile(record)


if __name__ == '__main__':
    unittest.main()
