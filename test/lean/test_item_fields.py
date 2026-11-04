#!/usr/bin/env python3
"""Admission controls for complete native item declarations and scalar probes.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import unittest
from test_item_layout import fixture as nominal
from generate_item_fields import FIELDS, NESTED, ITEM_TAGS, JUMP_TAGS, SOURCE, DEBUG_SOURCE, LOCATION_SOURCE, OPCODES, OUTPUT, generate, check_profile


def fixture():
    offsets = dict(zip(FIELDS, (208, 216, 0, 80, 120, 212, 32, 184, 200)))
    tags = lambda names: {'type': 'c_int', 'values': [{'name': name, 'value': i} for i, name in enumerate(names)]}
    integers = lambda bits: [None, 0, 1, 2**(bits - 1), 2**(bits - 1) + 17, 2**bits - 1, None, 0]
    nested_offsets = {'source_location': {'start': 16, 'end': 20, 'source_name': 0},
                      'verbatim': {'arguments': 0, 'return_variables': 8, 'data': 16},
                      'debug_data': {'native_location': 0, 'origin_location': 24, 'ast_id': 48}}
    record = {'schema': 'oksolc.assembly-item-fields.v5', 'target': nominal(),
            'fields': [{'name': name, 'type': native, 'offset': offsets[name], 'bytes': size, 'alignment': alignment}
                       for name, (native, size, alignment, _) in FIELDS.items()],
            'nested': {name: {'type': native, 'bytes': size, 'alignment': alignment,
                              'fields': [{'name': field, 'type': child, 'offset': nested_offsets[name][field], 'bytes': extent, 'alignment': aligned}
                                         for field, (child, extent, aligned, _) in fields.items()]}
                       for name, (native, size, alignment, _, fields) in NESTED.items()},
            'itemTag': tags(ITEM_TAGS), 'jumpTag': tags(JUMP_TAGS),
            'instruction': {'type': 'libevmasm.instruction.Instruction', 'tagType': 'u8', 'exhaustive': False},
            'integerOptionals': {'pushed_value': {'type': 'u256', 'bits': 256, 'signed': False},
                                'immutable_occurrences': {'type': 'usize', 'bits': 64, 'signed': False},
                                'ast_id': {'type': 'i64', 'bits': 64, 'signed': True}},
            'observations': {'optionalInstructions': [None, *range(256)],
                             'optionalIntegers': [dict(pushed_value=w, immutable_occurrences=s) for w, s in zip(integers(256), integers(64))],
                             'verbatim': [None, {'arguments': 0, 'returns': 0, 'data': {'offset': 2, 'length': 0}},
                                          {'arguments': 3, 'returns': 2, 'data': {'offset': 1, 'length': 3}},
                                          {'arguments': 2**64 - 1, 'returns': 2**64 - 1, 'data': {'offset': 0, 'length': 6}},
                                          None, {'arguments': 1, 'returns': 0, 'data': {'offset': 5, 'length': 0}}],
                             'debug': [{'native': {'start': -1, 'end': -1, 'source': None},
                                        'origin': {'start': -1, 'end': -1, 'source': None}, 'ast_id': None}] +
                                      [{'native': {'start': -1, 'end': 17, 'source': None if index == 6 else {'offset': 2, 'length': 3}},
                                        'origin': {'start': -(2**31), 'end': 2**31 - 1, 'source': {'offset': 7, 'length': 0}}, 'ast_id': identity}
                                       for index, identity in enumerate([0, -1, -(2**63), 2**63 - 1, 17, None, 0], 1)],
                             'operation': {'kind': 1, 'opcode': 1, 'data': 0, 'jump': 0, 'modifier': 0},
                             'pushed': {'kind': 2, 'opcodeAbsent': True, 'data': 2**255 + 17, 'jump': 2, 'modifier': 19}}}
    record['observations']['initializers'] = [
        {'kind': kind, 'instruction': instruction, 'data': data, 'verbatim': None,
         'debug': copy.deepcopy(record['observations']['debug'][debug]),
         'jump': 0, 'pushed': None, 'immutable': None, 'modifier': 0}
        for kind, instruction, data, debug in ((2, None, 0, 0), (2, None, 2**256 - 1, 4),
                                              (2, None, 2**255 + 17, 2), (1, 0, 0, 0), (1, 1, 0, 1), (1, 255, 0, 3))]
    return record


class ItemFieldsTests(unittest.TestCase):
    def test_complete_initializer_observations(self):
        for index in range(6):
            for key in fixture()['observations']['initializers'][index]:
                record = fixture()
                record['observations']['initializers'][index].pop(key)
                with self.subTest(index=index, missing=key), self.assertRaises(ValueError):
                    check_profile(record)
            for key, value in [('kind', 13), ('instruction', None if index >= 3 else 0), ('data', 123),
                               ('verbatim', {}), ('debug', {}), ('jump', 2), ('pushed', 99),
                               ('immutable', 27), ('modifier', 19), ('extra', 0)]:
                record = fixture()
                record['observations']['initializers'][index][key] = value
                with self.subTest(index=index, changed=key), self.assertRaises(ValueError):
                    check_profile(record)
        record = fixture()
        record['observations']['initializers'][4]['instruction'] = True
        with self.assertRaises(ValueError):
            check_profile(record)
        record = fixture()
        record['observations']['initializers'][1]['debug']['native']['source']['offset'] = 0
        self.assertEqual(record['observations']['debug'][4]['native']['source']['offset'], 2)
        with self.assertRaises(ValueError):
            check_profile(record)
        for change in (lambda rows: rows.pop(), lambda rows: rows.reverse()):
            record = fixture()
            change(record['observations']['initializers'])
            with self.assertRaises(ValueError):
                check_profile(record)

    def test_nested_declarations(self):
        for owner in NESTED:
            for change in (lambda r: r['nested'].pop(owner),
                           lambda r: r['nested'][owner].update(type='Other'),
                           lambda r: r['nested'][owner].update(bytes=True),
                           lambda r: r['nested'][owner].update(alignment=1),
                           lambda r: r['nested'][owner]['fields'].pop(),
                           lambda r: r['nested'][owner]['fields'].append(r['nested'][owner]['fields'][0])):
                record = fixture()
                change(record)
                with self.subTest(owner=owner), self.assertRaises(ValueError):
                    check_profile(record)
            for index in range(len(NESTED[owner][4])):
                for key, value in (('type', 'u8'), ('offset', 1), ('bytes', True), ('alignment', 1), ('name', 'other')):
                    record = fixture()
                    record['nested'][owner]['fields'][index][key] = value
                    with self.subTest(owner=owner, index=index, key=key), self.assertRaises(ValueError):
                        check_profile(record)
            record = fixture()
            record['nested'][owner]['fields'].reverse()
            check_profile(record)

    def test_nested_sources(self):
        for key, path, mutations in (
            ('debug', DEBUG_SOURCE, [(b'ast_id: ?i64 = null,', b'ast_id: ?u64 = null,'),
                                    (b'native_location: SourceLocation = .{},', b'native_location: SourceLocation = undefined,'),
                                    (b'    pub fn destroy(', b'    omitted: u8 = 0,\n    pub fn destroy('),
                                    (b'@import("source_location.zig")', b'@import("other.zig")')]),
            ('location', LOCATION_SOURCE, [(b'start: i32 = -1,', b'start: i32 = 0,'),
                                          (b'source_name: ?[]const u8 = null,', b'source_name: ?[]u8 = null,'),
                                          (b'    pub fn lessThan(', b'    omitted: u8 = 0,\n    pub fn lessThan(')])):
            source = path.read_bytes()
            for before, after in mutations:
                self.assertEqual(source.count(before), 1)
                with self.subTest(key=key, before=before), self.assertRaises(ValueError):
                    generate(fixture(), **{key: source.replace(before, after, 1)})
        source = SOURCE.read_bytes()
        with self.assertRaises(ValueError):
            generate(fixture(), source=source.replace(b'@import("../liblangutil/debug_data.zig")', b'@import("other.zig")'))

    def test_compound_observations(self):
        for name in ('verbatim', 'debug'):
            record = fixture()
            record['observations'][name].pop()
            with self.assertRaises(ValueError):
                check_profile(record)
        for name, index, field, value in [('verbatim', 1, 'arguments', True), ('verbatim', 2, 'returns', 99),
                                          ('verbatim', 3, 'data', {'offset': 1, 'length': 6}),
                                          ('debug', 1, 'ast_id', None), ('debug', 2, 'ast_id', 2**64-1),
                                          ('debug', 3, 'ast_id', -(2**63)-1),
                                          ('debug', 7, 'origin', {'start': -(2**31), 'end': 2**31-1, 'source': None})]:
            record = fixture()
            record['observations'][name][index][field] = value
            with self.subTest(name=name, field=field), self.assertRaises(ValueError):
                check_profile(record)
        record = fixture()
        record['integerOptionals']['ast_id']['signed'] = False
        with self.assertRaises(ValueError):
            check_profile(record)

    def test_current_and_modes(self):
        for mode in ('Debug', 'ReleaseSafe', 'ReleaseFast'):
            record = fixture()
            record['target']['mode'] = mode
            check_profile(record)
            self.assertEqual(generate(record), OUTPUT.read_bytes())

    def test_inventory(self):
        for change in (lambda r: r['fields'].pop(), lambda r: r['fields'].append(r['fields'][0]),
                       lambda r: r['fields'].__setitem__(1, r['fields'][0]), lambda r: r.update(extra=1)):
            record = fixture()
            change(record)
            with self.assertRaises(ValueError):
                check_profile(record)

    def test_field_metadata(self):
        for field in range(len(FIELDS)):
            for key, value in (('name', 'other'), ('type', 'u8'), ('bytes', True), ('bytes', 1),
                               ('alignment', True), ('alignment', 3), ('offset', True), ('offset', 224), ('offset', -1)):
                record = fixture()
                record['fields'][field][key] = value
                with self.subTest(field=field, key=key, value=value), self.assertRaises(ValueError):
                    check_profile(record)

    def test_overlap_and_changed_offsets(self):
        for offset in (208, 220):
            record = fixture()
            record['fields'][5]['offset'] = offset
            with self.assertRaises(ValueError):
                check_profile(record)
        record = fixture()
        record['fields'].reverse()
        check_profile(record)  # Publication is in captured byte order, independent of JSON order.

    def test_enum_domains(self):
        for tag in ('itemTag', 'jumpTag'):
            for value in (True, -1, 99):
                record = fixture()
                record[tag]['values'][1]['value'] = value
                with self.assertRaises(ValueError):
                    check_profile(record)
            for change in (lambda r: r[tag].update(type='u32'), lambda r: r[tag]['values'].pop(),
                           lambda r: r[tag]['values'][0].update(name='Other')):
                record = fixture()
                change(record)
                with self.assertRaises(ValueError):
                    check_profile(record)

    def test_native_observations(self):
        for name in ('operation', 'pushed'):
            row = fixture()['observations'][name]
            for key, value in row.items():
                record = fixture()
                record['observations'][name][key] = int(not value) if type(value) is bool else value + 1
                with self.subTest(name=name, key=key), self.assertRaises(ValueError):
                    check_profile(record)
        record = fixture()
        record['observations']['operation']['kind'] = True
        with self.assertRaises(ValueError):
            check_profile(record)

    def test_source_fields_and_enums(self):
        source = SOURCE.read_bytes()
        for before, after in ((b'modifier_depth: usize = 0,', b''),
                              (b'modifier_depth: usize = 0,', b'modifier_depth: u32 = 0,'),
                              (b'item_type: AssemblyItemType,', b'item_type: AssemblyItemType,\n extra: u8 = 0,'),
                              (b'enum(c_int)', b'enum(u32)'), (b'Ordinary,', b'Ordinary = 1,'),
                              (b'return initType(.Push, value, debug_data);', b'return initType(.Tag, value, debug_data);')):
            self.assertIn(before, source)
            with self.subTest(before=before), self.assertRaises(ValueError):
                generate(fixture(), source.replace(before, after, 1))

    def test_optional_child_and_domain(self):
        for key, value in (('type', 'other.Instruction'), ('tagType', 'u16'), ('exhaustive', True), ('exhaustive', 0)):
            record = fixture()
            record['instruction'][key] = value
            with self.assertRaises(ValueError):
                check_profile(record)
        instructions = OPCODES.read_bytes()
        for before, after in ((b'    _,', b''), (b'enum(u8)', b'enum(u16)')):
            self.assertIn(before, instructions)
            with self.assertRaises(ValueError):
                generate(fixture(), instructions=instructions.replace(before, after, 1))
        record = fixture()
        record['schema'] = 'oksolc.assembly-item-fields.v1'
        with self.assertRaises(ValueError):
            check_profile(record)

    def test_optional_observation_completeness(self):
        for index, value in ((0, 0), (1, None), (2, True), (256, 256)):
            record = fixture()
            record['observations']['optionalInstructions'][index] = value
            with self.assertRaises(ValueError):
                check_profile(record)
        record = fixture()
        record['observations']['optionalInstructions'].pop()
        with self.assertRaises(ValueError):
            check_profile(record)

    def test_nominal_target_binding(self):
        for key, value in (('bytes', 240), ('alignment', 8), ('arch', 'x86_64'), ('mode', 'ReleaseSmall')):
            record = fixture()
            record['target'][key] = value
            with self.assertRaises(ValueError):
                check_profile(record)

    def test_integer_optional_children(self):
        for name in ('pushed_value', 'immutable_occurrences'):
            for key, value in (('type', 'u8'), ('bits', True), ('bits', 32), ('signed', True), ('signed', 0), ('extra', 1)):
                record = fixture()
                record['integerOptionals'][name][key] = value
                with self.subTest(name=name, key=key, value=value), self.assertRaises(ValueError):
                    check_profile(record)
            record = fixture()
            del record['integerOptionals'][name]
            with self.assertRaises(ValueError):
                check_profile(record)
        record = fixture()
        record['schema'] = 'oksolc.assembly-item-fields.v2'
        with self.assertRaises(ValueError):
            check_profile(record)

    def test_integer_optional_observations(self):
        for name in ('pushed_value', 'immutable_occurrences'):
            for index in range(8):
                record = fixture()
                original = record['observations']['optionalIntegers'][index][name]
                for value in (True, -1, 2**256, None if original is not None else 0):
                    record['observations']['optionalIntegers'][index][name] = value
                    with self.subTest(name=name, index=index, value=value), self.assertRaises(ValueError):
                        check_profile(record)
            record = fixture()
            del record['observations']['optionalIntegers'][0][name]
            with self.assertRaises(ValueError):
                check_profile(record)
        record = fixture()
        record['observations']['optionalIntegers'].pop()
        with self.assertRaises(ValueError):
            check_profile(record)


if __name__ == '__main__':
    unittest.main()
