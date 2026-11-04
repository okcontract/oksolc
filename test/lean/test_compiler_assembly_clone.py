#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Source binding and fail-closed admission for item clone/cleanup.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_assembly_clone as extract
from extract_compiler import Unsupported

COPY = '''        if (self.verbatim) |verbatim| {
            result.verbatim = .{
                .arguments = verbatim.arguments,
                .return_variables = verbatim.return_variables,
                .data = try allocator.dupe(u8, verbatim.data),
            };
        }
'''
MUTATIONS = {
    'lost_arguments': ('.arguments = verbatim.arguments,', '.arguments = 0,',
        'cloneCode.run (duplicate true) original initial = (.ok copied, allocated)'),
    'lost_returns': ('.return_variables = verbatim.return_variables,', '.return_variables = 0,',
        'cloneCode.run (duplicate true) original initial = (.ok copied, allocated)'),
    'lost_bytes': ('try allocator.dupe(u8, verbatim.data)', 'try allocator.dupe(u8, &.{})',
        'cloneCode.run (duplicate true) original initial = (.ok copied, allocated)'),
    'shallow_payload': (COPY, '',
        'cloneCode.run (duplicate true) original initial = (.ok copied, allocated)'),
    'return_source': ('return result;\n    }\n\n    pub fn typeOf', 'return self.*;\n    }\n\n    pub fn typeOf',
        'cloneCode.run (duplicate true) original initial = (.ok copied, allocated)'),
    'lost_free': ('if (self.verbatim) |verbatim| allocator.free(verbatim.data);', '',
        'deinitCode.run free copied allocated = (none, initial)'),
    'lost_invalidation': ('if (self.verbatim) |verbatim| allocator.free(verbatim.data);\n        self.* = undefined;',
        'if (self.verbatim) |verbatim| allocator.free(verbatim.data);',
        'deinitCode.run free copied allocated = (none, initial)'),
}


def mutated(name):
    before, after, claim = MUTATIONS[name]
    data = extract.SOURCE.read_bytes()
    if data.count(before.encode()) != 1:
        raise ValueError('mutation must target exactly one source span: ' + name)
    return extract.extract(data.replace(before.encode(), after.encode())), claim


class AssemblyCloneTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.SOURCE.read_bytes()), extract.OUTPUT.read_bytes())

    def test_mutations_change_executable_definitions(self):
        baseline = extract.OUTPUT.read_bytes().split(b'def cloneCode', 1)[1]
        for name in MUTATIONS:
            with self.subTest(name=name):
                changed, _ = mutated(name)
                self.assertNotEqual(changed.split(b'def cloneCode', 1)[1], baseline)

    def test_unsupported_ownership_and_projection(self):
        for before, after in [
            ('var result = self.*;', 'var result = undefined;'),
            ('var result = self.*;', 'var result = self.*; result.data_value = 0;'),
            ('var result = self.*;', 'var result = self.*; result.debug_data = .{};'),
            ('try allocator.dupe(u8, verbatim.data)', 'verbatim.data'),
            ('try allocator.dupe(u8, verbatim.data)', 'allocator.dupe(u8, verbatim.data)'),
            ('try allocator.dupe(u8, verbatim.data)', 'try allocator.dupe(u16, verbatim.data)'),
            ('try allocator.dupe(u8, verbatim.data)', 'try other_allocator.dupe(u8, verbatim.data)'),
            ('allocator.free(verbatim.data);', 'allocator.free(self.debug_data);'),
            ('allocator.free(verbatim.data);', 'allocator.free(verbatim.data); allocator.free(verbatim.data);'),
            ('.arguments = verbatim.arguments,', '.arguments = verbatim.return_variables,'),
            ('data: []u8,', 'data: []const u8,'),
            ('modifier_depth: usize = 0,', 'modifier_depth: usize = 0, extra_owned: []u8,'),
        ]:
            data = extract.SOURCE.read_bytes()
            self.assertIn(before.encode(), data)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(data.replace(before.encode(), after.encode()))

    def test_trivia_is_not_semantic(self):
        data = extract.SOURCE.read_bytes()
        baseline = extract.extract(data).split(b'def cloneCode', 1)[1]
        changed = extract.extract(data + b'\n// return self.*;\n')
        self.assertEqual(changed.split(b'def cloneCode', 1)[1], baseline)

    def test_clone_owner_and_bindings(self):
        data = extract.SOURCE.read_bytes()
        start = data.index(b'pub fn clone(self: *const AssemblyItem,')
        end = data.index(b'\n    }', start) + len(b'\n    }')
        body = data[start:end]
        renamed = data[:start] + body.replace(b'fn clone(', b'fn renamed(') + data[end:]
        for suffix in (body, b'pub const Decoy = struct { ' + body + b' };'):
            with self.subTest(suffix=suffix[:30]), self.assertRaises(Unsupported):
                extract.extract(renamed + b'\n' + suffix)
        renamed_end = end + len(b'renamed') - len(b'clone')
        nested = renamed[:renamed_end] + b'\n const Nested = struct { ' + body + b' };\n' + renamed[renamed_end:]
        with self.assertRaises(Unsupported):
            extract.extract(nested)
        for insertion in (body, b'const std = @import("other.zig");', b'const VerbatimBytecode = u64;',
                          b'const AssemblyItem = u64;', b'extra_owned: []u8,'):
            with self.subTest(insertion=insertion[:40]), self.assertRaises(Unsupported):
                extract.extract(data[:end] + b'\n' + insertion + data[end:])
        with self.assertRaises(Unsupported):
            extract.extract(data.replace(b'@import("std");', b'@import("other.zig");'))

    def test_unreachable_clone_suffix_rejects(self):
        data = extract.SOURCE.read_bytes()
        before = b'return result;\n    }\n\n    pub fn typeOf'
        self.assertEqual(data.count(before), 1)
        with self.assertRaises(Unsupported):
            extract.extract(data.replace(before, before.replace(b'return result;', b'return result; result.data_value = 1;')))


if __name__ == '__main__':
    unittest.main()
