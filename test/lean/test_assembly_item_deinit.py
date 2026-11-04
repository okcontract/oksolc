#!/usr/bin/env python3
"""Fail-closed admission for the complete AssemblyItem destructor.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import check_compiler
import extract_assembly_item_deinit as extraction
from test_compiler_extraction import mutate, semantic_part

PAYLOAD = 'if (self.verbatim) |verbatim| allocator.free(verbatim.data);'
MUTATIONS = {
    'omit-payload': (PAYLOAD, ''),
    'omit-invalidation': ('self.* = undefined;', ''),
    'invalidate-first': (PAYLOAD + '\n        self.* = undefined;', 'self.* = undefined;\n        ' + PAYLOAD),
    'double-payload': (PAYLOAD, PAYLOAD + ' ' + PAYLOAD),
}


def change_body(data, before, after):
    start = data.index(b'pub fn deinit(self: *AssemblyItem,')
    end = data.index(b'\n    }', start) + len(b'\n    }')
    return data[:start] + mutate(data[start:end], before, after) + data[end:]


class ItemDestructorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = extraction.SOURCE.read_bytes()

    def test_current_source(self):
        self.assertEqual(extraction.extract(self.source), extraction.OUTPUT.read_bytes())

    def test_semantic_mutations(self):
        original = semantic_part(extraction.extract(self.source))
        for name, (before, after) in MUTATIONS.items():
            with self.subTest(name=name):
                self.assertNotEqual(semantic_part(extraction.extract(change_body(self.source, before, after))), original)

    def test_unsupported_body_rejects(self):
        for after in ('return;', 'allocator.destroy(self);', PAYLOAD.replace('allocator.free', 'other.free'),
                      PAYLOAD.replace('verbatim.data', 'self.data'), PAYLOAD.replace('self.verbatim', 'other.verbatim'),
                      'if (self.item_type == .VerbatimBytecode) ' + PAYLOAD,
                      PAYLOAD.replace('if (self.verbatim)', 'if (self.verbatim == null)')):
            with self.subTest(after=after), self.assertRaises(extraction.Unsupported):
                extraction.extract(change_body(self.source, PAYLOAD, after))

    def test_bindings_reject(self):
        for before, after in (
            ('@import("std");', '@import("other.zig");'),
            ('/// Allocator-owned bytes.\n    data: []u8,', '/// Allocator-owned bytes.\n    data: []const u8,'),
            ('verbatim: ?VerbatimBytecode = null,', 'verbatim: VerbatimBytecode,'),
            ('deinit(self: *AssemblyItem,', 'deinit(self: *const AssemblyItem,'),
        ):
            with self.subTest(after=after), self.assertRaises(extraction.Unsupported):
                extraction.extract(mutate(self.source, before, after))

    def test_decoys_and_shadow_bindings_reject(self):
        start = self.source.index(b'pub fn deinit(self: *AssemblyItem,')
        end = self.source.index(b'\n    }', start) + len(b'\n    }')
        body = self.source[start:end]
        renamed = self.source[:start] + body.replace(b'fn deinit(', b'fn renamed(') + self.source[end:]
        for suffix in (body, b'pub const Decoy = struct { ' + body + b' };'):
            with self.assertRaises(extraction.Unsupported):
                extraction.extract(renamed + b'\n' + suffix)
        with self.assertRaises(extraction.Unsupported):
            extraction.extract(self.source[:end] + b'\n const VerbatimBytecode = u64;\n' + self.source[end:])
        with self.assertRaises(extraction.Unsupported):
            extraction.extract(self.source[:end] + b'\n' + body + self.source[end:])
        with self.assertRaises(extraction.Unsupported):
            extraction.extract(self.source[:end] + b'\n extra_owned: []u8,\n' + self.source[end:])

    def test_comments_are_not_semantics(self):
        self.assertEqual(semantic_part(extraction.extract(self.source)),
                         semantic_part(extraction.extract(b'// pub fn deinit() {}\n' + self.source)))


if __name__ == '__main__':
    unittest.main()
