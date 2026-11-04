#!/usr/bin/env python3
"""Fail-closed admission for the production expression destructor.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import unittest
import check_compiler
import extract_expression_deinit as extraction
from test_compiler_extraction import mutate, semantic_part

MUTATIONS = {
    "omit-item-value": ("self.item.deinit(allocator);", ""),
    "omit-item-allocation": ("allocator.destroy(self.item);", ""),
    "omit-arguments": ("allocator.free(self.arguments);", ""),
    "omit-invalidation": ("self.* = undefined;", ""),
    "destroy-before-deinit": ("self.item.deinit(allocator);\n        allocator.destroy(self.item);",
                             "allocator.destroy(self.item);\n        self.item.deinit(allocator);"),
    "arguments-before-item": ("self.item.deinit(allocator);\n        allocator.destroy(self.item);\n        allocator.free(self.arguments);",
                              "allocator.free(self.arguments);\n        self.item.deinit(allocator);\n        allocator.destroy(self.item);"),
    "double-free-arguments": ("allocator.free(self.arguments);", "allocator.free(self.arguments); allocator.free(self.arguments);"),
    "invalidate-before-release": ("allocator.free(self.arguments);\n        self.* = undefined;",
                                  "self.* = undefined;\n        allocator.free(self.arguments);"),
}


def change_body(data, before, after):
    # Other deinitializers also invalidate descriptors. Restrict the mutation
    # to this function, while retaining the complete source for extraction.
    start = data.index(b"fn deinit(self: *Expression,")
    end = data.index(b"\n    }", start) + len(b"\n    }")
    return data[:start] + mutate(data[start:end], before, after) + data[end:]


class DestructorTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = extraction.SOURCE.read_bytes()

    def test_current_source(self):
        self.assertEqual(extraction.extract(self.source), extraction.OUTPUT.read_bytes())

    def test_mutations_are_semantic(self):
        original = semantic_part(extraction.extract(self.source))
        for name, (before, after) in MUTATIONS.items():
            with self.subTest(name=name):
                self.assertNotEqual(semantic_part(extraction.extract(change_body(self.source, before, after))), original)

    def test_unmodeled_operations_reject(self):
        for before, after in (
            ("self.item.deinit(allocator);", "self.item.deinit(other);"),
            ("allocator.destroy(self.item);", "allocator.destroy(self.arguments);"),
            ("allocator.free(self.arguments);", "allocator.free(other.arguments);"),
            ("allocator.free(self.arguments);", "if (condition) allocator.free(self.arguments);"),
            ("self.* = undefined;", "self.* = .{};"),
            ("self.item.deinit(allocator);", "return;"),
        ):
            with self.subTest(after=after), self.assertRaises(extraction.Unsupported):
                extraction.extract(change_body(self.source, before, after))

    def test_changed_types_and_imports_reject(self):
        for before, after in (
            ('@import("std");', '@import("different_std.zig");'),
            ('@import("assembly_item.zig");', '@import("different.zig");'),
            ('pub const Id = u32;', 'pub const Id = u64;'),
            ('item: *AssemblyItem,', 'item: AssemblyItem,'),
            ('arguments: []Id,', 'arguments: []const Id,'),
            ('fn deinit(self: *Expression,', 'fn deinit(self: *const Expression,'),
        ):
            with self.subTest(after=after), self.assertRaises(extraction.Unsupported):
                extraction.extract(mutate(self.source, before, after))

    def test_comments_are_not_semantics(self):
        self.assertEqual(semantic_part(extraction.extract(self.source)),
                         semantic_part(extraction.extract(b"// allocator.free(self.arguments);\n" + self.source)))

    def test_owner_and_shadow_bindings_reject(self):
        start = self.source.index(b"fn deinit(self: *Expression,")
        end = self.source.index(b"\n    }", start) + len(b"\n    }")
        decoy = self.source[start:end]
        renamed = self.source[:start] + decoy.replace(b"fn deinit(", b"fn renamed(", 1) + self.source[end:]
        with self.assertRaises(extraction.Unsupported):
            extraction.extract(renamed + b"\n" + decoy + b"\n")
        with self.assertRaises(extraction.Unsupported):
            extraction.extract(self.source[:end] + b"\n const Id = u64;\n" + self.source[end:])


if __name__ == "__main__":
    unittest.main()
