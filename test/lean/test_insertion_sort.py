#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Negative controls for the restricted normalization-sort translator.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import os
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
import extract_insertion_sort as extraction
from environment import zig_library


def mutate(data, before, after):
    before, after = before.encode(), after.encode()
    if data.count(before) != 1:
        raise ValueError("ambiguous mutation: " + before.decode())
    return data.replace(before, after)


def semantics(text):
    return "\n".join(line for line in text.splitlines() if " SHA-256: " not in line)


SORT_MUTATIONS = [
    ("assert(a <= b);\n\n    var i = a + 1;", "assert(a < b);\n\n    var i = a + 1;"),
    ("var i = a + 1;", "var i = a + 2;"),
    ("while (i < b) : (i += 1)", "while (i <= b) : (i += 1)"),
    ("while (i < b) : (i += 1)", "while (i < b) : (i += 2)"),
    ("var j = i;", "var j = i + 1;"),
    ("while (j > a and context.lessThan(j, j - 1))", "while (j >= a and context.lessThan(j, j - 1))"),
    ("while (j > a and context.lessThan(j, j - 1))", "while (j > a or context.lessThan(j, j - 1))"),
    ("while (j > a and context.lessThan(j, j - 1))", "while (j > a and context.lessThan(j - 1, j))"),
    ("(j -= 1)", "(j -= 2)"),
    ("context.swap(j, j - 1);", "context.swap(j, j);"),
    ("context.swap(j, j - 1);", "context.swap(j, j - 1); context.swap(j, j - 1);"),
    ("insertionContext(0, items.len, Context", "insertionContext(1, items.len, Context"),
    ("const mem = std.mem;", "const mem = replacement;"),
    ("const assert = std.debug.assert;", "const assert = replacement;"),
    ("return a < b;", "return a == b;"),
]
CALLER_MUTATIONS = [
    ("@memcpy(normalized, arguments);", ""),
    ("@memcpy(normalized, arguments);\n        std.sort.insertion(Id, normalized, {}, std.sort.asc(Id));",
     "std.sort.insertion(Id, normalized, {}, std.sort.asc(Id));\n        @memcpy(normalized, arguments);"),
    ('const std = @import("std");', 'const std = @import("replacement");'),
    ("pub const Id = u32;", "pub const Id = u64;"),
    ("@memcpy(normalized, arguments);", "@memcpy(arguments, normalized);"),
    ("std.sort.insertion(Id, normalized, {}, std.sort.asc(Id));", "std.sort.insertion(Id, arguments, {}, std.sort.asc(Id));"),
    ("std.sort.insertion(Id, normalized, {}, std.sort.asc(Id));", "std.sort.heap(Id, normalized, {}, std.sort.asc(Id));"),
    ("std.sort.asc(Id));", "std.sort.desc(Id));"),
    ("arguments.len < 2)", "arguments.len < 3)"),
    ("try allocator.alloc(Id, arguments.len)", "allocator.alloc(Id, arguments.len) catch return .{ .items = &.{} }"),
]


class InsertionExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        tree = os.environ.get("INSERTION_ZIG_TREE")
        library = Path(tree) / "lib" if tree else zig_library()
        cls.sort = (library / "std/sort.zig").read_bytes()
        cls.caller = extraction.SOURCE.read_bytes()

    def test_generated_matches(self):
        self.assertEqual(extraction.extract(self.sort, self.caller), extraction.OUTPUT.read_text())

    def test_unsupported_sort_mutations(self):
        for before, after in SORT_MUTATIONS:
            with self.subTest(before=before, after=after), self.assertRaises(extraction.Unsupported):
                extraction.extract(mutate(self.sort, before, after), self.caller)

    def test_unsupported_caller_mutations(self):
        for before, after in CALLER_MUTATIONS:
            with self.subTest(before=before, after=after), self.assertRaises(extraction.Unsupported):
                extraction.extract(self.sort, mutate(self.caller, before, after))

    def test_supported_comparators_change_program(self):
        original = semantics(extraction.extract(self.sort, self.caller))
        for comparison in ("<=", ">", ">="):
            with self.subTest(comparison=comparison):
                changed = extraction.extract(mutate(self.sort, "return a < b;", "return a " + comparison + " b;"), self.caller)
                self.assertNotEqual(semantics(changed), original)
                self.assertIn("decide (a.toNat " + comparison + " b.toNat)", changed)

    def test_trivia_does_not_change_program(self):
        original = semantics(extraction.extract(self.sort, self.caller))
        comment = b"// Ignore prose: context.swap(j, j); return a > b;\n"
        self.assertEqual(semantics(extraction.extract(comment + self.sort, comment + self.caller)), original)
        self.assertEqual(semantics(extraction.extract(self.sort.replace(b"var j = i;", b"var  j\n = i ;"), self.caller)), original)

    def test_ambiguous_or_missing_definition_rejects(self):
        signature = b"pub fn insertionContext(a: usize, b: usize, context: anytype) void"
        for source in (self.sort + signature + b" {}", self.sort.replace(signature, b"fn changed() void")):
            with self.assertRaises(extraction.Unsupported):
                extraction.extract(source, self.caller)


if __name__ == "__main__":
    unittest.main()
