#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Closed source binding for owned cache publication, including the shared
storage/interner admission profile and its rejection controls.
"""
import unittest
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_owned_keys as extraction
from extract_compiler import Unsupported
from test_compiler_extraction import mutate, semantic_part
from test_compiler_storage import PUBLICATION_REJECTIONS


class OwnedKeysTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extraction.extract(extraction.SOURCE.read_bytes()), extraction.OUTPUT.read_bytes())

    def test_unsafe_profiles_rejected(self):
        source = extraction.SOURCE.read_bytes()
        for before, after in PUBLICATION_REJECTIONS:
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extraction.extract(mutate(source, before, after))

    def test_ambiguous_helper_rejected(self):
        source = extraction.SOURCE.read_bytes()
        header = b'fn publishOwned(self: *ExpressionClasses, key: ExpressionKey, id: Id) std.mem.Allocator.Error!void'
        with self.assertRaises(Unsupported):
            extraction.extract(source + b'\n' + header + b' {}\n')

    def test_comments_are_not_semantics(self):
        source = extraction.SOURCE.read_bytes()
        self.assertEqual(semantic_part(extraction.extract(source)),
                         semantic_part(extraction.extract(source + b'\n// getOrPut free store\n')))


if __name__ == '__main__':
    unittest.main()
