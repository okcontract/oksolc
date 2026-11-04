#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admission boundaries for the complete binaryLogarithm helper.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_binary_logarithm as extract
from extract_compiler import Unsupported


class BinaryLogarithmTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.SOURCE.read_bytes()), extract.OUTPUT.read_bytes())

    def test_semantic_mutations_reject(self):
        for before, after in [
            ('pub fn binaryLogarithm(value: u256) ?usize', 'pub fn binaryLogarithm(value: u256) ?u8'),
            ('pub fn binaryLogarithm(value: u256)', 'pub fn binaryLogarithm(value: u128)'),
            ('value == 0 or (value & (value - 1)) != 0', 'value == 0 and (value & (value - 1)) != 0'),
            ('value == 0 or (value & (value - 1)) != 0', 'value != 0 or (value & (value - 1)) != 0'),
            ('(value & (value - 1)) != 0', '(value | (value - 1)) != 0'),
            ('(value & (value - 1)) != 0', '(value & (value - 1)) == 0'),
            ('(value & (value - 1)) != 0', '(value & (value -% 1)) != 0'),
            ('(value & (value - 1)) != 0', '(value & (value + 1)) != 0'),
            ('return @intCast(@ctz(value));', 'return @intCast(@clz(value));'),
            ('return @intCast(@ctz(value));', 'return @truncate(@ctz(value));'),
            ('return @intCast(@ctz(value));', 'return @intCast(@ctz(value) + 1);'),
        ]:
            source = extract.SOURCE.read_bytes()
            self.assertIn(before.encode(), source)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(source.replace(before.encode(), after.encode()))

    def test_trivia(self):
        source = extract.SOURCE.read_bytes()
        self.assertEqual(extract.extract(source).split(b'def binaryLogarithm', 1)[1],
                         extract.extract(source + b'\n// inert comment\n').split(b'def binaryLogarithm', 1)[1])


if __name__ == '__main__':
    unittest.main()
