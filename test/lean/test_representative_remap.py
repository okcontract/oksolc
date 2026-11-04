#!/usr/bin/env python3
"""Fail-closed admission of the exact refusing remap body and dispatch.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_representative_remap as admission
from extract_storage import Unsupported
from test_representative_growth import fixture, allocator_fixture


def callbacks():
    # Independent literal source: expected behavior is not generated from the
    # admission constants or the emitted Lean implementation.
    return b'''
pub fn noRemap(
    self: *anyopaque,
    memory: []u8,
    alignment: Alignment,
    new_len: usize,
    ret_addr: usize,
) ?[*]u8 {
    _ = self;
    _ = memory;
    _ = alignment;
    _ = new_len;
    _ = ret_addr;
    return null;
}
pub inline fn rawRemap(a: Allocator, memory: []u8, alignment: Alignment, new_len: usize, ret_addr: usize) ?[*]u8 {
    return a.vtable.remap(a.ptr, memory, alignment, new_len, ret_addr);
}
'''


class RemapAdmissionTests(unittest.TestCase):
    def test_complete_wrapper_and_callback(self):
        admission.admit(fixture(), allocator_fixture() + callbacks())

    def test_refusal_and_absence_of_side_effects(self):
        for before, after in (
                (b'return null;', b'return memory.ptr;'),
                (b'_ = memory;', b'@memset(memory, undefined);'),
                (b'_ = self;', b'self.* = undefined;'),
                (b'_ = new_len;', b'if (new_len == 0) return null;'),
                (b'_ = ret_addr;', b'allocator.free(memory);')):
            with self.subTest(statement=before), self.assertRaises(Unsupported):
                admission.admit(fixture(), allocator_fixture() + callbacks().replace(before, after))

    def test_exact_dispatch_arguments(self):
        for after in (
                b'a.vtable.remap(a.ptr, memory[1..], alignment, new_len, ret_addr)',
                b'a.vtable.remap(a.ptr, memory, alignment, memory.len, ret_addr)',
                b'a.vtable.remap(a.ptr, memory, .@"1", new_len, ret_addr)',
                b'a.vtable.remap(undefined, memory, alignment, new_len, ret_addr)',
                b'a.vtable.resize(a.ptr, memory, alignment, new_len, ret_addr)'):
            before = b'a.vtable.remap(a.ptr, memory, alignment, new_len, ret_addr)'
            self.assertEqual(callbacks().count(before), 1)
            with self.subTest(replacement=after), self.assertRaises(Unsupported):
                admission.admit(fixture(), allocator_fixture() + callbacks().replace(before, after))

    def test_missing_duplicate_and_renamed_callbacks(self):
        for body in (b'', callbacks() + callbacks(), callbacks().replace(b'pub fn noRemap', b'pub fn renamed')):
            with self.assertRaises(Unsupported):
                admission.admit(fixture(), allocator_fixture() + body)

    def test_callback_does_not_replace_whole_source_identity(self):
        with self.assertRaises(ValueError):
            admission.extract(fixture(), allocator_fixture() + callbacks())


if __name__ == '__main__':
    unittest.main()
