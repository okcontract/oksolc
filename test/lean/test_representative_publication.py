#!/usr/bin/env python3
"""Bind publication order while retaining both complete native growth branches.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import extract_representative_publication as admission
from extract_storage import Unsupported
from test_representative_append import fixture as append_fixture


def fixture():
    growth = b'''pub fn ensureTotalCapacityPrecise(self: *Self, gpa: Allocator, new_capacity: usize) Allocator.Error!void {
        self.pointer_stability.assertUnlocked();
    if (@sizeOf(T) == 0) { self.capacity = math.maxInt(usize); return; }
        if (self.capacity >= new_capacity) return;
        const old_memory = self.allocatedSlice();
        if (gpa.remap(old_memory, new_capacity)) |new_memory| {
            self.items.ptr = new_memory.ptr;
            self.capacity = new_memory.len;
        } else {
            const new_memory = try gpa.alignedAlloc(T, alignment, new_capacity);
            @memcpy(new_memory[0..self.items.len], self.items);
            gpa.free(old_memory);
            self.items.ptr = new_memory.ptr;
            self.capacity = new_memory.len;
        }
    }
    '''
    return append_fixture().replace(b"pub fn addOneAssumeCapacity", growth + b"pub fn addOneAssumeCapacity")


class RepresentativePublicationAdmissionTests(unittest.TestCase):
    def test_both_complete_branches(self):
        admission.admit(fixture())

    def test_each_branch_keeps_exact_publication_order(self):
        before = b"self.items.ptr = new_memory.ptr;\n            self.capacity = new_memory.len;"
        source = fixture()
        self.assertEqual(source.count(before), 2)
        for branch in range(2):
            position = source.index(before) if branch == 0 else source.rindex(before)
            for after in (
                    b"self.capacity = new_memory.len; self.items.ptr = new_memory.ptr;",
                    b"self.items.ptr = old_memory.ptr; self.capacity = new_memory.len;",
                    b"self.items = new_memory; self.capacity = new_memory.len;",
                    b"self.items.ptr = new_memory.ptr; self.items.len = new_memory.len; self.capacity = new_memory.len;",
                    b"self.items.ptr = new_memory.ptr;",
                    b"self.items.ptr = new_memory.ptr; self.capacity = self.items.len;"):
                changed = source[:position] + after + source[position + len(before):]
                with self.subTest(branch=branch, replacement=after), self.assertRaises(Unsupported):
                    admission.admit(changed)

    def test_control_and_prior_effects_remain_bound(self):
        for before, after in (
                (b"self.pointer_stability.assertUnlocked();", b""),
                (b"self.pointer_stability.assertUnlocked();", b"self.pointer_stability.lockShared();"),
                (b"@sizeOf(T) == 0", b"@sizeOf(T) != 0"),
                (b"const old_memory = self.allocatedSlice();", b"const old_memory = self.items;"),
                (b"gpa.remap(old_memory, new_capacity)", b"gpa.remap(self.items, new_capacity)"),
                (b"try gpa.alignedAlloc(T, alignment, new_capacity)", b"gpa.alignedAlloc(T, alignment, new_capacity) catch unreachable"),
                (b"@memcpy(new_memory[0..self.items.len], self.items);", b"@memcpy(new_memory[0..self.capacity], self.items);"),
                (b"gpa.free(old_memory);", b"gpa.free(new_memory);"),
                (b"gpa.free(old_memory);", b""),
                (b"@memcpy(new_memory[0..self.items.len], self.items);\n            gpa.free(old_memory);",
                 b"gpa.free(old_memory); @memcpy(new_memory[0..self.items.len], self.items);")):
            self.assertEqual(fixture().count(before), 1)
            with self.subTest(statement=before), self.assertRaises(Unsupported):
                admission.admit(fixture().replace(before, after))
        # The precise helper's early return is checked independently of append's
        # ensureTotalCapacity wrapper, which has the same comparison.
        source = fixture()
        before = b"if (self.capacity >= new_capacity) return;"
        position = source.rindex(before)
        changed = source[:position] + before.replace(b">=", b">") + source[position + len(before):]
        with self.assertRaises(Unsupported):
            admission.admit(changed)

    def test_factory_scope_and_owner_fields(self):
        managed = fixture().replace(b"pub fn Aligned(", b"pub fn AlignedManaged(").replace(b"gpa.free(old_memory);", b"")
        admission.admit(managed + fixture())
        for source in (fixture() + fixture(), fixture().replace(b"capacity: usize,", b"capacity: u32,"),
                fixture().replace(b"capacity: usize,", b"capacity: usize, extra: usize = 0,")):
            with self.subTest(source=source[:60]), self.assertRaises(Unsupported):
                admission.admit(source)

    def test_body_match_does_not_replace_std_identity(self):
        with self.assertRaisesRegex(ValueError, "unreviewed"):
            admission.extract(fixture())


if __name__ == "__main__":
    unittest.main()
