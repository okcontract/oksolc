#!/usr/bin/env python3
"""Bind empty-capacity growth to complete source bodies and early host guards.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import extract_representative_growth as admission
from extract_storage import Unsupported
from test_representative_publication import fixture as publication_fixture


def fixture():
    return publication_fixture().replace(b"pub fn addOneAssumeCapacity", b"""
        pub fn allocatedSlice(self: Self) Slice { return self.items.ptr[0..self.capacity]; }
        pub fn addOneAssumeCapacity""")


# Independent literal fixture: never derive the expected body from the admission
# implementation, which would let an incorrect wrapper admit its own mutation.
def allocator_fixture():
    return b'''
pub fn remap(self: Allocator, allocation: anytype, new_len: usize) ?Slice(AbsorbSentinel(@TypeOf(allocation))) {
    const slice_info = @typeInfo(@TypeOf(allocation)).pointer;
    const T = if (slice_info.size != .slice) comptime T: {
        assert(slice_info.size == .one);
        break :T @typeInfo(slice_info.child).array.child;
    } else slice_info.child;
    if (new_len == 0) { self.free(allocation); return allocation[0..0]; }
    if (allocation.len == 0) { return null; }
    if (@sizeOf(T) == 0) { var new_memory = allocation; new_memory.len = new_len; return new_memory; }
    const old_memory: []u8 = @ptrCast(@constCast(mem.absorbSentinel(allocation)));
    const new_len_bytes = math.mul(usize, @sizeOf(T), new_len) catch return null;
    const new_ptr = self.rawRemap(old_memory, .fromByteUnits(slice_info.attrs.@"align" orelse @alignOf(T)),
        new_len_bytes, @returnAddress(),) orelse return null;
    return @ptrCast(@alignCast(new_ptr[0..new_len_bytes]));
}
pub fn free(self: Allocator, memory: anytype) void {
    const slice_info = @typeInfo(@TypeOf(memory)).pointer;
    if (slice_info.size != .slice) {
        comptime assert(slice_info.size == .one and @typeInfo(slice_info.child) == .array);
    }
    const bytes: []u8 = @ptrCast(@constCast(mem.absorbSentinel(memory)));
    if (bytes.len == 0) return;
    @memset(bytes, undefined);
    self.rawFree(bytes, .fromByteUnits(slice_info.attrs.@"align" orelse @alignOf(slice_info.child)), @returnAddress());
}
'''


class RepresentativeGrowthAdmissionTests(unittest.TestCase):
    def test_complete_first_growth_dependency_bodies(self):
        admission.admit(fixture(), allocator_fixture())

    def test_allocation_view_uses_capacity_without_length_read(self):
        for replacement in (b"self.items", b"self.items.ptr[0..self.items.len]", b"self.items.ptr[1..self.capacity]",
                b"self.items.ptr[0..self.capacity + 1]"):
            with self.subTest(replacement=replacement), self.assertRaises(Unsupported):
                admission.admit(fixture().replace(b"self.items.ptr[0..self.capacity]", replacement), allocator_fixture())
        with self.assertRaises(Unsupported):
            admission.admit(fixture().replace(b"Slice { return", b"Slice { assert(self.items.len == 0); return"), allocator_fixture())

    def test_remap_empty_guard_precedes_external_callback(self):
        for before, after in (
                (b"if (allocation.len == 0) { return null; }", b""),
                (b"allocation.len == 0", b"allocation.len != 0"),
                (b"if (allocation.len == 0) { return null; }", b"if (allocation.len == 0) { return allocation; }"),
                (b"if (allocation.len == 0)", b"self.rawFree(allocation, .@\"8\", @returnAddress()); if (allocation.len == 0)"),
                (b"if (new_len == 0) { self.free(allocation); return allocation[0..0]; }\n    if (allocation.len == 0) { return null; }",
                 b"if (allocation.len == 0) { return null; } if (new_len == 0) { self.free(allocation); return allocation[0..0]; }"),
                (b"new_memory.len = new_len", b"new_memory.len = allocation.len"),
                (b"catch return null", b"catch unreachable"),
                (b"return @ptrCast(@alignCast(new_ptr[0..new_len_bytes]));", b"return allocation;")):
            self.assertEqual(allocator_fixture().count(before), 1)
            with self.subTest(statement=before), self.assertRaises(Unsupported):
                admission.admit(fixture(), allocator_fixture().replace(before, after))

    def test_free_empty_guard_precedes_effects(self):
        for before, after in (
                (b"if (bytes.len == 0) return;", b""),
                (b"bytes.len == 0", b"bytes.len != 0"),
                (b"if (bytes.len == 0) return;\n    @memset(bytes, undefined);", b"@memset(bytes, undefined); if (bytes.len == 0) return;"),
                (b"self.rawFree(bytes,", b"self.rawFree(memory,"),
                (b"@memset(bytes, undefined);", b"@memset(bytes, 0);")):
            self.assertEqual(allocator_fixture().count(before), 1)
            with self.subTest(statement=before), self.assertRaises(Unsupported):
                admission.admit(fixture(), allocator_fixture().replace(before, after))

    def test_complete_precise_caller_remains_bound(self):
        for before, after in (
                (b"try gpa.alignedAlloc", b"gpa.alignedAlloc"),
                (b"@memcpy(new_memory[0..self.items.len], self.items);", b"@memcpy(new_memory[0..self.capacity], self.items);"),
                (b"gpa.free(old_memory);", b"gpa.free(self.items);"),
                (b"const old_memory = self.allocatedSlice();", b"const old_memory = self.items;")):
            self.assertEqual(fixture().count(before), 1)
            with self.subTest(statement=before), self.assertRaises(Unsupported):
                admission.admit(fixture().replace(before, after), allocator_fixture())

    def test_duplicate_or_missing_wrapper_rejects(self):
        for allocator in (allocator_fixture() + allocator_fixture(), allocator_fixture().replace(b"pub fn remap", b"pub fn other")):
            with self.assertRaises(Unsupported):
                admission.admit(fixture(), allocator)

    def test_body_admission_does_not_replace_source_identity(self):
        with self.assertRaisesRegex(ValueError, "unreviewed"):
            admission.extract(fixture(), allocator_fixture())
        # Isolate the separately pinned Allocator file from ArrayList's identity
        # gate; ordinary extraction still requires both complete source hashes.
        with patch.object(admission.publication, "extract", return_value=admission.publication.OUTPUT.read_bytes()):
            with self.assertRaisesRegex(ValueError, "unreviewed representative allocator"):
                admission.extract(fixture(), allocator_fixture())


if __name__ == "__main__":
    unittest.main()
