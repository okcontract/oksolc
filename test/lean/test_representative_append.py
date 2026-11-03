#!/usr/bin/env python3
"""Reject changed spare-capacity append bodies and owning std container fields.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import extract_representative_append as admission
import extract_storage as storage


def fixture():
    return b'''pub fn Aligned(comptime T: type, comptime alignment: ?mem.Alignment) type {
    if (alignment) |a| { if (a.toByteUnits() == @alignOf(T)) { return Aligned(T, null); } }
    return struct {
        const Self = @This(); items: Slice, capacity: usize, pointer_stability: debug.SafetyLock,
        pub const empty: Self = .{ .items = &.{}, .capacity = 0, .pointer_stability = .{}, };
        pub const Slice = []T;
        pub fn append(self: *Self, gpa: Allocator, item: T) Allocator.Error!void {
            const new_item_ptr = try self.addOne(gpa); new_item_ptr.* = item;
        }
        pub fn addOne(self: *Self, gpa: Allocator) Allocator.Error!*T {
            const newlen = self.items.len + 1; try self.ensureTotalCapacity(gpa, newlen);
            return self.addOneAssumeCapacity();
        }
        pub fn ensureTotalCapacity(self: *Self, gpa: Allocator, new_capacity: usize) Allocator.Error!void {
            if (self.capacity >= new_capacity) return;
            return self.ensureTotalCapacityPrecise(gpa, growCapacity(new_capacity));
        }
        pub fn addOneAssumeCapacity(self: *Self) *T {
            assert(self.items.len < self.capacity); self.items.len += 1;
            return &self.items[self.items.len - 1];
        }
    };
}
'''


class RepresentativeAppendAdmissionTests(unittest.TestCase):
    def test_complete_selected_factory(self):
        admission.admit_aligned(fixture())

    def test_changed_reached_statements_reject(self):
        for before, after in (
                (b"try self.addOne(gpa)", b"self.addOneAssumeCapacity()"),
                (b"new_item_ptr.* = item", b"new_item_ptr.* = undefined"),
                (b"self.items.len + 1", b"self.items.len + 2"),
                (b"try self.ensureTotalCapacity(gpa, newlen)", b"self.ensureTotalCapacity(gpa, newlen) catch {}"),
                (b"self.capacity >= new_capacity", b"self.capacity > new_capacity"),
                (b"return self.ensureTotalCapacityPrecise", b"self.ensureTotalCapacityPrecise"),
                (b"growCapacity(new_capacity)", b"new_capacity"),
                (b"assert(self.items.len < self.capacity)", b"assert(self.items.len <= self.capacity)"),
                (b"self.items.len += 1", b"self.items.len += 2"),
                (b"self.items.len - 1", b"0"),
                (b"new_item_ptr.* = item;", b"new_item_ptr.* = item; self.items.len = 0;")):
            self.assertEqual(fixture().count(before), 1)
            with self.subTest(statement=before), self.assertRaises(storage.Unsupported):
                admission.admit_aligned(fixture().replace(before, after))

    def test_increment_and_selection_order_is_bound(self):
        before = b"self.items.len += 1;\n            return &self.items[self.items.len - 1];"
        after = b"const result = &self.items[self.items.len - 1]; self.items.len += 1; return result;"
        self.assertEqual(fixture().count(before), 1)
        with self.assertRaises(storage.Unsupported):
            admission.admit_aligned(fixture().replace(before, after))

    def test_allocation_error_and_assignment_order_are_bound(self):
        for before, after in (
                (b"const new_item_ptr = try self.addOne(gpa); new_item_ptr.* = item;",
                 b"const new_item_ptr = self.addOne(gpa) catch return; new_item_ptr.* = item;"),
                (b"try self.ensureTotalCapacity(gpa, newlen); return self.addOneAssumeCapacity();",
                 b"const result = self.addOneAssumeCapacity(); try self.ensureTotalCapacity(gpa, newlen); return result;")):
            # Source fixtures keep their own formatting, so normalize whitespace
            # only to select the complete token sequence being corrupted.
            fixture_bytes = b" ".join(fixture().split())
            self.assertEqual(fixture_bytes.count(before), 1)
            with self.subTest(statement=before), self.assertRaises(storage.Unsupported):
                admission.admit_aligned(fixture_bytes.replace(before, after))

    def test_factory_scope_ignores_managed_names(self):
        managed = fixture().replace(b"pub fn Aligned(", b"pub fn AlignedManaged(").replace(b"self.items.len + 1", b"self.items.len + 2")
        admission.admit_aligned(managed + fixture())
        with self.assertRaises(storage.Unsupported):
            admission.admit_aligned(fixture() + fixture())

    def test_all_owner_fields_and_full_factory_tail_are_checked(self):
        for before, after in (
                (b"pointer_stability: debug.SafetyLock,", b""),
                (b".pointer_stability = .{},", b""),
                (b".pointer_stability = .{},", b".pointer_stability = undefined,"),
                (b"items: Slice", b"items: []u8"), (b"items: Slice, capacity: usize, pointer_stability: debug.SafetyLock,", b"items: Slice, capacity: u32,"),
                (b"pub const Slice", b"extra: usize = 0, pub const Slice"),
                (b"    };\n}", b"        extra: usize = 0,\n    };\n}"),
                (b"    };\n}", b"    }; allocator.free(self.items);\n}")):
            self.assertEqual(fixture().count(before), 1)
            with self.subTest(change=after), self.assertRaises(storage.Unsupported):
                admission.admit_aligned(fixture().replace(before, after))

    def test_parse_success_does_not_accept_unpinned_std(self):
        with self.assertRaisesRegex(ValueError, "unreviewed Zig"):
            admission.extract(storage.SOURCE.read_bytes(), fixture())


if __name__ == "__main__":
    unittest.main()
