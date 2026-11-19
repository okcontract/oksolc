#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Admission and semantic mutation checks for the production ownership extractor.
The acceptance gate separately kernel-rejects each supported unsafe mutation.
"""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
import extract_storage as extraction
from test_compiler_extraction import mutate, semantic_part

PUBLICATION_REJECTIONS = [
    ("const entry = try self.expressions.getOrPut(self.allocator, key);",
     "const entry = self.expressions.getOrPut(self.allocator, key) catch return;"),
    ("if (entry.found_existing) self.allocator.free(entry.key_ptr.arguments);", ""),
    ("self.allocator.free(entry.key_ptr.arguments);", "self.allocator.free(key.arguments);"),
    ("if (entry.found_existing)", "if (!entry.found_existing)"),
    ("entry.key_ptr.* = key;", ""),
    ("entry.value_ptr.* = id;", "entry.value_ptr.* = 0;"),
    ("if (entry.found_existing) self.allocator.free(entry.key_ptr.arguments);\n        entry.key_ptr.* = key;",
     "entry.key_ptr.* = key;\n        if (entry.found_existing) self.allocator.free(entry.key_ptr.arguments);"),
]

# Input bits are deterministic, room, dupe, create, clone, append, publish.
MUTATIONS = {
    "aliased_buffer_double_free": (
        "normalized_owned = false;\n            break :blk normalized;",
        "normalized_owned = true;\n            break :blk normalized;",
        "false true true true true true true"),
    "published_key_freed": (
        "makeKey(item, normalized, sequence_number), id);\n            normalized_owned = false;",
        "makeKey(item, normalized, sequence_number), id);\n            normalized_owned = true;",
        "true true true true true true true"),
    "item_double_free": (
        "item_allocation_owned = false;\n        item_value_owned = false;",
        "item_allocation_owned = true;\n        item_value_owned = false;",
        "true true true true true true false"),
    "lost_rollback": (
        "self.representatives.items.len -= 1;", "", "true true true true true true false"),
    "lost_destruction": (
        "self.representatives.items[self.representatives.items.len - 1].deinit(self.allocator);",
        "", "true true true true true true false"),
    "defer_on_success": (
        "errdefer {\n            self.representatives", "defer {\n            self.representatives",
        "true true true true true true true"),
    "missing_item_cleanup": (
        "errdefer if (item_allocation_owned) self.allocator.destroy(owned_item);", "",
        "true true true true false true true"),
}

READ_MUTATIONS = {
    "bounds_safety_fault": (
        "pub fn representative(self: *const ExpressionClasses, id: Id) ExpressionError!*const Expression {\n        if (id >=",
        "pub fn representative(self: *const ExpressionClasses, id: Id) ExpressionError!*const Expression {\n        if (id >",
        "mutantRepresentative.run [] 0 = .error .invalidId"),
    "wrong_representative": (
        "return &self.representatives.items[id];\n    }\n\n    pub fn representativeMut",
        "return &self.representatives.items[0];\n    }\n\n    pub fn representativeMut",
        "(mutantRepresentative.run [{ item := ⟨2, none, 7⟩, otherValue := 0, itemAddress := 4 },"
        " { item := ⟨2, none, 13⟩, otherValue := 0, itemAddress := 8 }] 1).toOption.map Cell.value = some 13"),
    "false_constant": (
        "if (expression.item.item_type != .Push) return null;",
        "if (expression.item.item_type == .Push) return null;",
        "mutantConstant.run [{ item := ⟨0, none, 13⟩, otherValue := 7, itemAddress := 4 }] 0 = .ok none"),
    "wrong_operation_kind": (
        "if (expression.item.item_type != .Operation or",
        "if (expression.item.item_type == .Operation or",
        "mutantOperation.run [{ item := ⟨1, some 1, 0⟩, otherValue := 7, itemAddress := 4,"
        " arguments := [1, 2], argumentsAddress := 8 }] 0 1 = .ok (some ⟨8, [1, 2]⟩)"),
    "wrong_operation_opcode": (
        "expression.item.instruction_value.? != instruction) return null;",
        "expression.item.instruction_value.? == instruction) return null;",
        "mutantOperation.run [{ item := ⟨1, some 3, 0⟩, otherValue := 7, itemAddress := 4 }] 0 1 = .ok none"),
    "lost_operation_arguments": (
        "return expression.arguments;", "return &.{};",
        "mutantOperation.run [{ item := ⟨1, some 1, 0⟩, otherValue := 7, itemAddress := 4,"
        " arguments := [1, 2], argumentsAddress := 8 }] 0 1 = .ok (some ⟨8, [1, 2]⟩)"),
}


class StorageTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = extraction.SOURCE.read_bytes()

    def test_current_source(self):
        self.assertEqual(extraction.extract(self.source), extraction.OUTPUT.read_bytes())

    def test_semantic_mutations(self):
        original = semantic_part(extraction.extract(self.source))
        for name, (old, new, _) in MUTATIONS.items():
            with self.subTest(name=name):
                changed = extraction.extract(mutate(self.source, old, new))
                self.assertNotEqual(semantic_part(changed), original)

    def test_read_mutations(self):
        original = semantic_part(extraction.extract(self.source))
        for name, (old, new, _) in READ_MUTATIONS.items():
            with self.subTest(name=name):
                self.assertNotEqual(semantic_part(extraction.extract(mutate(self.source, old, new))), original)

    def test_unsupported_rejects(self):
        cases = [
            ("pub const Id = u32;", "pub const Id = u64;"),
            ("const owned_item = try self.allocator.create(AssemblyItem);",
             "const owned_item = self.allocator.create(AssemblyItem);"),
            ("const owned_item = try self.allocator.create(AssemblyItem);",
             "const owned_item = try self.allocator.create(Id);"),
            ("const owned_item = try self.allocator.create(AssemblyItem);",
             "const owned_item = try other_allocator.create(AssemblyItem);"),
            ("owned_item.* = try item.clone(self.allocator);", "owned_item.* = item.*;"),
            ("const id: Id = @intCast(self.representatives.items.len);\n        try self.representatives.append",
             "const id: Id = 0;\n        try self.representatives.append"),
            ("makeKey(item, normalized, sequence_number), id);", "makeKey(item, normalized, 0), id);"),
            ("errdefer if (item_value_owned) owned_item.deinit(self.allocator);",
             "errdefer if (item_value_owned) owned_item.deinit(other_allocator);"),
            ("representative_arguments_owned = false;", "representative_arguments_owned = unknown();"),
            (".Operation or\n            expression.item.instruction_value.?", ".Operation and\n            expression.item.instruction_value.?"),
            ("return expression.arguments;", "return self.representatives.items[0].arguments;"),
            ('@import("instruction.zig");', '@import("fake.zig");'),
            ("item: *AssemblyItem,", "item: AssemblyItem,"),
            ("arguments: []Id,\n    sequence_number", "arguments: []u64,\n    sequence_number"),
        ]
        for old, new in cases + PUBLICATION_REJECTIONS:
            with self.subTest(old=old):
                with self.assertRaises(extraction.Unsupported):
                    extraction.extract(mutate(self.source, old, new))

    def test_comments_are_not_semantics(self):
        self.assertEqual(semantic_part(extraction.extract(self.source)),
                         semantic_part(extraction.extract(b"// errdefer return id;\n" + self.source)))

    def test_capacity_limit_cannot_change_production_or_test_defaults(self):
        for before, after in (
            ('@import("builtin");', '@import("other.zig");'),
            ("pub const invalid_id = std.math.maxInt(Id);", "pub const invalid_id = 4;"),
            ("if (builtin.is_test) Id else void", "if (builtin.is_test) Id else Id"),
            ("if (builtin.is_test) invalid_id else {}", "if (builtin.is_test) 4 else {}"),
            ("return if (builtin.is_test) self.test_id_limit else invalid_id;",
             "return self.test_id_limit;"),
            ("return if (builtin.is_test) self.test_id_limit else invalid_id;",
             "return if (builtin.is_test) invalid_id else self.test_id_limit;"),
            ("defer if (normalized_owned) self.allocator.free(normalized);\n"
             "        if (self.representatives.items.len >= self.idLimit())",
             "defer if (normalized_owned) self.allocator.free(normalized);\n"
             "        if (self.representatives.items.len > self.idLimit())"),
        ):
            with self.subTest(mutation=after), self.assertRaises(extraction.Unsupported):
                extraction.extract(mutate(self.source, before, after))


if __name__ == "__main__":
    unittest.main()
