#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Actual key/normalization extraction and fail-closed primitive admission.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_cache as extract
from extract_compiler import Unsupported

MUTATIONS = {
    'missing_transfer_clear': ('source', 'self.owned = null;', '',
        '(normalizationOwnershipCode.run true 3 2 true false .transfer).2.invalid = false'),
    'missing_lookup_free': ('source', 'if (self.owned) |owned| allocator.free(owned);', '',
        '(normalizationOwnershipCode.run true 3 2 true false .lookup).2.owner = .released'),
    'own_exact_fit_scratch': ('source', '.owned = if (arguments.len > buffer.len)',
        '.owned = if (arguments.len >= buffer.len)',
        '(normalizationOwnershipCode.run true 2 2 true true .lookup).2.invalid = false'),
    'oversized_scratch': ('source', 'const normalized = if (arguments.len <= buffer.len)',
        'const normalized = if (arguments.len >= buffer.len)',
        '(normalizationOwnershipCode.run true 3 2 true true .lookup).2.invalid = false'),
    'lost_sequence_comparison': ('source', 'left.sequence_number == right.sequence_number and', '',
        'equal equalityFields ⟨2, 0, 7, [], 0⟩ ⟨2, 0, 7, [], 1⟩ = false'),
    'lost_argument_comparison': ('source', ' and\n            std.mem.eql(Id, left.arguments, right.arguments)', '',
        'equal equalityFields ⟨1, 1, 0, [0], 0⟩ ⟨1, 1, 0, [1], 0⟩ = false'),
    'lost_constant_value': ('source', '0 else item.data_value,', '0 else 0,',
        'keyCode.run ⟨2, none, 7⟩ [] 0 = some ⟨2, 0, 7, [], 0⟩'),
    'lost_sequence_value': ('source', '.sequence_number = sequence_number,\n    };', '.sequence_number = 0,\n    };',
        'keyCode.run ⟨2, none, 7⟩ [] 1 = some ⟨2, 0, 7, [], 1⟩'),
    'wrong_instruction_guard': ('source', '.instruction = if (item.item_type == .Operation)',
        '.instruction = if (item.item_type != .Operation)',
        'keyCode.run ⟨1, some 3, 0⟩ [0, 1] 0 = some ⟨1, 3, 0, [0, 1], 0⟩'),
    'commutative_subtraction': ('semantics', '.ADD, .MUL, .EQ, .AND, .OR, .XOR => true',
        '.SUB, .ADD, .MUL, .EQ, .AND, .OR, .XOR => true',
        'normalizeCode.commutative.contains 3 = true → Binary.sub.eval 1 2 = Binary.sub.eval 2 1'),
}


def inputs():
    return {n: p.read_bytes() for n, p in [('source',extract.SOURCE), ('semantics',extract.SEMANTICS),
        ('items',extract.ITEMS), ('opcodes',extract.OPCODES)]}


def generate(values):
    return extract.extract(values['source'], values['semantics'], values['items'], values['opcodes'])


def mutated(name):
    values = inputs()
    target, before, after, claim = MUTATIONS[name]
    if values[target].count(before.encode()) != 1:
        raise ValueError('mutation must target exactly one source span: ' + name)
    values[target] = values[target].replace(before.encode(), after.encode())
    return generate(values), claim


class CacheTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(generate(inputs()), extract.OUTPUT.read_bytes())

    def test_semantic_mutations_are_executable_data(self):
        baseline = generate(inputs()).split(b'def keyCode', 1)[1]
        for name in MUTATIONS:
            with self.subTest(name=name):
                changed, _ = mutated(name)
                self.assertNotEqual(changed.split(b'def keyCode', 1)[1], baseline)

    def test_primitive_and_type_rejections(self):
        for target, before, after in [
            ('source','pub const Id = u32;', 'pub const Id = u64;'),
            ('source','instruction: u8,', 'instruction: u16,'),
            ('source','@memcpy(normalized, arguments);', '@memcpy(arguments, normalized);'),
            ('source','try allocator.alloc(Id, arguments.len)', 'allocator.alloc(Id, arguments.len)'),
            ('source','std.sort.asc(Id)', 'std.sort.desc(Id)'),
            ('source','owned: ?[]Id = null,', 'owned: ?[]Id = undefined,'),
            ('source','allocator.free(owned);', 'allocator.free(self.items);'),
            ('source','return allocator.dupe(Id, self.items);', 'return self.items;'),
            ('source','return allocator.dupe(Id, self.items);', 'return allocator.dupe(Id, &.{});'),
            ('source','self.owned = null;', 'self.owned = owned;'),
            ('source','.arguments = arguments,\n        .sequence_number = sequence_number,',
                '.arguments = &.{},\n        .sequence_number = sequence_number,'),
            ('items','UndefinedItem,\n    Operation,', 'Operation,\n    UndefinedItem,'),
            ('opcodes','enum(u8)', 'enum(u16)'),
            ('opcodes','ADD = 0x01,', 'ADD = (0x01), // ADD = 0x01,'),
        ]:
            values = inputs()
            self.assertIn(before.encode(), values[target])
            values[target] = values[target].replace(before.encode(), after.encode())
            with self.subTest(target=target, before=before), self.assertRaises(Unsupported):
                generate(values)

    def test_trivia_is_not_semantic(self):
        values = inputs()
        baseline = generate(values).split(b'def keyCode', 1)[1]
        values['source'] += b'\n// comment only\n'
        values['opcodes'] += b'\n// ADD = 0x03,\n'
        self.assertEqual(generate(values).split(b'def keyCode', 1)[1], baseline)


if __name__ == '__main__':
    unittest.main()
