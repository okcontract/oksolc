#!/usr/bin/env python3
"""Source binding and closed admission for production interner queries.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import copy
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'lean'))
import extract_interner_queries as extraction
import capture_interner_queries as native


class QueryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.sources = [p.read_bytes() for p in (extraction.cache.SOURCE, extraction.cache.SEMANTICS,
                                               extraction.cache.ITEMS, extraction.cache.OPCODES)]

    def mutate(self, index, before, after):
        sources = list(self.sources)
        self.assertEqual(sources[index].count(before.encode()), 1)
        sources[index] = sources[index].replace(before.encode(), after.encode())
        return extraction.extract(*sources)

    def test_current_source(self):
        self.assertEqual(extraction.extract(*self.sources), extraction.OUTPUT.read_bytes())

    def test_semantic_changes_are_translated(self):
        original = extraction.extract(*self.sources).split(b'def determinismCode')[1]
        for index, before, after in (
            (1, 'if (item.item_type == .VerbatimBytecode) return error.AssemblyException;',
                'if (item.item_type != .VerbatimBytecode) return error.AssemblyException;'),
            (1, 'if (!item.hasInstruction()) return true;', 'if (!item.hasInstruction()) return false;'),
            (2, 'const should_have_instruction = self.item_type == .Operation;',
                'const should_have_instruction = self.item_type != .Operation;'),
            (2, 'std.debug.assert(should_have_instruction == (self.instruction_value != null));', ''),
            (3, 'BALANCE = 0x31,', 'BALANCE = 0x30,')):
            with self.subTest(after=after):
                self.assertNotEqual(self.mutate(index, before, after).split(b'def determinismCode')[1], original)

    def test_unsupported_source_fails_closed(self):
        for index, before, after in (
            (1, 'if (!item.hasInstruction()) return true;', 'if (!item.hasInstruction()) return item.data_value == 0;'),
            (1, 'if (item.item_type == .VerbatimBytecode) return error.AssemblyException;',
                'if (item.item_type == .VerbatimBytecode) return false;'),
            (2, 'return should_have_instruction;', 'return true;'),
            (2, 'std.debug.assert(should_have_instruction == (self.instruction_value != null));',
                'std.debug.assert(should_have_instruction == (self.instruction_value == null));'),
            (0, 'pub const Id = u32;', 'pub const Id = u64;'),
            (0, 'if (id >= self.representatives.items.len) return error.InvalidExpressionId;\n        return &self.representatives.items[id];\n    }\n\n    pub fn representativeMut',
                'return &self.representatives.items[id];\n    }\n\n    pub fn representativeMut')):
            with self.subTest(after=after), self.assertRaises(extraction.storage.Unsupported):
                self.mutate(index, before, after)

    def test_duplicate_functions_are_rejected(self):
        sources = list(self.sources)
        sources[1] += b'\npub fn isDeterministic(item: *const AssemblyItemModule.AssemblyItem) error{AssemblyException}!bool { return true; }\n'
        with self.assertRaises(extraction.storage.Unsupported):
            extraction.extract(*sources)

    def test_native_case_inventory(self):
        profile = {'schema': 'oksolc.interner-query-observations.v1', 'zigVersion': '0.17.0',
                   'mode': 'Debug', 'backend': 'stage2_llvm', 'cases': native.expected_cases()}
        native.check_profile(profile, 'Debug')
        self.assertEqual(len(profile['cases']), 525)
        self.assertEqual(len({(r['kind'], r['instruction']) for r in profile['cases']}), 525)
        for label, change in (
            ('missing-case', lambda p: p['cases'].pop()),
            ('duplicate-case', lambda p: p['cases'].append(p['cases'][0])),
            ('wrong-result', lambda p: p['cases'][0].update(result='nondeterministic')),
            ('bool-tag', lambda p: p['cases'][0].update(kind=False)),
            ('bad-opcode', lambda p: p['cases'][1].update(instruction=256)),
            ('extra-field', lambda p: p.update(accepted=True)),
            ('wrong-mode', lambda p: p.update(mode='ReleaseFast')),
            ('wrong-version', lambda p: p.update(zigVersion='0.15.0')),
            ('wrong-backend', lambda p: p.update(backend='stage2_aarch64'))):
            changed = copy.deepcopy(profile)
            change(changed)
            with self.subTest(label=label), self.assertRaises(ValueError):
                native.check_profile(changed, 'Debug')


if __name__ == '__main__':
    unittest.main()
