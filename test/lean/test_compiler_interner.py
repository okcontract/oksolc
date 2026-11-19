#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Actual interner control extraction and fail-closed primitive admission.
"""
import sys
from pathlib import Path
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'lean'))
import extract_interner as extract
from extract_compiler import Unsupported
from test_compiler_storage import PUBLICATION_REJECTIONS

MUTATIONS = {
    'wrong_cache_hit': ('|existing| return existing;', '|existing| return 0;',
        '(findCode.run primitives request cached).1 = .ok 3'),
    'wrong_simplified_return': ('return simplified;', 'return 0;',
        '(findCode.run primitives request empty).1 = .ok 7'),
    'wrong_simplified_publication': ('lookup_key, simplified);', 'lookup_key, 0);',
        '(findCode.run primitives request empty).2.table key = some 7'),
    'wrong_forced_publication': ('self.publishOwned(key, id);', 'self.publishOwned(key, 0);',
        '(forceCode.run primitives (fun _ _ => .ok ()) 7 request.item request.arguments empty).2.table key = some 7'),
}


def mutated(name):
    data = extract.SOURCE.read_bytes()
    before, after, claim = MUTATIONS[name]
    if data.count(before.encode()) != 1:
        raise ValueError('mutation must target exactly one source span: ' + name)
    return extract.extract(data.replace(before.encode(), after.encode())), claim


class InternerTests(unittest.TestCase):
    def test_freshness(self):
        self.assertEqual(extract.extract(extract.SOURCE.read_bytes()), extract.OUTPUT.read_bytes())

    def test_semantic_mutations_are_executable_data(self):
        baseline = extract.OUTPUT.read_bytes().split(b'def findCode', 1)[1]
        for name in MUTATIONS:
            with self.subTest(name=name):
                self.assertNotEqual(mutated(name)[0].split(b'def findCode', 1)[1], baseline)

    def test_control_and_primitive_rejections(self):
        for before, after in [
            ('const deterministic = try SemanticInformation.isDeterministic(item);',
             'const deterministic = true;'),
            ('if (deterministic and item.item_type == .Operation)', 'if (deterministic)'),
            ('if (try RuleList.simplify(', 'if (RuleList.simplify('),
            ('try self.publishOwned(lookup_key, simplified);',
             'self.publishOwned(lookup_key, simplified) catch {};'),
            ('makeKey(item, lookup.items, sequence_number)', 'makeKey(item, lookup.items, 0)'),
            ('defer if (normalized_owned) self.allocator.free(normalized);',
             'defer self.allocator.free(normalized);'),
            ('_ = try self.representative(id);', '_ = self.representative(id);'),
            ('if (self.expressions.get(makeKey(item, lookup.items, 0)) != null)',
             'if (self.expressions.get(makeKey(item, lookup.items, 0)) == null)'),
            ('const key = makeKey(item, normalized, 0);', 'const key = makeKey(item, normalized, 1);'),
            ('defer if (owned) self.allocator.free(normalized);', 'defer self.allocator.free(normalized);'),
        ] + PUBLICATION_REJECTIONS:
            data = extract.SOURCE.read_bytes()
            self.assertIn(before.encode(), data)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(data.replace(before.encode(), after.encode()))

    def test_trivia_is_not_semantic(self):
        data = extract.SOURCE.read_bytes()
        self.assertEqual(extract.extract(data).split(b'def findCode', 1)[1],
            extract.extract(data + b'\n// comment only\n').split(b'def findCode', 1)[1])

    def test_ownership_handoff_rejections(self):
        for before, after in [
            ('defer lookup.deinit(self.allocator);', ''),
            ('var argument_buffer: [2]Id = undefined;', 'var argument_buffer: [3]Id = undefined;'),
            ('normalized_owned = false;\n        return self.insertOwned', 'return self.insertOwned'),
            ('try self.publishOwned(lookup_key, simplified);\n                normalized_owned = false;',
             'normalized_owned = false;\n                try self.publishOwned(lookup_key, simplified);'),
            ('try self.publishOwned(key, id);\n        owned = false;',
             'owned = false;\n        try self.publishOwned(key, id);'),
        ]:
            source = extract.SOURCE.read_bytes()
            self.assertIn(before.encode(), source)
            with self.subTest(before=before), self.assertRaises(Unsupported):
                extract.extract(source.replace(before.encode(), after.encode()))


if __name__ == '__main__':
    unittest.main()
