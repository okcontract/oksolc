#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Closed admission of actual find/forceEqual control flow. Allocator and cleanup
operations have an explicit semantic frame contract, not an erased error path.
"""
import argparse
import hashlib
from pathlib import Path
import re
from extract_compiler import Unsupported
from extract_storage import function, check_capacity_limit, check_publication

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'src/libevmasm/expression_classes.zig'
OUTPUT = ROOT / 'lean/Compiler/Extraction/InternerProgram.lean'


def result(p, expected):
    value = p.pop()
    if value == expected:
        return '.captured'
    if re.fullmatch(r'[0-9]+', value) and int(value) < 2**32:
        return '(.literal ' + value + ')'
    raise Unsupported('unmodeled result ID expression')


def extract(data):
    check_capacity_limit(data)
    check_publication(data)
    p = function(data, 'pub fn find(self: *ExpressionClasses, item: *const AssemblyItem, arguments: []const Id,'
                 ' _: bool, sequence_number: u32,) ExpressionError!Id')
    p.expect('{ if (self.representatives.items.len >= self.idLimit()) return error.ExpressionCapacity;'
        ' var argument_buffer: [2]Id = undefined;'
        ' var lookup = try NormalizedArguments.init(self.allocator, item, arguments, &argument_buffer);'
        ' defer lookup.deinit(self.allocator);'
        ' const deterministic = try SemanticInformation.isDeterministic(item);'
        ' if (deterministic) if (self.expressions.get(makeKey(item, lookup.items, sequence_number))) |existing| return')
    hit = result(p, 'existing')
    p.expect('; const normalized = try lookup.takeOwned(self.allocator); var normalized_owned = true;'
        ' defer if (normalized_owned) self.allocator.free(normalized);'
        ' const lookup_key = makeKey(item, normalized, sequence_number);'
        ' if (deterministic and item.item_type == .Operation) {'
        ' if (try RuleList.simplify(self, item.instruction_value.?, normalized, item.debug_data,)) |simplified| {'
        ' try self.publishOwned(lookup_key,')
    published = result(p, 'simplified')
    p.expect('); normalized_owned = false; return')
    simplified = result(p, 'simplified')
    p.expect('; } } normalized_owned = false; return self.insertOwned(item, normalized, deterministic, sequence_number); }')
    p = function(data, 'pub fn forceEqual(self: *ExpressionClasses, id: Id, item: *const AssemblyItem,'
                 ' arguments: []const Id, _: bool,) ExpressionError!void')
    p.expect('{ _ = try self.representative(id); var argument_buffer: [2]Id = undefined;'
        ' var lookup = try NormalizedArguments.init(self.allocator, item, arguments, &argument_buffer);'
        ' defer lookup.deinit(self.allocator);'
        ' if (self.expressions.get(makeKey(item, lookup.items, 0)) != null) return;'
        ' const normalized = try lookup.takeOwned(self.allocator); var owned = true;'
        ' defer if (owned) self.allocator.free(normalized);'
        ' const key = makeKey(item, normalized, 0); try self.publishOwned(key,')
    forced = result(p, 'id')
    p.expect('); owned = false; }')
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.InternerControl\n\nnamespace Compiler.Extraction.Interner\n\n'
        '-- Shared value/scoped control profile, including both ownership handoff sites.\n'
        '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
        'def findCode : FindCode := { hit := ' + hit + ', simplified := ' + simplified + ', published := ' + published + ' }\n\n'
        'def forceCode : ForceCode := { published := ' + forced + ' }\n\n'
        'end Compiler.Extraction.Interner\n').encode()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    output = extract(SOURCE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != output:
            p.error('interner extraction is stale; review source and proofs')
    else:
        OUTPUT.write_bytes(output)


if __name__ == '__main__':
    main()
