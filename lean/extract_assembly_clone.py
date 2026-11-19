#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Extract AssemblyItem.clone/deinit. Parsing, field projection and the allocator
dupe/free primitives remain trusted; unsupported source fails closed.
"""
import argparse
import hashlib
from pathlib import Path
import re

from extract_compiler import Unsupported
from extract_assembly_item import member_body

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'src/libevmasm/assembly_item.zig'
OUTPUT = ROOT / 'lean/Compiler/Extraction/AssemblyCloneProgram.lean'


def counter(p, field):
    if p.take('verbatim'):
        p.expect('.' + field)
        return '.input'
    value = p.pop()
    if not re.fullmatch(r'[0-9]+', value):
        raise Unsupported('unmodeled cloned payload counter')
    return '(.literal ' + value + ')'


def extract(data):
    p = member_body(data, 'clone', 'pub fn clone(self: *const AssemblyItem, allocator: std.mem.Allocator) std.mem.Allocator.Error!AssemblyItem')
    p.expect('var result = self.*;')
    copies = p.take('if')
    arguments = returns = contents = '.input'
    if copies:
        p.expect('(self.verbatim) |verbatim| { result.verbatim = .{ .arguments =')
        arguments = counter(p, 'arguments')
        p.expect(', .return_variables =')
        returns = counter(p, 'return_variables')
        p.expect(', .data = try allocator.dupe(u8,')
        if p.take('verbatim'):
            p.expect('.data')
        else:
            p.expect('&.{}')
            contents = '(.literal [])'
        p.expect('), }; }')
    p.expect('return')
    if p.take('result'):
        returned_copy = True
    else:
        p.expect('self.*')
        returned_copy = False
    p.expect(';')
    if p.pos != len(p.items):
        raise Unsupported('unmodeled clone suffix')
    p = member_body(data, 'deinit', 'pub fn deinit(self: *AssemblyItem, allocator: std.mem.Allocator) void')
    frees = p.take('if')
    if frees:
        p.expect('(self.verbatim) |verbatim| allocator.free(verbatim.data);')
    invalidates = p.take('self')
    if invalidates:
        p.expect('.* = undefined;')
    if p.pos != len(p.items):
        raise Unsupported('unmodeled destructor suffix')
    return ('/-\n// SPDX-License-Identifier: GPL-3.0\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n-/\n'
        'import Compiler.Extraction.AssemblyClone\n\nnamespace Compiler.Extraction.AssemblyClone\n\n'
        '-- AssemblyItem source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
        'def cloneCode : CloneCode := { copyPayload := ' + str(copies).lower() +
        ', arguments := ' + arguments + ', returns := ' + returns + ', contents := ' + contents +
        ', returnCopy := ' + str(returned_copy).lower() + ' }\n'
        'def deinitCode : DeinitCode := { freePayload := ' + str(frees).lower() +
        ', invalidate := ' + str(invalidates).lower() + ' }\n\nend Compiler.Extraction.AssemblyClone\n').encode()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = extract(SOURCE.read_bytes())
    if args.check:
        if OUTPUT.read_bytes() != result:
            parser.error('assembly clone extraction is stale; review source and proofs')
    else:
        OUTPUT.write_bytes(result)


if __name__ == '__main__':
    main()
