#!/usr/bin/env python3
"""Bind the refusing remap callback without adding an allocator assumption.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Callback identity is an explicit admission input. Other vtable targets remain
unsupported; this does not infer a target from an allocator's logical brand.
"""
import argparse
import hashlib
from pathlib import Path

import extract_representative_growth as growth
import extract_storage as storage

OUTPUT = storage.ROOT / 'lean/Compiler/Extraction/RepresentativeRemapProgram.lean'
SIGNATURE = 'pub fn noRemap(self: *anyopaque, memory: []u8, alignment: Alignment, new_len: usize, ret_addr: usize,) ?[*]u8'
BODY = '_ = self; _ = memory; _ = alignment; _ = new_len; _ = ret_addr; return null;'
RAW_SIGNATURE = 'pub inline fn rawRemap(a: Allocator, memory: []u8, alignment: Alignment, new_len: usize, ret_addr: usize) ?[*]u8'
RAW_BODY = 'return a.vtable.remap(a.ptr, memory, alignment, new_len, ret_addr);'


def admit(array_list, allocator):
    growth.admit(array_list, allocator)
    storage.function(allocator, SIGNATURE).expect('{' + BODY + '}')
    storage.function(allocator, RAW_SIGNATURE).expect('{' + RAW_BODY + '}')


def extract(array_list, allocator):
    admit(array_list, allocator)
    if growth.extract(array_list, allocator) != growth.OUTPUT.read_bytes():
        raise ValueError('representative growth admission is stale')
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "namespace Compiler.Extraction.RepresentativeArray.Remap\n\n"
        "-- std/mem/Allocator.zig SHA-256: " + hashlib.sha256(allocator).hexdigest() + "\n"
        "-- Complete noRemap body; callback identity must be bound at the caller.\n"
        "-- Other remap implementations have no admitted preservation contract.\n"
        "def noRemap (_context _base _bytes _alignment _newBytes _returnAddress : Nat) : Option Nat := none\n\n"
        "end Compiler.Extraction.RepresentativeArray.Remap\n").encode()


def check(lib):
    lib = Path(lib)
    data = extract((lib / 'std/array_list.zig').read_bytes(), (lib / 'std/mem/Allocator.zig').read_bytes())
    if data != OUTPUT.read_bytes():
        raise ValueError('representative remap admission is stale')
    return {'programSha256': hashlib.sha256(data).hexdigest(), 'allocatorSha256': growth.ALLOCATOR_SHA256,
            'callback': 'std.mem.Allocator.noRemap', 'callbackIdentityDerivedFromOwner': False,
            'otherRemapImplementationsVerified': False}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--zig-lib-dir', type=Path, required=True)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    if args.check:
        check(args.zig_lib_dir)
    else:
        OUTPUT.write_bytes(extract((args.zig_lib_dir / 'std/array_list.zig').read_bytes(),
            (args.zig_lib_dir / 'std/mem/Allocator.zig').read_bytes()))
