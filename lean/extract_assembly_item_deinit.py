#!/usr/bin/env python3
"""Bind the complete AssemblyItem.deinit body and its owned byte field.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
from extract_storage import ROOT, Unsupported
from extract_assembly_item import member_body

SOURCE = ROOT / 'src/libevmasm/assembly_item.zig'
OUTPUT = ROOT / 'lean/Compiler/Extraction/AssemblyItemDeinitProgram.lean'


def extract(data):
    parser = member_body(data, 'deinit', 'pub fn deinit(self: *AssemblyItem, allocator: std.mem.Allocator) void')
    stages = []
    while parser.pos < len(parser.items):
        if parser.take('if'):
            parser.expect('(self.verbatim) |verbatim| allocator.free(verbatim.data);')
            stages.append('.payload')
        else:
            parser.expect('self.* = undefined;')
            stages.append('.invalidate')
    return ('/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n'
            'import Compiler.Extraction.AssemblyItemDeinit\n\n'
            'namespace Compiler.Extraction.AssemblyItemDeinit\n\n'
            '-- Generated from the complete production AssemblyItem.deinit body.\n'
            '-- Source SHA-256: ' + hashlib.sha256(data).hexdigest() + '\n'
            'def assemblyItemDeinitCode : List Stage := [' + ', '.join(stages) + ']\n\n'
            'end Compiler.Extraction.AssemblyItemDeinit\n').encode()


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generated = extract(SOURCE.read_bytes())
    if args.check:
        if generated != OUTPUT.read_bytes():
            parser.error('assembly item destructor extraction is stale; review source and proofs')
    else:
        OUTPUT.write_bytes(generated)
