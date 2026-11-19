#!/usr/bin/env python3
"""Extract Expression.deinit for insertion rollback, preserving operation order.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import argparse
import hashlib
from extract_storage import ROOT, SOURCE, Unsupported, function

OUTPUT = ROOT / "lean/Compiler/Extraction/ExpressionDeinitProgram.lean"


def extract(data):
    for header, body in (
        ('const std =', '@import("std");'),
        ('const AssemblyItemModule =', '@import("assembly_item.zig");'),
        ('const AssemblyItem =', 'AssemblyItemModule.AssemblyItem;'),
        ('const Id =', 'u32;'),
    ):
        function(data, header).expect(body)
    # Continue within the admitted owner, rather than accepting a same-named
    # function elsewhere in the file. Global type/import bindings are unique.
    parser = function(data, "const Expression =")
    parser.expect("struct { id: Id, item: *AssemblyItem, arguments: []Id, sequence_number: u32 = 0,"
                  " fn deinit(self: *Expression, allocator: std.mem.Allocator) void {")
    stages = []
    while not parser.take("}"):
        if parser.take("self"):
            parser.expect(".")
            if parser.take("item"):
                parser.expect(".deinit(allocator);")
                stages.append(".itemValue")
            elif parser.take("*"):
                parser.expect("= undefined;")
                stages.append(".invalidate")
            else:
                raise Unsupported("unsupported expression destructor receiver")
        elif parser.take("allocator"):
            parser.expect(".")
            action = parser.pop()
            if action == "destroy":
                parser.expect("(self.item);")
                stages.append(".itemAllocation")
            elif action == "free":
                parser.expect("(self.arguments);")
                stages.append(".arguments")
            else:
                raise Unsupported("unsupported expression destructor allocator operation")
        else:
            raise Unsupported("unsupported expression destructor statement")
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
            "import Compiler.Extraction.ExpressionDeinit\n\n"
            "namespace Compiler.Extraction.ExpressionDeinit\n\n"
            "-- Generated from the production Expression.deinit body.\n"
            "-- Source SHA-256: " + hashlib.sha256(data).hexdigest() + "\n"
            "def expressionDeinitCode : List Stage := [" + ", ".join(stages) + "]\n\n"
            "end Compiler.Extraction.ExpressionDeinit\n").encode()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    generated = extract(SOURCE.read_bytes())
    if args.check:
        if generated != OUTPUT.read_bytes():
            parser.error("expression destructor extraction is stale; review source and proofs")
    else:
        OUTPUT.write_bytes(generated)
