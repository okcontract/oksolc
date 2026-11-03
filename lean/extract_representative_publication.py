#!/usr/bin/env python3
"""Admit the shared pointer/capacity publication suffix of ArrayList growth.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

Both complete growth branches are checked. Only their publication assignments
are emitted here; remap, allocation, copy and release remain caller obligations.
"""
import argparse
import hashlib
from pathlib import Path

import extract_representative_append as append
import extract_storage as storage

OUTPUT = storage.ROOT / "lean/Compiler/Extraction/RepresentativePublicationProgram.lean"
SIGNATURE = "pub fn ensureTotalCapacityPrecise(self: *Self, gpa: Allocator, new_capacity: usize) Allocator.Error!void"
BODY = """
    self.pointer_stability.assertUnlocked();
    if (@sizeOf(T) == 0) { self.capacity = math.maxInt(usize); return; }
    if (self.capacity >= new_capacity) return;
    const old_memory = self.allocatedSlice();
    if (gpa.remap(old_memory, new_capacity)) |new_memory| {
        self.items.ptr = new_memory.ptr;
        self.capacity = new_memory.len;
    } else {
        const new_memory = try gpa.alignedAlloc(T, alignment, new_capacity);
        @memcpy(new_memory[0..self.items.len], self.items);
        gpa.free(old_memory);
        self.items.ptr = new_memory.ptr;
        self.capacity = new_memory.len;
    }
"""


def admit(array_list):
    declarations = array_list.split(b'\ntest "', 1)[0]
    owner = storage.function(declarations, append.FACTORY)
    owner.expect(append.PRELUDE)
    body = storage.struct_member_body(owner, append.FIELDS, "ensureTotalCapacityPrecise", SIGNATURE)
    owner.expect("}")
    body.expect(BODY)
    if body.pos != len(body.items):
        raise storage.Unsupported("extra representative growth behavior")


def extract(array_list):
    admit(array_list)
    digest = hashlib.sha256(array_list).hexdigest()
    if digest != append.graph.STD["array_list.zig"]:
        raise ValueError("unreviewed representative growth implementation")
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "namespace Compiler.Extraction.RepresentativeArray.Publication\n\n"
        "-- Shared reached suffix of both ensureTotalCapacityPrecise growth branches.\n"
        "-- New-memory evaluation and preceding effects remain caller obligations.\n"
        "-- std/array_list.zig SHA-256: " + digest + "\n"
        "inductive Update where | itemsPointer | capacity deriving DecidableEq\n"
        "def program : List Update := [.itemsPointer, .capacity]\n\n"
        "end Compiler.Extraction.RepresentativeArray.Publication\n").encode()


def check(lib):
    # The caller's append gate also checks the compiler owner and all pinned std
    # dependencies. This gate binds the exact complete growth body and suffix.
    data = extract((Path(lib) / "std/array_list.zig").read_bytes())
    if data != OUTPUT.read_bytes():
        raise ValueError("representative publication admission is stale")
    return {"programSha256": hashlib.sha256(data).hexdigest(),
        "arrayListSha256": append.graph.STD["array_list.zig"],
        "scope": "reached pointer-then-capacity publication", "nativeGrowthVerified": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zig-lib-dir", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.check:
        check(args.zig_lib_dir)
    else:
        OUTPUT.write_bytes(extract((args.zig_lib_dir / "std/array_list.zig").read_bytes()))
