#!/usr/bin/env python3
"""Admit the complete ArrayList(Expression) append dependency bodies.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

The emitted equations cover the capacity comparison, increment and new slot.
Execution proofs compose these bodies with the separately admitted capacity
policy and precise growth; nonempty relocation remains an open obligation.
"""
import argparse
import hashlib
from pathlib import Path

import extract_graph_init as graph
import extract_storage as storage

ROOT = storage.ROOT
OUTPUT = ROOT / "lean/Compiler/Extraction/RepresentativeAppendProgram.lean"
FACTORY = "pub fn Aligned(comptime T: type, comptime alignment: ?mem.Alignment) type"
PRELUDE = """{ if (alignment) |a| { if (a.toByteUnits() == @alignOf(T)) {
    return Aligned(T, null); } } return"""
FIELDS = """const Self = @This(); items: Slice, capacity: usize, pointer_stability: debug.SafetyLock,
    pub const empty: Self = .{ .items = &.{}, .capacity = 0, .pointer_stability = .{}, };"""
BODIES = {
    "append": ("pub fn append(self: *Self, gpa: Allocator, item: T) Allocator.Error!void",
        "const new_item_ptr = try self.addOne(gpa); new_item_ptr.* = item;"),
    "addOne": ("pub fn addOne(self: *Self, gpa: Allocator) Allocator.Error!*T",
        "const newlen = self.items.len + 1; try self.ensureTotalCapacity(gpa, newlen); return self.addOneAssumeCapacity();"),
    "ensureTotalCapacity": ("pub fn ensureTotalCapacity(self: *Self, gpa: Allocator, new_capacity: usize) Allocator.Error!void",
        "if (self.capacity >= new_capacity) return; return self.ensureTotalCapacityPrecise(gpa, growCapacity(new_capacity));"),
    "addOneAssumeCapacity": ("pub fn addOneAssumeCapacity(self: *Self) *T",
        "assert(self.items.len < self.capacity); self.items.len += 1; return &self.items[self.items.len - 1];"),
}


def admit_aligned(data):
    # The pinned file's top-level tests follow all declarations; they contain
    # quoted enum identifiers outside the existing restricted lexer. The whole
    # file is hash-bound below. No executable declaration is omitted from the
    # selected factory, whose complete struct fields and members are scanned.
    declarations = data.split(b'\ntest "', 1)[0]
    for name, (signature, body) in BODIES.items():
        owner = storage.function(declarations, FACTORY)
        owner.expect(PRELUDE)
        member = storage.struct_member_body(owner, FIELDS, name, signature)
        owner.expect("}")
        member.expect(body)
        if member.pos != len(member.items):
            raise storage.Unsupported("extra representative append behavior: " + name)


def extract(source, array_list):
    if storage.extract(source) != storage.OUTPUT.read_bytes() or graph.extract(source) != graph.OUTPUT.read_bytes():
        raise ValueError("representative append insertion/owner admission is stale")
    # Review the complete reached bodies even for a rejected library identity.
    admit_aligned(array_list)
    std_hash = hashlib.sha256(array_list).hexdigest()
    if std_hash != graph.STD["array_list.zig"]:
        raise ValueError("unreviewed Zig representative append implementation")
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "namespace Compiler.Extraction.RepresentativeArray.Append\n\n"
        "-- Admitted insertOwned descriptor and unmanaged Aligned append helpers.\n"
        "-- Growth/relocation is retained in admission and not covered by these equations.\n"
        "-- Source SHA-256: " + hashlib.sha256(source).hexdigest() + "\n"
        "-- std/array_list.zig SHA-256: " + std_hash + "\n"
        "def nextLength (length : Nat) : Nat := length + 1\n"
        "def hasCapacity (capacity newLength : Nat) : Bool := decide (capacity ≥ newLength)\n"
        "def selectedIndex (newLength : Nat) : Nat := newLength - 1\n\n"
        "end Compiler.Extraction.RepresentativeArray.Append\n").encode()


def check(lib):
    graph.check_std(lib)
    data = extract(storage.SOURCE.read_bytes(), (Path(lib) / "std/array_list.zig").read_bytes())
    if data != OUTPUT.read_bytes():
        raise ValueError("representative append program admission is stale")
    return {"sourceSha256": hashlib.sha256(storage.SOURCE.read_bytes()).hexdigest(),
        "programSha256": hashlib.sha256(data).hexdigest(), "pinnedStd": graph.STD.copy(),
        "scope": "complete append helpers; execution checked separately", "nativeGrowthVerified": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zig-lib-dir", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.check:
        check(args.zig_lib_dir)
    else:
        graph.check_std(args.zig_lib_dir)
        OUTPUT.write_bytes(extract(storage.SOURCE.read_bytes(), (args.zig_lib_dir / "std/array_list.zig").read_bytes()))
