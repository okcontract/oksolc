#!/usr/bin/env python3
"""Admit first representative growth without assuming a remap contract.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

The nonzero Expression layout excludes the zero-sized-element branch. Empty
old capacity makes Allocator.remap return null before its external callback.
Existing nonempty growth remains an explicit unsupported scope.
"""
import argparse
import hashlib
from pathlib import Path

import extract_representative_publication as publication
import extract_storage as storage

OUTPUT = storage.ROOT / "lean/Compiler/Extraction/RepresentativeGrowthProgram.lean"
ALLOCATOR_SHA256 = "25099a1aaed1fe80b811e1eaedf8c3e2059a3fe7b6c29db868a68da3085b7997"
REMAP = """
    const slice_info = @typeInfo(@TypeOf(allocation)).pointer;
    const T = if (slice_info.size != .slice) comptime T: {
        assert(slice_info.size == .one);
        break :T @typeInfo(slice_info.child).array.child;
    } else slice_info.child;
    if (new_len == 0) { self.free(allocation); return allocation[0..0]; }
    if (allocation.len == 0) { return null; }
    if (@sizeOf(T) == 0) { var new_memory = allocation; new_memory.len = new_len; return new_memory; }
    const old_memory: []u8 = @ptrCast(@constCast(mem.absorbSentinel(allocation)));
    const new_len_bytes = math.mul(usize, @sizeOf(T), new_len) catch return null;
    const new_ptr = self.rawRemap(old_memory, .fromByteUnits(slice_info.attrs.@"align" orelse @alignOf(T)),
        new_len_bytes, @returnAddress(),) orelse return null;
    return @ptrCast(@alignCast(new_ptr[0..new_len_bytes]));
"""
FREE = """
    const slice_info = @typeInfo(@TypeOf(memory)).pointer;
    if (slice_info.size != .slice) {
        comptime assert(slice_info.size == .one and @typeInfo(slice_info.child) == .array);
    }
    const bytes: []u8 = @ptrCast(@constCast(mem.absorbSentinel(memory)));
    if (bytes.len == 0) return;
    @memset(bytes, undefined);
    self.rawFree(bytes, .fromByteUnits(slice_info.attrs.@"align" orelse @alignOf(slice_info.child)), @returnAddress());
"""


def admit(array_list, allocator):
    publication.admit(array_list)
    owner = storage.function(array_list.split(b'\ntest "', 1)[0], publication.append.FACTORY)
    owner.expect(publication.append.PRELUDE)
    body = storage.struct_member_body(owner, publication.append.FIELDS, "allocatedSlice", "pub fn allocatedSlice(self: Self) Slice")
    owner.expect("}")
    body.expect("return self.items.ptr[0..self.capacity];")
    if body.pos != len(body.items):
        raise storage.Unsupported("extra representative allocated-slice behavior")
    for signature, expected in (
            ("pub fn remap(self: Allocator, allocation: anytype, new_len: usize) ?Slice(AbsorbSentinel(@TypeOf(allocation)))", REMAP),
            ("pub fn free(self: Allocator, memory: anytype) void", FREE)):
        storage.function(allocator, signature).expect("{" + expected + "}")


def extract(array_list, allocator):
    admit(array_list, allocator)
    if publication.extract(array_list) != publication.OUTPUT.read_bytes():
        raise ValueError("representative publication admission is stale")
    if hashlib.sha256(allocator).hexdigest() != ALLOCATOR_SHA256:
        raise ValueError("unreviewed representative allocator wrapper")
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "namespace Compiler.Extraction.RepresentativeArray.Growth\n\n"
        "-- Nonzero captured Expression layout; complete growth and remap bodies admitted.\n"
        "-- For positive new capacity, zero old capacity returns null before rawRemap.\n"
        "-- Nonempty growth requires separately admitted remap callback execution.\n"
        "-- std/array_list.zig SHA-256: " + publication.append.graph.STD["array_list.zig"] + "\n"
        "-- std/mem/Allocator.zig SHA-256: " + ALLOCATOR_SHA256 + "\n"
        "inductive Branch where | unchanged | firstAllocation | existingGrowth deriving DecidableEq\n"
        "def choose (oldCapacity newCapacity : Nat) : Branch :=\n"
        "  if oldCapacity ≥ newCapacity then .unchanged else\n"
        "  if oldCapacity = 0 then .firstAllocation else .existingGrowth\n\n"
        "end Compiler.Extraction.RepresentativeArray.Growth\n").encode()


def check(lib):
    lib = Path(lib)
    data = extract((lib / "std/array_list.zig").read_bytes(), (lib / "std/mem/Allocator.zig").read_bytes())
    if data != OUTPUT.read_bytes():
        raise ValueError("representative first-growth admission is stale")
    return {"programSha256": hashlib.sha256(data).hexdigest(), "allocatorSha256": ALLOCATOR_SHA256,
        "scope": "unchanged capacity and first allocation", "nativeGrowthVerified": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zig-lib-dir", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.check:
        check(args.zig_lib_dir)
    else:
        OUTPUT.write_bytes(extract((args.zig_lib_dir / "std/array_list.zig").read_bytes(),
            (args.zig_lib_dir / "std/mem/Allocator.zig").read_bytes()))
