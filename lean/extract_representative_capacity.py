#!/usr/bin/env python3
"""Admit representative capacity selection for the captured aarch64 target.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

The pinned library's policy constant is 128 on aarch64, independently of CPU
features. This is a source-policy value, not a claim about hardware cache size.
The nonzero captured Expression size is 32, giving an initial capacity of four.
"""
import argparse
import hashlib
from pathlib import Path

import extract_representative_append as append
import extract_storage as storage

OUTPUT = storage.ROOT / "lean/Compiler/Extraction/RepresentativeCapacityProgram.lean"
ATOMIC_SHA256 = "85b467837478ff64aba29bf52cf9eef9b973ddb3ec6b5472901500a8e4a925c5"
CACHE_LINE = """{
    return switch (cpu.arch) {
        .x86_64, .aarch64, .aarch64_be, .arc, .arceb, .powerpc64, .powerpc64le, => 128,
        .hexagon, => if (cpu.has(.hexagon, .v73)) 64 else 32,
        .arm, .armeb, .thumb, .thumbeb, .m88k, .microblaze, .microblazeel,
        .mips, .mipsel, .mips64, .mips64el, .sh, .sheb, .sparc, .sparc64, => 32,
        .hppa, .hppa64, .m68k, .or1k, => 16,
        .msp430, => 8,
        .s390x, .ve, => 256,
        else => 64,
    };
}"""


def admit(array_list, atomic):
    append.admit_aligned(array_list)
    owner = storage.function(array_list.split(b'\ntest "', 1)[0], append.FACTORY)
    owner.expect(append.PRELUDE)
    body = storage.struct_member_body(owner, append.FIELDS, "growCapacity", "pub fn growCapacity(minimum: usize) usize")
    owner.expect("}")
    body.expect("""if (@sizeOf(T) == 0) return math.maxInt(usize);
        const init_capacity: comptime_int = @max(1, std.atomic.cache_line / @sizeOf(T));
        return minimum +| (minimum / 2 + init_capacity);""")
    if body.pos != len(body.items):
        raise storage.Unsupported("extra representative capacity behavior")
    storage.function(atomic, "pub fn cacheLineForCpu(cpu: std.Target.Cpu) u16").expect(CACHE_LINE)
    storage.function(atomic, "pub const cache_line: comptime_int =").expect("cacheLineForCpu(builtin.cpu);")


def extract(source, array_list, atomic):
    admit(array_list, atomic)
    if append.extract(source, array_list) != append.OUTPUT.read_bytes():
        raise ValueError("representative append admission is stale")
    if hashlib.sha256(atomic).hexdigest() != ATOMIC_SHA256:
        raise ValueError("unreviewed representative capacity policy")
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.ZigAir.MemoryTypes\n\nnamespace Compiler.Extraction.RepresentativeArray.Capacity\n\n"
        "-- Captured aarch64 target and 32-byte nonzero Expression, checked by native admission.\n"
        "-- Complete ensureTotalCapacity/growCapacity and cache-line policy bodies are bound.\n"
        "-- std/array_list.zig SHA-256: " + append.graph.STD["array_list.zig"] + "\n"
        "-- std/atomic.zig SHA-256: " + ATOMIC_SHA256 + "\n"
        "def initialCapacity : Nat := max 1 (128 / 32)\n"
        "def grow (minimum : Nat) : Nat :=\n"
        "  min (Compiler.ZigAir.Memory.addressLimit - 1) (minimum + (minimum / 2 + initialCapacity))\n\n"
        "end Compiler.Extraction.RepresentativeArray.Capacity\n").encode()


def check(lib):
    lib = Path(lib)
    data = extract(storage.SOURCE.read_bytes(), (lib / "std/array_list.zig").read_bytes(), (lib / "std/atomic.zig").read_bytes())
    if data != OUTPUT.read_bytes():
        raise ValueError("representative capacity admission is stale")
    return {"programSha256": hashlib.sha256(data).hexdigest(), "atomicSha256": ATOMIC_SHA256,
        "scope": "captured aarch64 capacity selection", "nativeGrowingAppendVerified": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--zig-lib-dir", type=Path, required=True)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    if args.check:
        check(args.zig_lib_dir)
    else:
        OUTPUT.write_bytes(extract(storage.SOURCE.read_bytes(), (args.zig_lib_dir / "std/array_list.zig").read_bytes(),
            (args.zig_lib_dir / "std/atomic.zig").read_bytes()))
