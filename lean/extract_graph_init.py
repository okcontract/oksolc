#!/usr/bin/env python3
"""Admit graph initialization and its complete owning instance-field profile.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0

This establishes the empty state only. Native growth, item/container storage,
publication, teardown and recursive preservation remain compiler obligations.
"""
import argparse
import hashlib
from pathlib import Path

import extract_storage as storage

ROOT = storage.SOURCE.parents[2]
OUTPUT = ROOT / "lean/Compiler/Extraction/GraphInitProgram.lean"
FIELDS = """allocator: std.mem.Allocator,
    representatives: std.ArrayList(Expression) = .empty,
    expressions: ExpressionMap = .empty,""" + storage.CAPACITY_FIELD
# Reviewed Zig 0.17 sources at 7647adab80dd088f4de3610fd245915a912eb6ad.
# std.ArrayList aliases Aligned(T, null); both empty containers allocate nothing.
# Both empty containers initialize their captured debug pointer-stability locks.
STD = {
    "meta.zig": "af1d7b90ee1a3f019aae7c6b94b7db3845402af86434f6f2847bafcbfe2cd76a",
    "std.zig": "053cdeca0cb3632a98117ddbef4ffa1a65cf30bcc6555af9437dc3ee3781d12e",
    "array_list.zig": "0420c0177c67490083f1055cff6de253f9ee8fb28755c5200002627640ff7aee",
    "hash_map.zig": "da14a2401ab5c12d6ca25bbf49e950596859ffc9e4b6d7726ade7ea8fd4a1b34",
    "debug.zig": "98e84c2194011077e8b8156cb3b2cb7b310a08dd34f396ee3654c102796e8f59",
}


def extract(data):
    storage.extract(data)  # Bind the existing representative/query admission too.
    storage.function(data, "const std =").expect('@import("std");')
    storage.function(data, "const ExpressionMap =").expect(
        "std.HashMapUnmanaged(ExpressionKey, Id, ExpressionKeyContext, 80);")
    for name, signature, body in (
        ("init", "pub fn init(allocator: std.mem.Allocator) ExpressionClasses", "return .{ .allocator = allocator };"),
        ("size", "pub fn size(self: *const ExpressionClasses) usize", "return self.representatives.items.len;"),
    ):
        parsed = storage.struct_member(data, "pub const ExpressionClasses =", FIELDS, name, signature)
        parsed.expect(body)
        if parsed.pos != len(parsed.items):
            raise storage.Unsupported("extra graph initialization/query behavior")
    hashes = "\n".join("-- std/" + name + " SHA-256: " + value for name, value in sorted(STD.items()))
    return ("/-\n// Copyright (C) 2026 OKcontract Pte. Ltd.\n// SPDX-License-Identifier: GPL-3.0\n-/\n"
        "import Compiler.Extraction.InternerGraphInitOwnership\n\n"
        "namespace Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit\n\n"
        "-- Generated from the complete graph initializer and owner fields.\n"
        "-- Source SHA-256: " + hashlib.sha256(data).hexdigest() + "\n" + hashes + "\n"
        "def zigInit (allocator : Nat) (before : Session σ) : Nat × World σ := run allocator before\n\n"
        "-- Complete container defaults in a declared owner; native owner allocation and allocator contents remain open.\n"
        "def zigInitInOwner (runtimeSafety : Bool) (allocator : Nat) (before : Session σ)\n"
        "    (owner sentinel : Compiler.ZigAir.Memory.Address) : Except Compiler.ZigAir.Memory.Fault (Nat × World σ) :=\n"
        "  OwnerMemory.run runtimeSafety allocator before owner sentinel\n\n"
        "-- Pinned null-metadata keyIterator/FieldIterator.next branch establishes empty key ownership.\n"
        "def zigInitOwned (runtimeSafety : Bool) (allocator : Nat) (before : Session σ)\n"
        "    (owner sentinel : Compiler.ZigAir.Memory.Address) :=\n"
        "  Ownership.run runtimeSafety allocator before owner sentinel\n\n"
        "-- Pinned std get/getContext/getAdapted/getIndex empty branch; nonempty probing rejects.\n"
        "def zigEmptyCacheGet (runtimeSafety : Bool) (state : Compiler.ZigAir.Memory.State)\n"
        "    (owner : Compiler.ZigAir.Memory.Address) (key : Compiler.Extraction.Cache.Key) :=\n"
        "  Compiler.Extraction.ExpressionMap.getEmpty runtimeSafety state owner key\n\n"
        "end Compiler.Extraction.Memory.Arguments.Normalization.OwnedCall.GraphInit\n").encode()


def check_std(lib):
    for name, expected in STD.items():
        if hashlib.sha256((Path(lib) / "std" / name).read_bytes()).hexdigest() != expected:
            raise ValueError("unreviewed Zig graph container default: " + name)
    return STD.copy()


def check():
    data = storage.SOURCE.read_bytes()
    if storage.extract(data) != storage.OUTPUT.read_bytes():
        raise ValueError("graph representative/query source admission is stale")
    if extract(data) != OUTPUT.read_bytes():
        raise ValueError("graph initialization source admission is stale")
    return {"sourceSha256": hashlib.sha256(data).hexdigest(),
        "programSha256": hashlib.sha256(OUTPUT.read_bytes()).hexdigest(),
        "pinnedStd": STD.copy(), "nativeGraphMutationCorrespondenceVerified": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    if parser.parse_args().check:
        check()
    else:
        OUTPUT.write_bytes(extract(storage.SOURCE.read_bytes()))
