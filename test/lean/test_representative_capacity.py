#!/usr/bin/env python3
"""Reject changes to the complete capacity wrapper and target policy.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import hashlib
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import extract_representative_capacity as admission
from extract_storage import Unsupported
from test_representative_append import fixture as append_fixture


def fixture():
    return append_fixture().replace(b"pub fn addOneAssumeCapacity", b"""
        pub fn growCapacity(minimum: usize) usize {
            if (@sizeOf(T) == 0) return math.maxInt(usize);
            const init_capacity: comptime_int = @max(1, std.atomic.cache_line / @sizeOf(T));
            return minimum +| (minimum / 2 + init_capacity);
        }
        pub fn addOneAssumeCapacity""")


# Independent literal source, including every branch of the dependency.
def atomic_fixture():
    return b'''pub fn cacheLineForCpu(cpu: std.Target.Cpu) u16 {
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
}
pub const cache_line: comptime_int = cacheLineForCpu(builtin.cpu);
'''


class RepresentativeCapacityAdmissionTests(unittest.TestCase):
    def test_complete_wrapper_and_policy(self):
        admission.admit(fixture(), atomic_fixture())

    def test_growth_arithmetic_and_nonzero_specialization(self):
        for before, after in (
                (b"@sizeOf(T) == 0", b"@sizeOf(T) != 0"),
                (b"return math.maxInt(usize)", b"return minimum"),
                (b"@max(1,", b"@min(1,"),
                (b"std.atomic.cache_line / @sizeOf(T)", b"std.atomic.cache_line / @alignOf(T)"),
                (b"minimum +|", b"minimum +"),
                (b"minimum +|", b"minimum +%"),
                (b"minimum / 2", b"minimum / 3"),
                (b"minimum / 2 + init_capacity", b"minimum / 2 - init_capacity"),
                (b"return minimum +| (minimum / 2 + init_capacity);", b"return minimum +| (minimum / 2 + init_capacity); unreachable;")):
            self.assertEqual(fixture().count(before), 1)
            with self.subTest(statement=before), self.assertRaises(Unsupported):
                admission.admit(fixture().replace(before, after), atomic_fixture())

    def test_wrapper_early_return_and_forwarding(self):
        for before, after in (
                (b"self.capacity >= new_capacity", b"self.capacity > new_capacity"),
                (b"growCapacity(new_capacity)", b"new_capacity"),
                (b"growCapacity(new_capacity)", b"growCapacity(self.items.len)"),
                (b"return self.ensureTotalCapacityPrecise", b"self.ensureTotalCapacityPrecise")):
            self.assertEqual(fixture().count(before), 1)
            with self.subTest(statement=before), self.assertRaises(Unsupported):
                admission.admit(fixture().replace(before, after), atomic_fixture())

    def test_target_policy_and_binding(self):
        for before, after in (
                (b"=> 128", b"=> 64"), (b".aarch64,", b""),
                (b"cpu.arch", b"builtin.cpu.arch"), (b".v73", b".v72"),
                (b"else => 64", b"else => 32"),
                (b"cacheLineForCpu(builtin.cpu)", b"cacheLineForCpu(.{})"),
                (b"cacheLineForCpu(builtin.cpu)", b"128"),
                (b"return switch", b"_ = cpu; return switch")):
            self.assertEqual(atomic_fixture().count(before), 1)
            with self.subTest(statement=before), self.assertRaises(Unsupported):
                admission.admit(fixture(), atomic_fixture().replace(before, after))

    def test_duplicate_or_missing_declarations(self):
        for array, atomic in ((fixture() + fixture(), atomic_fixture()),
                (append_fixture(), atomic_fixture()), (fixture(), atomic_fixture() + atomic_fixture()),
                (fixture(), atomic_fixture().replace(b"pub const cache_line:", b"pub const other:"))):
            with self.subTest(array=array[:40], atomic=atomic[:40]), self.assertRaises(Unsupported):
                admission.admit(array, atomic)

    def test_complete_atomic_identity_is_independently_bound(self):
        with patch.object(admission.append, "extract", return_value=admission.append.OUTPUT.read_bytes()), \
                patch.object(admission, "ATOMIC_SHA256", hashlib.sha256(atomic_fixture()).hexdigest()):
            generated = admission.extract(b"source", fixture(), atomic_fixture())
            self.assertIn(b"max 1 (128 / 32)", generated)
            with self.assertRaisesRegex(ValueError, "unreviewed representative capacity"):
                admission.extract(b"source", fixture(), atomic_fixture() + b"// changed identity\n")
        with patch.object(admission.append, "extract", return_value=b"stale"):
            with self.assertRaisesRegex(ValueError, "append admission is stale"):
                admission.extract(b"source", fixture(), atomic_fixture())


if __name__ == "__main__":
    unittest.main()
