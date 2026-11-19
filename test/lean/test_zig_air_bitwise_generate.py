#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Retain unsigned bit operations and reject incompatible types/layouts.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import copy
import unittest

from test_zig_air_generate import fixture, inst, ref, const, NEVER, decode
from check_zig_air_memory import pointer, layout, uint
from generate_memory import type_of


def bit_fixture(tag, width=256, count_width=8, count=1):
    record = fixture()
    value_type = uint(width)
    record["signature"].update(parameters=[value_type], returnType=value_type)
    record["body"] = [0, 1, 2]
    record["instructions"] = [inst(0, "arg", value_type, zirParameterIndex=0),
        inst(1, tag, value_type, lhs=ref(0), rhs=const(count, uint(count_width))),
        inst(2, "ret", NEVER, operand=ref(1))]
    return record


class BitwiseGenerationTests(unittest.TestCase):
    def test_and_retains_matching_widths(self):
        for width in (0, 1, 8, 64, 256, 512):
            self.assertIn("(.bitAnd (.local 0)", decode(bit_fixture("bit_and", width, width, 0)))
        with self.assertRaisesRegex(ValueError, "operand width"):
            decode(bit_fixture("bit_and"))

    def test_xor_retains_unsigned_width_and_unused_operations(self):
        for width in (0, 1, 8, 64, 128, 256, 512):
            record = bit_fixture("xor", width, width, 0)
            self.assertIn("(.bitXor (.local 0)", decode(record))
            record["instructions"][2]["operand"] = const(0, uint(width))
            self.assertIn("(.bitXor (.local 0)", decode(record))
        with self.assertRaisesRegex(ValueError, "operand width"):
            decode(bit_fixture("xor", 64, 32))

    def test_shift_retains_narrow_count_and_dead_operation(self):
        for width in (1, 3, 8, 64, 256, 512):
            record = bit_fixture("shr", width, (width - 1).bit_length(), 0)
            self.assertIn("(.shiftRight (.local 0)", decode(record))
            record["instructions"][2]["operand"] = const(0, uint(width))
            self.assertIn("(.shiftRight (.local 0)", decode(record))
        # Valid count type can contain an out-of-range shift for u3. Keep it
        # executable so the semantics reports illegal behavior, even if dead.
        self.assertIn("(.int false 2 (3))", decode(bit_fixture("shr", 3, 2, 3)))

    def test_wrong_count_signed_vectors_and_other_shifts_reject(self):
        for width, count_width in ((0, 0), (256, 256), (8, 8), (1, 1)):
            with self.assertRaises(ValueError):
                decode(bit_fixture("shr", width, count_width, 0))
        for tag in ("shr", "bit_and", "xor"):
            for side in ("lhs", "rhs"):
                record = bit_fixture(tag, 256, 8 if tag == "shr" else 256)
                record["instructions"][1][side] = const(1, {"kind": "int", "bits": 256, "signedness": "signed"})
                with self.assertRaisesRegex(ValueError, "unsigned AIR bit operation"):
                    decode(record)
        for tag in ("shr_exact", "shl", "bit_or"):
            with self.assertRaisesRegex(ValueError, "unsupported AIR operation"):
                decode(bit_fixture(tag))
        record = bit_fixture("shr")
        record["instructions"][1]["rhs"]["type"] = {"kind": "vector"}
        with self.assertRaises(ValueError):
            decode(record)

    def test_bit_operations_keep_dominance_and_payload_checks(self):
        for tag in ("bit_and", "xor", "shr"):
            record = bit_fixture(tag, 256, 8 if tag == "shr" else 256)
            for key in ("lhs", "rhs"):
                changed = copy.deepcopy(record)
                changed["instructions"][1][key] = ref(1)
                with self.assertRaisesRegex(ValueError, "dominated"):
                    decode(changed)
                del changed["instructions"][1][key]
                with self.assertRaisesRegex(ValueError, "fields"):
                    decode(changed)

    def test_wide_layout_is_exact_and_unsigned_only(self):
        ty = pointer(uint(256), layout(32, 16))
        self.assertEqual(type_of(ty), ("ptr", True, False, ("int", False, 256)))
        for size, alignment in ((32, 32), (32, 8), (16, 16), (True, 16)):
            changed = copy.deepcopy(ty)
            changed["pointeeLayout"] = layout(size, alignment)
            with self.assertRaisesRegex(ValueError, "layout"):
                type_of(changed)
        for width, signed in ((128, False), (256, True), (512, False)):
            changed = copy.deepcopy(ty)
            changed["child"].update(bits=width, signedness="signed" if signed else "unsigned")
            with self.assertRaisesRegex(ValueError, "unsupported memory layout"):
                type_of(changed)


if __name__ == "__main__":
    unittest.main()
