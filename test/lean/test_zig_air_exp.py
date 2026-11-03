#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Malformed shift captures must not masquerade as exponent halving.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import copy
import unittest

from check_zig_air_exp import inspect_shift
from check_zig_air_memory import uint

SHIFT = {"index": 1, "tag": "shr", "payloadVisited": True, "type": uint(256),
         "lhs": {"kind": "instruction", "index": 0},
         "rhs": {"kind": "constant", "type": uint(8), "value": 1}}
INSTRUCTIONS = [{"type": uint(256)}, SHIFT]


class ExponentShiftTests(unittest.TestCase):
    def test_retains_wide_value_and_narrow_count(self):
        self.assertEqual(inspect_shift(SHIFT, INSTRUCTIONS, {0}),
                         {"instruction": 1, "lhs": 0, "count": 1, "countBits": 8})

    def test_count_must_be_exact_typed_integer(self):
        for rhs in ({"kind": "constant", "type": uint(8), "value": 2},
                    {"kind": "constant", "type": uint(8), "value": True},
                    {"kind": "constant", "type": uint(256), "value": 1},
                    {"kind": "instruction", "index": 0}, None):
            with self.subTest(rhs=rhs), self.assertRaises(ValueError):
                changed = copy.deepcopy(SHIFT)
                changed["rhs"] = rhs
                inspect_shift(changed, INSTRUCTIONS, {0})

    def test_left_must_dominate_and_retain_full_width(self):
        for index in (True, -1, 1, 99):
            with self.subTest(index=index), self.assertRaises(ValueError):
                changed = copy.deepcopy(SHIFT)
                changed["lhs"]["index"] = index
                inspect_shift(changed, INSTRUCTIONS, {0})
        with self.assertRaises(ValueError):
            inspect_shift(SHIFT, [{"type": uint(64)}, SHIFT], {0})
        with self.assertRaises(ValueError):
            inspect_shift(SHIFT, INSTRUCTIONS, set())

    def test_kind_width_and_payload_presence_are_checked(self):
        for key, value in (("tag", "shr_exact"), ("tag", "shl"), ("type", uint(64)),
                           ("payloadVisited", False), ("unsupportedPayload", True)):
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                changed = copy.deepcopy(SHIFT)
                changed[key] = value
                inspect_shift(changed, INSTRUCTIONS, {0})
        for field in ("lhs", "rhs"):
            with self.subTest(field=field), self.assertRaises(ValueError):
                changed = copy.deepcopy(SHIFT)
                del changed[field]
                inspect_shift(changed, INSTRUCTIONS, {0})


if __name__ == "__main__":
    unittest.main()
