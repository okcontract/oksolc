#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Finite native/model sort comparisons with untouched surrounding storage.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import argparse
import ctypes as c
import json
from pathlib import Path

CASES = [("empty", []), ("singleton", [7]), ("ordered", [0, 1, 2, 3]),
         ("reversed", [3, 2, 1, 0]), ("duplicates", [2, 1, 2, 0, 1]),
         ("unsigned", [4294967295, 0, 2147483648, 1]), ("equal", [9, 9, 9]),
         ("alternating", [5, 1, 4, 2, 3, 0])]

EXCHANGES = [("swap_zero", 0, 0), ("swap_small", 1, 2), ("swap_max", 4294967295, 0),
             ("swap_equal_max", 4294967295, 4294967295), ("swap_high", 2147483648, 1),
             ("swap_zero_high", 0, 2147483648), ("swap_duplicate", 7, 7),
             ("swap_mixed", 2863311530, 1431655765)]


def check(args):
    library = c.CDLL(str(args.library))
    sort = library.sort_ids
    sort.argtypes, sort.restype = [c.c_void_p, c.c_size_t], None
    swap = library.swap_ids
    swap.argtypes, swap.restype = [c.c_void_p, c.c_size_t, c.c_size_t], None
    observations, exchanges = [], []

    def save():
        args.output.write_text(json.dumps({"schema": "oksolc.native-insertion-cases.v2",
            "cases": observations, "exchanges": exchanges}, indent=2) + "\n")

    for name, values in CASES:
        expected = [0xDEADBEEF, *sorted(values), 0xBAADF00D]
        # Even the empty slice points into live, suitably aligned storage.
        words = (c.c_uint32 * (len(values) + 2))(0xDEADBEEF, *values, 0xBAADF00D)
        sort(c.addressof(words) + c.sizeof(c.c_uint32), len(values))
        observations.append({"case": name, "input": values, "expected": expected, "actual": list(words)})
        save()
        if list(words) != expected:
            raise ValueError("native sort or surrounding storage mismatch: " + name)
    for name, a, b in EXCHANGES:
        expected = [0xDEADBEEF, b, a, 0xBAADF00D]
        words = (c.c_uint32 * 4)(0xDEADBEEF, a, b, 0xBAADF00D)
        swap(words, 2, 1)
        exchanges.append({"case": name, "input": [a, b], "left": 2, "right": 1,
                          "expected": expected, "actual": list(words)})
        save()
        if list(words) != expected:
            raise ValueError("native exchange or surrounding storage mismatch: " + name)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
