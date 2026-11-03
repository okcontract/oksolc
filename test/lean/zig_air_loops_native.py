#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Defined native loop cases, isolated from the capture/verification harness.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import argparse
import ctypes as c
import json
from pathlib import Path


def check(args):
    library = c.CDLL(str(args.library))
    fill, copy, nested = library.fill, library.copy_forward, library.nested_continue
    fill.argtypes = [c.c_void_p, c.c_size_t, c.c_uint32]
    copy.argtypes = [c.c_void_p, c.c_void_p, c.c_size_t]
    nested.argtypes = [c.c_void_p, c.c_size_t, c.c_size_t, c.c_size_t, c.c_uint32]
    fill.restype = copy.restype = nested.restype = None
    cases = []

    def observe(name, expected, actual):
        cases.append({"case": name, "expected": expected, "actual": list(actual)})
        # Retain observations even if a later case crashes or a comparison fails.
        args.output.write_text(json.dumps({"schema": "oksolc.native-loop-cases.v1", "cases": cases}, indent=2) + "\n")

    for length, expected in ((0, [1, 2, 3, 4, 5]), (1, [9, 2, 3, 4, 5]), (5, [9] * 5)):
        words = (c.c_uint32 * 5)(1, 2, 3, 4, 5)
        fill(words, length, 9)
        observe("fill-" + str(length), expected, words)
    for name, dst, src, length, expected in (
        ("zero", 1, 0, 0, [1, 2, 3, 4, 5]),
        ("same", 0, 0, 5, [1, 2, 3, 4, 5]),
        ("forward-overlap", 1, 0, 4, [1, 1, 1, 1, 1]),
        ("backward-overlap", 0, 1, 4, [2, 3, 4, 5, 5])):
        words = (c.c_uint32 * 5)(1, 2, 3, 4, 5)
        address = c.addressof(words)
        copy(address + 4 * dst, address + 4 * src, length)
        observe("copy-" + name, expected, words)
    for name, rows, columns, stop, expected in (
        ("no-rows", 0, 3, 1, [1] * 6), ("no-columns", 2, 0, 1, [1] * 6),
        ("immediate", 2, 3, 0, [1] * 6), ("continue", 2, 3, 1, [9, 1, 1, 9, 1, 1]),
        ("full", 2, 3, 3, [9] * 6)):
        words = (c.c_uint32 * 6)(*([1] * 6))
        nested(words, rows, columns, stop, 9)
        observe("nested-" + name, expected, words)
    if any(case["expected"] != case["actual"] for case in cases):
        raise ValueError("native loop observation mismatch")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
