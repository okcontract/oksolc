#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Finite native pointer/heap observations for the captured slice-element root.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import argparse
import ctypes
import json
from pathlib import Path

CASES = [(0, 1, 0), (0, 8, 0), (0, 8, 7), (1, 2, 0), (1, 2, 1), (3, 4, 2), (6, 2, 1), (7, 1, 0)]
WORDS = [0, 4294967295, 305419896, 3735928559, 2147483648, 1, 3131961357, 2147483647]


def check(library, output):
    fn = ctypes.CDLL(str(library)).slice_element
    fn.argtypes = [ctypes.POINTER(ctypes.c_uint32), ctypes.c_size_t, ctypes.c_size_t]
    fn.restype = ctypes.c_void_p
    records = []
    for first, length, index in CASES:
        values = (ctypes.c_uint32 * len(WORDS))(*WORDS)
        pointer = ctypes.cast(ctypes.byref(values, first * 4), ctypes.POINTER(ctypes.c_uint32))
        result = fn(pointer, length, index)
        records.append({"first": first, "length": length, "index": index,
                        "before": WORDS, "after": list(values), "offset": result - ctypes.addressof(values)})
    passed = all(r["after"] == WORDS and r["offset"] == (r["first"] + r["index"]) * 4 for r in records)
    output.write_text(json.dumps({"status": "passed" if passed else "failed", "cases": records}, indent=2) + "\n")
    if not passed:
        raise ValueError("native slice-element observations differ")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    check(args.library, args.output)
