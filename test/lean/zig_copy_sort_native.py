#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Compare native copy/sort results, readonly source observations and sentinels.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import argparse
import ctypes as c
import json
from pathlib import Path
from zig_insertion_sort_native import CASES


def expected(values):
    return {"source": [0xDEADBEEF, *values, 0xBAADF00D], "target": [0xDEADBEEF, *sorted(values), 0xBAADF00D]}


def check(args):
    library = c.CDLL(str(args.library))
    copy_sort = library.copy_sort_ids
    copy_sort.argtypes, copy_sort.restype = [c.c_void_p, c.c_void_p, c.c_size_t], None
    observations = []

    def save():
        args.output.write_text(json.dumps({"schema": "oksolc.native-copy-sort-cases.v1", "cases": observations}, indent=2) + "\n")

    for name, values in CASES:
        wanted = expected(values)
        source = (c.c_uint32 * (len(values) + 2))(*wanted["source"])
        # Distinct initialized poison makes a missing copy observable without
        # relying on native reads of uninitialized storage. Lean covers that case.
        target = (c.c_uint32 * (len(values) + 2))(0xDEADBEEF, *([0xCCCCCCCC] * len(values)), 0xBAADF00D)
        copy_sort(c.addressof(source) + 4, c.addressof(target) + 4, len(values))
        actual = {"source": list(source), "target": list(target)}
        observations.append({"case": name, "input": values, "expected": wanted, "actual": actual})
        save()
        if actual != wanted:
            raise ValueError("native copy/sort source, result or sentinel mismatch: " + name)
    shared = (c.c_uint32 * 6)(3, 1, 2, 0xCCCCCCCC, 0xCCCCCCCC, 0xCCCCCCCC)
    copy_sort(c.addressof(shared), c.addressof(shared) + 12, 3)
    wanted = [3, 1, 2, 1, 2, 3]
    observations.append({"case": "same_allocation", "input": [3, 1, 2], "expected": wanted, "actual": list(shared)})
    save()
    if list(shared) != wanted:
        raise ValueError("native disjoint sub-slice copy/sort mismatch")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
