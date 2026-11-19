#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Full-width native observations of the production modular exponentiation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import argparse
import ctypes as c
import json
from pathlib import Path

MODULUS = 2**256
CASES = [(0, 0), (0, 1), (1, MODULUS - 1), (2, 10), (2, 255), (2, 256),
         (MODULUS - 1, MODULUS - 1), (MODULUS - 1, MODULUS - 2),
         (2**255, 1), (2**255, 2), (2**128 + 1, 2), (2**192 + 3, 257),
         (3, 2**255), (7, MODULUS - 1)]


def check(args):
    library = c.CDLL(str(args.library))
    power = library.power256
    power.argtypes = [c.POINTER(c.c_uint64)] + [c.c_uint64] * 8
    power.restype = None
    cases = []
    for base, exponent in CASES:
        output = (c.c_uint64 * 4)()
        limbs = [(value >> (64 * index)) & (2**64 - 1) for value in (base, exponent) for index in range(4)]
        power(output, *limbs)
        actual = sum(int(limb) << (64 * index) for index, limb in enumerate(output))
        cases.append({"base": str(base), "exponent": str(exponent),
                      "expected": str(pow(base, exponent, MODULUS)), "actual": str(actual)})
        args.output.write_text(json.dumps({"schema": "oksolc.native-exp-cases.v1", "cases": cases}, indent=2) + "\n")
    if any(case["expected"] != case["actual"] for case in cases):
        raise ValueError("native exponentiation mismatch")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
