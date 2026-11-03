#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Observe defined u32 byte reads/writes and surrounding words.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""
import argparse
import ctypes as c
import json
from pathlib import Path

CASES = [(f"case_{i}_{index}", value, index, [0, 255, 18, 129][index])
         for i, value in enumerate([0, 4294967295, 3735928559, 2147483649]) for index in range(4)]


def expected(order, value, index, byte):
    before = list(value.to_bytes(4, order))
    after = before.copy()
    after[index] = byte
    return {"beforeBytes": before, "afterBytes": after,
            "afterWords": [0xDEADBEEF, int.from_bytes(bytes(after), order), 0xBAADF00D]}


def check(args):
    library = c.CDLL(str(args.library))
    order_fn = library.word_byte_order
    order_fn.argtypes, order_fn.restype = [], c.c_uint8
    read, write = library.read_word_byte, library.write_word_byte
    read.argtypes, read.restype = [c.c_void_p, c.c_size_t], c.c_uint8
    write.argtypes, write.restype = [c.c_void_p, c.c_size_t, c.c_uint8], None
    order_id = order_fn()
    report = {"schema": "oksolc.native-word-bytes.v1", "status": "failed", "byteOrderId": order_id, "cases": []}

    def save():
        args.output.write_text(json.dumps(report, indent=2) + "\n")

    save()
    if order_id not in (0, 1):
        raise ValueError("unknown native byte order")
    order = report["byteOrder"] = ["little", "big"][order_id]
    for name, value, index, byte in CASES:
        words = (c.c_uint32 * 3)(0xDEADBEEF, value, 0xBAADF00D)
        pointer = c.addressof(words) + c.sizeof(c.c_uint32)
        before = [read(pointer, i) for i in range(4)]
        write(pointer, index, byte)
        actual = {"beforeBytes": before, "afterBytes": [read(pointer, i) for i in range(4)], "afterWords": list(words)}
        wanted = expected(order, value, index, byte)
        report["cases"].append({"case": name, "value": value, "index": index, "byte": byte,
                                "expected": wanted, "actual": actual})
        save()
        if actual != wanted:
            raise ValueError("native byte-view mismatch: " + name)
    report["status"] = "passed"
    save()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--library", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
