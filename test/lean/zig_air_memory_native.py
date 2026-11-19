#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Execute defined memory fixture cases in an isolated native child process.
// Copyright (C) 2026 OKcontract Pte. Ltd.

Invalid/undefined Zig inputs are tested only by Lean, never executed here.
"""

import argparse
import ctypes as c
import json
from pathlib import Path


def check(args):
    slices, cells = c.CDLL(str(args.slices)), c.CDLL(str(args.cells))
    data = (c.c_uint8 * 16)()
    pointer = c.cast(data, c.c_void_p)
    results = []

    def observe(name, expected, actual):
        results.append({"case": name, "expected": expected, "actual": actual})

    def function(library, name, parameters, result=c.c_size_t):
        fn = getattr(library, name)
        fn.argtypes, fn.restype = parameters, result
        return fn

    bounded = function(slices, "bounded_slice", [c.c_void_p, c.c_size_t, c.c_size_t, c.c_size_t])
    observe("bounded-slice", 3, bounded(pointer, 8, 2, 5))
    conditional = function(slices, "conditional_slice", [c.c_void_p, c.c_size_t, c.c_size_t, c.c_bool])
    observe("untaken-slice", 0, conditional(pointer, 2, 4, False))
    observe("taken-valid-slice", 5, conditional(pointer, 8, 5, True))
    array = function(slices, "array_slice", [c.c_void_p, c.c_size_t, c.c_size_t])
    observe("array-slice", 3, array(pointer, 2, 5))
    fixed = function(slices, "constant_length", [c.c_void_p, c.c_size_t])
    observe("constant-length", 4, fixed(pointer, 4))
    unbounded = function(slices, "unbounded_constant_length", [c.c_void_p])
    observe("unbounded-constant-length", 4, unbounded(pointer))
    unused = function(slices, "unused_slice", [c.c_void_p, c.c_size_t, c.c_size_t])
    observe("unused-valid-slice", 1, unused(pointer, 2, 1))
    cell = c.c_uint32(1)
    stored = function(cells, "load_store", [c.POINTER(c.c_uint32), c.c_uint32], c.c_uint32)
    returned = stored(c.byref(cell), 7)
    observe("store-load", [7, 7], [returned, cell.value])

    class Slice(c.Structure):
        _fields_ = [("ptr", c.c_void_p), ("length", c.c_size_t)]

    view = Slice(pointer.value, 2)
    field = function(cells, "slice_fields", [c.POINTER(Slice), c.c_size_t], c.c_void_p)
    returned = field(c.byref(view), 4)
    observe("slice-field-alias", [0, 4], [returned - pointer.value, view.length])
    words = (c.c_uint32 * 4)()
    origin = c.addressof(words)
    back = function(cells, "move_back", [c.c_void_p, c.c_size_t], c.c_void_p)
    observe("pointer-subtraction", 4, back(origin + 8, 1) - origin)
    alias = function(cells, "buffer_alias", [c.c_void_p, c.c_size_t, c.c_uint32, c.c_uint32], c.c_uint32)
    observe("buffer-alias", [7, 7], [alias(origin, 0, 3, 7), words[0]])
    observe("buffer-separation", [3, 7], [alias(origin, 1, 3, 7), words[1]])
    initialize = function(cells, "initialize_slice", [c.POINTER(Slice), c.c_void_p, c.c_size_t], None)
    view = Slice(pointer.value, 2)
    initialize(c.byref(view), pointer, 4)
    observe("slice-initialization", [0, 4], [view.ptr - pointer.value, view.length])
    length = function(cells, "initialize_length", [c.POINTER(Slice), c.c_size_t])
    view = Slice(pointer.value, 2)
    observe("length-field-only", [4, 0, 4], [length(c.byref(view), 4), view.ptr - pointer.value, view.length])
    args.output.write_text(json.dumps({"schema": "oksolc.native-memory-cases.v1", "cases": results}, indent=2) + "\n")
    if any(case["expected"] != case["actual"] for case in results):
        raise ValueError("native memory observation mismatch")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--slices", type=Path, required=True)
    parser.add_argument("--cells", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    check(parser.parse_args())
