#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Lexical control and indexed-pointer checks for resumable AIR decoding.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import copy
import unittest

from test_zig_air_generate import fixture, inst, ref, const, U8, VOID, NEVER
from test_zig_air_memory_generate import memory_fixture, MANY, USIZE
from check_zig_air_memory import pointer, layout
from generate_memory import Decoder, LoopDecoder


def loop_fixture():
    result = fixture()
    result["configuration"].update(arch="aarch64", os="macos", pointerBits=64, endianness="little")
    result["body"] = [0, 1, 8]
    result["instructions"] = [
        inst(0, "arg", U8, zirParameterIndex=0),
        inst(1, "block", U8, body=[2]),
        inst(2, "loop", NEVER, body=[3, 4]),
        inst(3, "cmp_lt", {"kind": "bool"}, lhs=ref(0), rhs=const(128)),
        inst(4, "cond_br", NEVER, condition=ref(3), thenBody=[5, 6], elseBody=[7]),
        inst(5, "add", U8, lhs=ref(0), rhs=const(1)),
        inst(6, "repeat", NEVER, target=2),
        inst(7, "br", NEVER, target=1, operand=ref(0)),
        inst(8, "ret", NEVER, operand=ref(1)),
    ]
    return result


def decode(record):
    return LoopDecoder(record).program(record)


class LoopGenerationTests(unittest.TestCase):
    def rejects(self, edit, message):
        record = loop_fixture()
        edit(record)
        with self.assertRaisesRegex(ValueError, message):
            decode(record)

    def test_explicit_loop_capability_and_control(self):
        record = loop_fixture()
        text = decode(record)
        self.assertIn("(.loop rfl 2", text)
        self.assertIn("(.repeat rfl 2)", text)
        self.assertIn("(.jump 1 (.local 0))", text)
        with self.assertRaisesRegex(ValueError, "unsupported AIR operation: loop"):
            Decoder(record).program(record)

    def test_repeat_requires_lexically_enclosing_loop(self):
        for target in (0, 1, 5, 6, 8, -1, 9, True):
            self.rejects(lambda r: r["instructions"][6].update(target=target), "enclosing loop|integer")
        self.rejects(lambda r: r["instructions"].__setitem__(7, inst(7, "br", NEVER, target=2, operand=ref(0))),
                     "destination")
        self.rejects(lambda r: r["instructions"].__setitem__(8, inst(8, "repeat", NEVER, target=2)), "enclosing loop")

    def test_loop_values_and_iteration_locals_do_not_escape(self):
        for index, field, value in ((3, "lhs", ref(5)), (5, "rhs", ref(5)),
                                    (7, "operand", ref(5)), (8, "operand", ref(3)), (8, "operand", ref(2))):
            self.rejects(lambda r: r["instructions"][index].update({field: value}), "dominated")

    def test_loop_ownership_termination_and_backedges(self):
        for body in ([], [3], [3, 4, 6], [3, 3, 4], [2]):
            self.rejects(lambda r: r["instructions"][2].update(body=body), "ownership|terminator|body")
        self.rejects(lambda r: r["instructions"][4].update(elseBody=[5, 6]), "ownership")
        self.rejects(lambda r: r["instructions"].__setitem__(6, inst(6, "br", NEVER, target=1, operand=ref(5))),
                     "no repeat")
        for index in (2, 6):
            self.rejects(lambda r: r["instructions"][index].update(type=VOID), "non-returning|enclosing loop")
            self.rejects(lambda r: r["instructions"][index].update(extra=True), "fields")

    def test_nested_continue_can_target_outer_loop(self):
        record = loop_fixture()
        record["instructions"][2]["body"] = [9]
        record["instructions"][4]["elseBody"] = [10]
        record["instructions"][9:] = [inst(9, "loop", NEVER, body=[3, 4]), inst(10, "repeat", NEVER, target=9)]
        # The old exit is outside the decoded closure, so it must be explicitly accounted for.
        record["instructions"][7] = dict(index=7, tag="br", payloadVisited=False,
                                          unsupportedPayload=True, reason="outside-decoded-body-closure")
        decoder = LoopDecoder(record)
        text = decoder.program(record)
        self.assertEqual(decoder.loop_ids, {2, 9})
        self.assertEqual(decoder.repeat_targets, {2, 9})
        self.assertIn("(.repeat rfl 9)", text)

    def test_unknown_operations_remain_explicit_rejections(self):
        for tag in ("call", "ret_load", "unreach", "future"):
            self.rejects(lambda r: r["instructions"][5].update(tag=tag), "unsupported AIR operation")

    def test_index_pointer_preserves_type_and_permissions(self):
        record = memory_fixture()
        record["sourceValidity"]["slices"] = []
        one = pointer(U8, layout(1, 1), const=True)
        record["instructions"][2] = inst(2, "ptr_elem_ptr", one, lhs=ref(0), rhs=ref(1))
        self.assertIn("(.elementPointer (.local 0) (.local 1))", decode(record))
        for key, value, message in (("type", MANY, "element type"),
                                     ("type", pointer(U8, layout(1, 1)), "permissions"),
                                     ("rhs", ref(2), "dominated"), ("rhs", ref(0), "offset type")):
            changed = copy.deepcopy(record)
            changed["instructions"][2][key] = value
            with self.assertRaisesRegex(ValueError, message):
                decode(changed)
        for child, size, stride in ((VOID, "many", 0), (U8, "one", 1)):
            changed = copy.deepcopy(record)
            source = pointer(child, layout(stride, 1), size=size, const=True)
            changed["signature"]["parameters"][0] = source
            changed["instructions"][0]["type"] = source
            with self.assertRaisesRegex(ValueError, "offset type"):
                decode(changed)


if __name__ == "__main__":
    unittest.main()
