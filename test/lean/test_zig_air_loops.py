#!/usr/bin/env python3
# SPDX-License-Identifier: GPL-3.0
"""Malformed capture controls for lexical loop-target inspection.
// Copyright (C) 2026 OKcontract Pte. Ltd.
"""

import copy
import unittest

from check_zig_air_loops import inspect_loops
from check_zig_air_memory import inspect_memory, layout, pointer, uint


def instruction(index, tag, **payload):
    return {"index": index, "tag": tag, "payloadVisited": True,
            "type": {"kind": "noreturn"}, **payload}


RECORD = {"body": [0, 3], "instructions": [
    instruction(0, "block", body=[1], type={"kind": "void"}),
    instruction(1, "loop", body=[2]), instruction(2, "repeat", target=1),
    instruction(3, "ret", operand={"kind": "unit"})]}


class LoopCaptureTests(unittest.TestCase):
    def test_loop_target_and_ownership(self):
        result = inspect_loops(RECORD)
        self.assertEqual(result["loops"], {1: {"bodyInstructions": 1, "backedges": 1}})
        self.assertEqual(result["repeats"], [{"instruction": 2, "target": 1}])
        self.assertEqual(result["bodyInstructions"], 4)

    def test_invalid_repeat_target(self):
        for target in (0, 2, 3, -1, 99, True):
            with self.subTest(target=target), self.assertRaises(ValueError):
                record = copy.deepcopy(RECORD)
                record["instructions"][2]["target"] = target
                inspect_loops(record)

    def test_missing_or_wrong_loop_payload(self):
        for index, key, value in ((1, "type", {"kind": "void"}), (1, "body", []),
                                  (1, "body", [2, 2]), (1, "body", [3]),
                                  (1, "payloadVisited", False), (2, "unsupportedPayload", True),
                                  (2, "type", {"kind": "void"})):
            with self.subTest(index=index, key=key, value=value), self.assertRaises(ValueError):
                record = copy.deepcopy(RECORD)
                record["instructions"][index][key] = value
                inspect_loops(record)

    def test_code_after_terminator(self):
        record = copy.deepcopy(RECORD)
        record["body"] = [3, 0]
        with self.assertRaisesRegex(ValueError, "after a terminator"):
            inspect_loops(record)

    def test_nested_loop_can_repeat_outer(self):
        record = copy.deepcopy(RECORD)
        record["instructions"][1]["body"] = [4]
        record["instructions"].extend([
            instruction(4, "loop", body=[5]),
            instruction(5, "cond_br", condition={"kind": "unit"}, thenBody=[2], elseBody=[6]),
            instruction(6, "repeat", target=4)])
        result = inspect_loops(record)
        self.assertEqual({loop: data["backedges"] for loop, data in result["loops"].items()}, {1: 1, 4: 1})

    def test_index_pointer_retains_type_and_constness(self):
        for const in (False, True):
            many = pointer(uint(32), layout(4, 4), size="many", const=const)
            one = pointer(uint(32), layout(4, 4), const=const)
            record = {"configuration": {"pointerBits": 64}, "body": [0, 1, 2, 3], "instructions": [
                instruction(0, "arg", type=many), instruction(1, "arg", type=uint(64)),
                instruction(2, "ptr_elem_ptr", type=one, lhs={"kind": "instruction", "index": 0},
                            rhs={"kind": "instruction", "index": 1}),
                instruction(3, "ret", operand={"kind": "unit"})]}
            self.assertEqual(inspect_memory(record), {"ptr_elem_ptr": 1})
            for result in (many, pointer(uint(8), layout(1, 1)),
                           pointer(uint(32), layout(4, 4), const=not const)):
                with self.subTest(const=const, result=result), self.assertRaises(ValueError):
                    changed = copy.deepcopy(record)
                    changed["instructions"][2]["type"] = result
                    inspect_memory(changed)
            changed = copy.deepcopy(record)
            changed["instructions"][2]["rhs"]["index"] = 3
            with self.assertRaisesRegex(ValueError, "does not dominate"):
                inspect_memory(changed)


if __name__ == "__main__":
    unittest.main()
