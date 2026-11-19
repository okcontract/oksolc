#!/usr/bin/env python3
"""Mutation controls for complete-owner modular literal admission.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import extract_rule_ternary as admission
from extract_compiler import Unsupported
from check_rule_ternary import literal_inventory


def air_fixture():
    word = {"kind": "int", "bits": 32, "signedness": "unsigned"}
    source_type = {"kind": "pointer", "flags": {"size": "slice", "isConst": True}, "child": word}
    array_type = {"kind": "pointer", "child": {"kind": "array", "length": 3, "child": word,
        "sentinel": None, "layout": {"kind": "abi", "bytes": 12, "alignment": 4}}}
    instructions = []
    for start in (0, 20):
        ref = lambda index: {"kind": "instruction", "index": start + index}
        const = lambda value: {"kind": "constant", "value": value}
        instructions.extend([
            {"index": start, "tag": "load", "type": source_type, "operand": {"kind": "instruction", "index": 500 + start}},
            {"index": start + 1, "tag": "slice_elem_ptr", "lhs": ref(0), "rhs": const(0)},
            {"index": start + 2, "tag": "load", "type": word, "operand": ref(1)},
            {"index": start + 3, "tag": "load", "type": source_type, "operand": {"kind": "instruction", "index": 500 + start}},
            {"index": start + 4, "tag": "slice_elem_ptr", "lhs": ref(3), "rhs": const(1)},
            {"index": start + 5, "tag": "load", "type": word, "operand": ref(4)},
            {"index": start + 6, "tag": "alloc", "allocationKind": "stack", "type": array_type},
            {"index": start + 7, "tag": "ptr_elem_ptr", "lhs": ref(6), "rhs": const(0)},
            {"index": start + 8, "tag": "store", "lhs": ref(7), "rhs": ref(2)},
            {"index": start + 9, "tag": "ptr_elem_ptr", "lhs": ref(6), "rhs": const(1)},
            {"index": start + 10, "tag": "store", "lhs": ref(9), "rhs": ref(5)},
            {"index": start + 11, "tag": "ptr_elem_ptr", "lhs": ref(6), "rhs": const(2)},
            {"index": start + 12, "tag": "store", "lhs": ref(11), "rhs": ref(600)},
        ])
    return {"instructions": instructions}


class RuleTernaryTests(unittest.TestCase):
    def test_complete_owner_and_both_literal_segments_are_bound(self):
        self.assertEqual(admission.extract(*admission.owner.inputs()), admission.OUTPUT.read_bytes())
        report = admission.check()
        self.assertEqual(report["liveLiteralSites"], 2)
        self.assertFalse(report["completeModularRuleVerified"])
        self.assertFalse(report["nativeQueryCorrespondenceVerified"])
        self.assertFalse(report["completeRecursiveConstructorsVerified"])

    def test_guards_operands_and_opcode_mutations_reject(self):
        source, *rest = admission.owner.inputs()
        for before, after in (
            (b"options.for_yul_optimizer and right_constant", b"true and right_constant"),
            (b"binaryLogarithm(right_constant.?) != null", b"binaryLogarithm(right_constant.?) == null"),
            (b".MULMOD,\n                            &.{ nested[0], nested[1], right }", b".ADDMOD,\n                            &.{ nested[0], nested[1], right }"),
            (b".ADDMOD,\n                            &.{ nested[0], nested[1], right }", b".MULMOD,\n                            &.{ nested[0], nested[1], right }"),
            (b"&.{ nested[0], nested[1], right }", b"&.{ nested[1], nested[0], right }"),
            (b"&.{ nested[0], nested[1], right }", b"&.{ nested[0], nested[1], left }"),
            (b"&.{ nested[0], nested[1], right }", b"&.{ nested[0], nested[1] }"),
            (b"if (classes.operationArguments(left, .MUL)) |nested|\n                    if (nested.len == 2)",
             b"if (classes.operationArguments(left, .MUL)) |nested|\n                    if (nested.len >= 2)"),
            (b"if (classes.operationArguments(left, .ADD)) |nested|\n                    if (nested.len == 2)",
             b"if (classes.operationArguments(left, .ADD)) |nested|\n                    if (nested.len >= 2)"),
        ):
            with self.subTest(mutation=after), self.assertRaises(Unsupported):
                self.assertIn(before, source)
                admission.extract(source.replace(before, after, 1), *rest)

    def test_comment_decoys_do_not_admit_changed_literals(self):
        source, *rest = admission.owner.inputs()
        decoy = b"// &.{ nested[0], nested[1], right }\n"
        with self.assertRaises(Unsupported):
            admission.extract(decoy + source.replace(b"&.{ nested[0], nested[1], right }", b"&.{ nested[1], nested[1], right }", 1), *rest)
        self.assertNotEqual(admission.extract(decoy + source, *rest), admission.OUTPUT.read_bytes())

    def test_readonly_load_order_and_array_metadata(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "air.json"
            fixture = air_fixture()
            path.write_text(json.dumps(fixture))
            checked = literal_inventory(path)
            self.assertEqual([array["initializerReadInstructions"] for array in checked["arrays"]], [[2, 5], [22, 25]])
            self.assertFalse(checked["airControlSemanticsVerified"])
            for index, field, value in (
                    (6, "allocationKind", "heap"), (6, "type.child.sentinel", 0), (6, "type.child.length", 2),
                    (6, "type.child.layout.bytes", 8), (6, "type.child.layout.alignment", 8),
                    (0, "type.flags.isConst", False), (3, "operand.index", 900), (4, "rhs.value", 0),
                    (5, "operand.index", 1), (8, "rhs.index", 5), (10, "rhs.index", 2), (11, "rhs.value", 1),
                    (2, "index", 30)):
                with self.subTest(index=index, field=field), self.assertRaises(ValueError):
                    changed = copy.deepcopy(fixture)
                    target = changed["instructions"][index]
                    parts = field.split(".")
                    for part in parts[:-1]:
                        target = target[part]
                    target[parts[-1]] = value
                    path.write_text(json.dumps(changed))
                    literal_inventory(path)


if __name__ == "__main__":
    unittest.main()
