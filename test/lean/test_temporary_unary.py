#!/usr/bin/env python3
"""Fail-closed controls for every unary algebraic source initializer.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import extract_temporary_unary as admission
from extract_compiler import Unsupported
from constructor_array_checks import array_inventory


class TemporaryUnaryTests(unittest.TestCase):
    def test_current_owner_and_all_sites_are_bound(self):
        self.assertEqual(admission.extract(admission.SOURCE.read_bytes()), admission.OUTPUT.read_bytes())
        report = admission.check()
        self.assertEqual(report["admittedBranches"], ["not_right", "iszero_left", "iszero_right", "bool_left", "bool_right"])
        self.assertEqual(report["temporarySites"], 4)
        self.assertFalse(report["completeRecursiveConstructorsVerified"])

    def test_selection_contents_order_and_error_boundaries_reject(self):
        source = admission.SOURCE.read_text()
        for before, after in (
            (".NOT, &.{right}", ".NOT, &.{left}"),
            (".NOT, &.{right}", ".ISZERO, &.{right}"),
            ("if (replacement == .iszero_left) left else right", "if (replacement == .iszero_left) right else left"),
            ("if (replacement == .bool_left) left else right", "if (replacement == .bool_right) left else right"),
            ("const first = try classes.makeOperation", "const first = classes.makeOperation"),
            ("break :blk try classes.makeOperation", "break :blk classes.makeOperation"),
            ("&.{first}", "&.{right}"),
            ("&.{first}", "&.{first + 1}"),
            (".bool_left, .bool_right => blk:", ".bool_left => blk:"),
            ("            try classes.makeConstant(0, debug_data),", "            try classes.makeConstant(1, debug_data),"),
            ("left: u32", "left: u64"),
        ):
            with self.subTest(mutation=after), self.assertRaises(Unsupported):
                self.assertEqual(source.count(before), 1)
                admission.extract(source.replace(before, after).encode())

    def test_comments_cannot_admit_a_changed_owner(self):
        source = admission.SOURCE.read_bytes()
        decoy = b"// " + admission.FAMILIES[("bool_left", "bool_right")].replace("\n", " ").encode() + b"\n"
        with self.assertRaises(Unsupported):
            admission.extract(decoy + source.replace(b"&.{first}", b"&.{left}"))
        self.assertNotEqual(admission.extract(decoy + source), admission.OUTPUT.read_bytes())

    def test_array_inventory_rejects_missing_geometry_and_store_paths(self):
        def array(index, extent):
            return {"index": index, "tag": "alloc", "allocationKind": "stack", "type": {"child": {
                "kind": "array", "length": extent, "sentinel": None,
                "child": {"kind": "int", "bits": 32, "signedness": "unsigned"},
                "layout": {"kind": "abi", "bytes": extent * 4, "alignment": 4}}}}

        record = {"instructions": [array(0, 1),
            {"index": 1, "tag": "ptr_elem_ptr", "lhs": {"kind": "instruction", "index": 0}, "rhs": {"value": 0}},
            {"index": 2, "tag": "store", "lhs": {"kind": "instruction", "index": 1}},
            {"index": 3, "tag": "call", "unsupportedPayload": True}]}
        mutations = []
        missing = deepcopy(record)
        missing["instructions"].pop(2)
        mutations.append(missing)
        missing_sentinel = deepcopy(record)
        del missing_sentinel["instructions"][0]["type"]["child"]["sentinel"]
        mutations.append(missing_sentinel)
        for field, value in (("allocationKind", "heap"), ("sentinel", 0), ("alignment", 1), ("bytes", 8), ("offset", 1)):
            changed = deepcopy(record)
            if field == "allocationKind":
                changed["instructions"][0][field] = value
            elif field == "sentinel":
                changed["instructions"][0]["type"]["child"][field] = value
            elif field == "offset":
                changed["instructions"][1]["rhs"]["value"] = value
            else:
                changed["instructions"][0]["type"]["child"]["layout"][field] = value
            mutations.append(changed)
        duplicate = deepcopy(record)
        duplicate["instructions"].append(deepcopy(duplicate["instructions"][2]))
        mutations.append(duplicate)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "air.json"
            path.write_text(json.dumps(record))
            result = array_inventory(path, 1, 1)
            self.assertEqual(len(result["arrays"]), 1)
            self.assertEqual(result["unsupportedPayloadCount"], 1)
            self.assertFalse(result["airControlSemanticsVerified"])
            with self.assertRaises(ValueError):
                array_inventory(path, 1, 2)
            for changed in mutations:
                path.write_text(json.dumps(changed))
                with self.assertRaises(ValueError):
                    array_inventory(path, 1, 1)


if __name__ == "__main__":
    unittest.main()
