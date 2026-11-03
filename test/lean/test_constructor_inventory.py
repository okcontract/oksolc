#!/usr/bin/env python3
"""Negative controls for the recursive constructor premise inventory.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
from pathlib import Path
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import constructor_inventory as inventory
from extract_compiler import Unsupported


class ConstructorInventoryTests(unittest.TestCase):
    def test_reviewed_inventory(self):
        expected = json.loads(inventory.OUTPUT.read_bytes())
        self.assertEqual(inventory.inventory(), expected)
        sources = expected["sources"]
        self.assertEqual([len(source["sites"]) for source in sources], [9, 104, 4])
        self.assertEqual(sum(site["storage"] == "borrowed" for source in sources for site in source["sites"]), 9)
        self.assertFalse(inventory.check()["constructorGoalEstablished"])

    def test_each_span_is_bound_to_exact_bytes(self):
        for source in inventory.inventory()["sources"]:
            data = (inventory.ROOT / source["path"]).read_bytes()
            for site in source["sites"]:
                with self.subTest(path=source["path"], line=site["line"]):
                    self.assertEqual(inventory.hashlib.sha256(data[site["startByte"]:site["endByte"]]).hexdigest(), site["sha256"])

    def test_omitted_site_and_forged_storage_are_detected(self):
        for mutation in ("omit", "storage", "child", "scope"):
            document = copy.deepcopy(inventory.inventory())
            site = document["sources"][0]["sites"][4]
            if mutation == "omit":
                document["sources"][0]["sites"].pop()
            elif mutation == "storage":
                site["storage"] = "borrowed"
            elif mutation == "child":
                site["children"] = []
            else:
                document["scope"] = "all compiler paths"
            actual = inventory.inventory()
            with self.subTest(mutation=mutation), patch.object(Path, "read_bytes", return_value=json.dumps(document).encode()), patch.object(inventory, "inventory", return_value=actual):
                with self.assertRaisesRegex(ValueError, "stale"):
                    inventory.check()

    def test_nested_calls_and_comment_decoys(self):
        data = b'''pub fn apply(classes: anytype) !u32 {
            // classes.makeConstant(7, debug_data)
            return try classes.makeOperation(.SUB, &.{ try classes.makeConstant(0, debug_data), right }, debug_data);
        }
        test "excluded" { _ = classes.makeConstant(123, debug_data); }
        '''
        sites = inventory.sites(data)
        self.assertEqual([site["callee"] for site in sites], ["makeOperation", "makeConstant"])
        self.assertEqual(sites[0]["children"], [1])
        self.assertEqual((sites[0]["storage"], sites[0]["arity"]), ("temporary", 2))

    def test_unclassified_storage_and_indirect_calls_reject(self):
        for body in ("classes.makeOperation(.ADD, invented, debug_data)", "classes.makeConstant"):
            with self.subTest(body=body), self.assertRaises(Unsupported):
                inventory.sites(("fn apply(classes: anytype) !u32 { return " + body + "; }").encode())

    def test_production_root_cannot_be_satisfied_by_a_test_helper(self):
        with self.assertRaisesRegex(Unsupported, "root disappeared"):
            inventory.sites(b'test "fake" { fn makeOperation() void {} }', {"makeOperation"})


if __name__ == "__main__":
    unittest.main()
