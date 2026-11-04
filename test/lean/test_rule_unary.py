#!/usr/bin/env python3
"""Mutation controls for complete-owner unary literal admission.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import extract_rule_unary as admission
from extract_compiler import Unsupported


class RuleUnaryTests(unittest.TestCase):
    def test_three_live_sites_and_complete_owner_are_bound(self):
        self.assertEqual(admission.extract(*admission.inputs()), admission.OUTPUT.read_bytes())
        report = admission.check()
        self.assertEqual(report["liveLiteralSites"], 3)
        self.assertFalse(report["nativeQueryCorrespondenceVerified"])
        self.assertFalse(report["completeExponentRuleVerified"])
        self.assertFalse(report["completeRecursiveConstructorsVerified"])

    def test_source_load_selection_and_returned_id_mutations_reject(self):
        source, *rest = admission.inputs()
        text = source.decode()
        for before, after in (
            ("&.{third[0]}", "&.{third[1]}"),
            ("if (third.len == 1)", "if (third.len >= 1)"),
            (".ISZERO, &.{third[0]}", ".NOT, &.{third[0]}"),
            (".ISZERO, &.{arguments[1]}", ".ISZERO, &.{arguments[0]}"),
            ("const even = try classes.makeOperation(.ISZERO, &.{parity}, debug_data);",
             "const even = try classes.makeOperation(.ISZERO, &.{arguments[1]}, debug_data);"),
            ("const even = try classes.makeOperation(.ISZERO, &.{parity}, debug_data);",
             "const even = classes.makeOperation(.ISZERO, &.{parity}, debug_data);"),
            ("const parity = try classes.makeOperation(.AND, &.{ arguments[1], one }, debug_data);",
             "const parity = classes.makeOperation(.AND, &.{ arguments[1], one }, debug_data);"),
            ("if (base == 0)", "if (base == 1)"),
        ):
            with self.subTest(mutation=after), self.assertRaises(Unsupported):
                self.assertEqual(text.count(before), 1)
                admission.extract(text.replace(before, after).encode(), *rest)

    def test_comment_decoys_do_not_admit_changed_literal(self):
        source, *rest = admission.inputs()
        decoy = b"// return try classes.makeOperation(.ISZERO, &.{third[0]}, debug_data);\n"
        with self.assertRaises(Unsupported):
            admission.extract(decoy + source.replace(b"&.{third[0]}", b"&.{third[1]}"), *rest)
        self.assertNotEqual(admission.extract(decoy + source, *rest), admission.OUTPUT.read_bytes())


if __name__ == "__main__":
    unittest.main()
