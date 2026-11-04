#!/usr/bin/env python3
"""Fail-closed admission controls for native negation argument preparation.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import extract_temporary_arguments as admission
from extract_compiler import Unsupported


class TemporaryArgumentsTests(unittest.TestCase):
    def test_current_source_and_generated_program_are_bound(self):
        self.assertEqual(admission.extract(admission.SOURCE.read_bytes()), admission.OUTPUT.read_bytes())
        self.assertEqual(admission.check()["admittedBranches"], ["neg_left", "neg_right"])
        self.assertFalse(admission.check()["completeRecursiveConstructorsVerified"])

    def test_initializer_mutations_reject(self):
        source = admission.SOURCE.read_text()
        for before, after in (
            ("try classes.makeConstant(0, debug_data),\n            if (replacement == .neg_left) left else right,",
             "if (replacement == .neg_left) left else right,\n            try classes.makeConstant(0, debug_data),"),
            ("try classes.makeOperation(.SUB", "classes.makeOperation(.SUB"),
            ("try classes.makeOperation(.SUB", "try classes.makeOperation(.ADD"),
            ("            try classes.makeConstant(0, debug_data),", "            try classes.makeConstant(1, debug_data),"),
            ("if (replacement == .neg_left) left else right,", "if (replacement == .neg_left) right else left,"),
            ("if (replacement == .neg_left) left else right,", "try classes.makeConstant(1, debug_data),"),
            ("            try classes.makeConstant(0, debug_data),", "            classes.makeConstant(0, debug_data),"),
            ("left: u32", "left: u64"),
        ):
            with self.subTest(mutation=after), self.assertRaises(Unsupported):
                self.assertEqual(source.count(before), 1)
                admission.extract(source.replace(before, after).encode())

    def test_comments_do_not_supply_or_replace_the_initializer(self):
        source = admission.SOURCE.read_bytes()
        changed = source.replace(b"try classes.makeConstant(0, debug_data),", b"try classes.makeConstant(1, debug_data),")
        decoy = b"// " + admission.INITIALIZER.replace("\n", " ").encode() + b"\n"
        with self.assertRaises(Unsupported):
            admission.extract(decoy + changed)
        self.assertNotEqual(admission.extract(decoy + source), admission.OUTPUT.read_bytes())


if __name__ == "__main__":
    unittest.main()
