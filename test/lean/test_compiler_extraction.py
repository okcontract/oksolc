#!/usr/bin/env python3
"""
// SPDX-License-Identifier: GPL-3.0
// Copyright (C) 2026 OKcontract Pte. Ltd.

Tests of the trusted extraction boundary, including supported semantic mutations.
Kernel checks of the mutations are also required by check_compiler.py.
"""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "lean"))
import extract_compiler as extraction
import compiler_ir

# Each mutation must translate from its actual body, then fail its Lean claim.
# Imports and definitions are generated independently for each retained input.
MUTATIONS = {
    "guard_constant": (".left_zero => facts.left == 0", ".left_zero => facts.left == 1",
                       "zigMatches .left_zero { left := some 0 } = true"),
    "guard_operand": (".left_zero => facts.left == 0", ".left_zero => facts.right == 0",
                      "zigMatches .left_zero { left := some 0 } = true"),
    "guard_negated": (".left_zero => facts.left == 0", ".left_zero => facts.left != 0",
                      "zigMatches .left_zero { left := some 0 } = true"),
    "wrong_stage": ("if (rule.guard == .equal) .equal else .constants",
                    "if (rule.guard == .equal) .constants else .equal",
                    "zigSelect (productionOpcode .add) .constants { right := some 0 } = some .left"),
    "wrong_return": ("return rule.replacement;", "return .zero;",
                     "zigSelect (productionOpcode .add) .constants { right := some 0 } = some .left"),
    "lost_return": ("return rule.replacement;", "return null;",
                    "zigSelect (productionOpcode .add) .constants { right := some 0 } = some .left"),
    "weakened_guard": ("stage == rule_stage and matches", "stage == rule_stage or matches",
                       "zigSelect (productionOpcode .add) .constants {} = none"),
    "wrong_opcode": ("@backingInt(rule.instruction) == opcode", "@backingInt(rule.instruction) != opcode",
                     "zigSelect 0 .constants { right := some 0 } = none"),
}

CONSTRUCTION_MUTATIONS = {
    "capture": (".left => left,", ".left => right,",
        "zigApply .left callbacks 2 3 9 { budget := 0 } = (.ok 2, { budget := 0 })"),
    "constant": (".zero => try classes.makeConstant(0, debug_data)",
        ".zero => try classes.makeConstant(1, debug_data)",
        "zigApply .zero callbacks 2 3 9 {} = (.ok 7, { events := [.constant 0 9], next := 8, budget := 1 })"),
    "not_operand": (".not_right => try classes.makeOperation(.NOT, &.{right}, debug_data)",
        ".not_right => try classes.makeOperation(.NOT, &.{left}, debug_data)",
        "zigApply .not_right callbacks 2 3 9 {} = (.ok 7, { events := [.operation .NOT [3] 9], next := 8, budget := 1 })"),
    "neg_operand": ("if (replacement == .neg_left) left else right",
        "if (replacement == .neg_left) right else left",
        "zigApply .neg_left callbacks 2 3 9 {} = (.ok 8, { events := [.constant 0 9, .operation .SUB [7, 2] 9], next := 9, budget := 0 })"),
    "bool_operand": ("if (replacement == .bool_left) left else right",
        "if (replacement == .bool_left) right else left",
        "zigApply .bool_left callbacks 2 3 9 {} = (.ok 8, { events := [.operation .ISZERO [2] 9, .operation .ISZERO [7] 9], next := 9, budget := 0 })"),
    "second_call": ("break :blk try classes.makeOperation(.ISZERO, &.{first}, debug_data)",
        "break :blk try classes.makeOperation(.ISZERO, &.{left}, debug_data)",
        "zigApply .bool_left callbacks 2 3 9 {} = (.ok 8, { events := [.operation .ISZERO [2] 9, .operation .ISZERO [7] 9], next := 9, budget := 0 })"),
}


def mutate(data, old, new):
    if data.count(old.encode()) != 1:
        raise ValueError("mutation anchor changed or is ambiguous: " + old)
    return data.replace(old.encode(), new.encode())


def semantic_part(data):
    return b"\n".join(line for line in data.splitlines() if not line.startswith(b"-- Source SHA-256:"))


class ExtractionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = extraction.SOURCE.read_bytes()

    def test_checked_source(self):
        self.assertEqual(extraction.extract(self.source), extraction.OUTPUT.read_bytes())
        self.assertEqual(extraction.extract_construction(self.source), extraction.CONSTRUCTION.read_bytes())
        self.assertEqual(compiler_ir.extract(self.source), compiler_ir.OUTPUT.read_bytes())

    def test_semantic_mutations_change_definitions(self):
        checked = semantic_part(extraction.extract(self.source))
        for name, (old, new, _) in MUTATIONS.items():
            with self.subTest(name=name):
                changed = extraction.extract(mutate(self.source, old, new))
                self.assertNotEqual(semantic_part(changed), checked)
                self.assertNotEqual(semantic_part(compiler_ir.extract(mutate(self.source, old, new))),
                                    semantic_part(compiler_ir.OUTPUT.read_bytes()))

    def test_comments_do_not_change_semantics(self):
        self.assertEqual(semantic_part(extraction.extract(self.source)),
                         semantic_part(extraction.extract(b"// prose and tokens: return null;\n" + self.source)))
        self.assertEqual(semantic_part(compiler_ir.extract(self.source)),
                         semantic_part(compiler_ir.extract(b"// return null;\n" + self.source)))

    def test_construction_mutations_change_definitions(self):
        checked = semantic_part(extraction.extract_construction(self.source))
        for name, (old, new, _) in CONSTRUCTION_MUTATIONS.items():
            with self.subTest(name=name):
                changed = extraction.extract_construction(mutate(self.source, old, new))
                self.assertNotEqual(semantic_part(changed), checked)
                self.assertNotEqual(semantic_part(compiler_ir.extract(mutate(self.source, old, new))),
                                    semantic_part(compiler_ir.OUTPUT.read_bytes()))

    def test_construction_fail_closed(self):
        cases = [
            (".left => left,", ".left => debug_data,"),
            (".zero => try classes.makeConstant(0, debug_data)", ".zero => classes.makeConstant(0, debug_data)"),
            (".not_right => try classes.makeOperation(.NOT, &.{right}, debug_data)",
             ".not_right => try classes.makeOperation(.NOT, &.{right, left}, debug_data)"),
            (".not_right => try classes.makeOperation(.NOT, &.{right}, debug_data)",
             ".not_right => try classes.makeOperation(.UNKNOWN, &.{right}, debug_data)"),
            ("const first =", "const classes ="),
            ("const first =", "const debug_data ="),
            ("break :blk", "break :different"),
            ("if (replacement == .neg_left) left else right", "try classes.makeConstant(1, debug_data)"),
            (".zero => try classes.makeConstant(0, debug_data)", ".zero => try classes.unknown(0, debug_data)"),
            (".zero => try classes.makeConstant(0, debug_data)", ".zero => try classes.makeConstant(0, left)"),
        ]
        for old, new in cases:
            with self.subTest(old=old):
                with self.assertRaises(extraction.Unsupported):
                    extraction.extract_construction(mutate(self.source, old, new))

    def test_fail_closed(self):
        cases = [
            ("facts.left == 0", "unknown(facts.left)"),
            ("facts.left == 0", "facts.left.? == 0"),
            ("facts.left == 0", "facts.left + 1 == 0"),
            ("facts.left == 0", "facts.missing == 0"),
            ("return rule.replacement;", "return matches(rule.guard, facts);"),
            ("inline for (rules)", "inline for (rules.reverse())"),
            ("inline for (rules)", "while (true)"),
            ("const rule_stage:", "var rule_stage:"),
            ("const rule_stage: Stage", "const rule_stage: u32"),
            ("|opcode|", "|facts|"),
            ("const max_word = ~@as(u256, 0)", "const max_word = 0"),
            ("@setEvalBranchQuota(256 * (rules.len + 1) * 4)", "@setEvalBranchQuota(sideEffect())"),
            (".equal => facts.equal", ".equal => facts.equal, .equal => false"),
            (".equal => facts.equal,", ""),
            ("facts.left == 0", "facts.left == " + str(2**256)),
        ]
        for old, new in cases:
            with self.subTest(old=old):
                with self.assertRaises(extraction.Unsupported):
                    extraction.extract(mutate(self.source, old, new))
        for suffix in (b"pub fn hidden() void {}", b"\x00", b"/* hidden */"):
            with self.subTest(suffix=suffix):
                with self.assertRaises(extraction.Unsupported):
                    extraction.extract(self.source + suffix)


if __name__ == "__main__":
    unittest.main()
