#!/usr/bin/env python3
"""Source and shared-script controls for max-base EXP constructor admission.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
from pathlib import Path
import copy
import json
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean"))
import extract_rule_max_exponent as admission
from extract_compiler import Unsupported
from constructor_array_checks import max_exponent_inventory


def captured_fixture():
    """A compact decoded-operand fixture; try and slice payloads stay opaque."""
    word = {"kind": "int", "bits": 32, "signedness": "unsigned"}
    ref = lambda index: {"kind": "instruction", "index": index}
    instructions = []

    def emit(index, tag, **fields):
        instructions.append({"index": index, "tag": tag, "payloadVisited": True, **fields})

    def operation(index, slice_index):
        emit(index, "call", callee={"kind": "function", "identity": {"name": "fixture.Graph.makeOperation"}},
             arguments=[ref(0), {"kind": "unsupported", "reason": "constant-type"}, ref(slice_index), ref(1)])

    def array(index, values):
        emit(index, "alloc", allocationKind="stack", type={"kind": "pointer", "child": {
            "kind": "array", "length": len(values), "child": word,
            "layout": {"kind": "abi", "bytes": len(values) * 4, "alignment": 4}, "sentinel": None}})
        for offset, value in enumerate(values):
            element = index + offset * 2 + 1
            emit(element, "ptr_elem_ptr", lhs=ref(index), rhs={"kind": "constant", "value": offset})
            emit(element + 1, "store", lhs=ref(element), rhs=ref(value))
        slice_index = index + len(values) * 2 + 1
        emit(slice_index, "array_to_slice", unsupportedPayload=True)
        operation(slice_index + 1, slice_index)

    emit(10, "call", callee={"kind": "function", "identity": {"name": "fixture.Graph.makeConstant"}},
         arguments=[ref(0), {"kind": "constant", "value": 1}, ref(1)])
    emit(11, "try", type=word, unsupportedPayload=True)
    emit(14, "load", operand=ref(0), type={"kind": "pointer", "child": word, "flags": {"size": "slice", "isConst": True}})
    emit(15, "slice_elem_ptr", lhs=ref(14), rhs={"kind": "constant", "value": 1})
    emit(16, "load", operand=ref(15), type=word)
    array(20, [16, 11])
    emit(27, "try", type=word, unsupportedPayload=True)
    array(30, [27])
    emit(35, "try", type=word, unsupportedPayload=True)
    array(40, [35, 27])
    return {"bodyTraversal": "supported-structured-containers-only", "instructions": instructions}


class RuleMaxExponentTests(unittest.TestCase):
    def test_complete_owner_and_shared_script(self):
        self.assertEqual(admission.extract(*admission.owner.inputs()), admission.OUTPUT.read_bytes())
        report = admission.check()
        self.assertEqual(report["pairLiteralSites"], 2)
        self.assertFalse(report["completeExponentRuleVerified"])
        self.assertFalse(report["nativeQueryCorrespondenceVerified"])
        self.assertFalse(report["completeRecursiveConstructorsVerified"])
        script = admission.OUTPUT.read_text()
        self.assertIn("Compiler.Extraction.Dispatch.maxExponent", script)
        self.assertNotIn("let one ←", script)

    def test_every_constructor_and_its_order_are_source_bound(self):
        source, *rest = admission.owner.inputs()
        text = source.decode()
        for before, after in (
            ("const one = try classes.makeConstant(1, debug_data);", "const one = try classes.makeConstant(2, debug_data);"),
            ("const one = try classes.makeConstant(1, debug_data);", "const one = classes.makeConstant(1, debug_data);"),
            (".AND, &.{ arguments[1], one }", ".AND, &.{ arguments[0], one }"),
            (".AND, &.{ arguments[1], one }", ".AND, &.{ one, arguments[1] }"),
            ("const parity = try classes.makeOperation(.AND, &.{ arguments[1], one }, debug_data);",
             "const parity = classes.makeOperation(.AND, &.{ arguments[1], one }, debug_data);"),
            (".ISZERO, &.{parity}", ".ISZERO, &.{one}"),
            (".SUB, &.{ even, parity }", ".SUB, &.{ parity, even }"),
            ("return try classes.makeOperation(.SUB, &.{ even, parity }, debug_data);",
             "return classes.makeOperation(.SUB, &.{ even, parity }, debug_data);"),
            ("if (base == max_word)", "if (base == 2)"),
        ):
            with self.subTest(mutation=after), self.assertRaises(Unsupported):
                self.assertEqual(text.count(before), 1)
                admission.extract(text.replace(before, after).encode(), *rest)
        first = "const one = try classes.makeConstant(1, debug_data);"
        second = "const parity = try classes.makeOperation(.AND, &.{ arguments[1], one }, debug_data);"
        with self.assertRaises(Unsupported):
            admission.extract(text.replace(first + "\n                " + second,
                                          second + "\n                " + first).encode(), *rest)

    def test_comment_decoy_does_not_admit_changed_operand(self):
        source, *rest = admission.owner.inputs()
        decoy = b"// .AND, &.{ arguments[1], one }\n"
        with self.assertRaises(Unsupported):
            admission.extract(decoy + source.replace(b".AND, &.{ arguments[1], one }", b".AND, &.{ arguments[0], one }"), *rest)

    def test_decoded_air_initializers_and_corruption_controls(self):
        fixture = captured_fixture()
        with tempfile.TemporaryDirectory(prefix="max-exponent-air-", dir="/private/tmp") as directory:
            path = Path(directory) / "capture.json"
            path.write_text(json.dumps(fixture))
            result = max_exponent_inventory(path, pair_count=2, unary_count=1)
            self.assertEqual(result["constructorChain"]["constantCallInstruction"], 10)
            self.assertEqual(result["constructorChain"]["finalCallInstruction"], 46)
            self.assertFalse(result["airControlSemanticsVerified"])
            self.assertFalse(result["tryAndSliceProvenanceVerified"])
            self.assertFalse(result["sourceCallSiteCoverageVerified"])
            for name, index, key, value in (
                ("wrong-exponent-offset", 15, "rhs", {"kind": "constant", "value": 0}),
                ("writable-source", 14, "type", {"kind": "pointer", "child": fixture["instructions"][1]["type"], "flags": {"size": "slice", "isConst": False}}),
                ("wrong-loaded-width", 16, "type", {"kind": "int", "bits": 64, "signedness": "unsigned"}),
                ("wrong-one", 24, "rhs", {"kind": "instruction", "index": 16}),
                ("wrong-parity", 32, "rhs", {"kind": "instruction", "index": 11}),
                ("wrong-even", 42, "rhs", {"kind": "instruction", "index": 27}),
                ("wrong-final-parity", 44, "rhs", {"kind": "instruction", "index": 11}),
                ("wrong-final-slice", 46, "arguments", [{"kind": "instruction", "index": 0}, {}, {"kind": "instruction", "index": 33}, {}]),
                ("wrong-constant", 10, "arguments", [{"kind": "instruction", "index": 0}, {"kind": "constant", "value": 2}, {}]),
                ("read-before-constant", 10, "index", 18),
                ("store-before-allocation", 22, "index", 13),
                ("wrong-final-callee", 46, "callee", {"kind": "function", "identity": {"name": "fixture.Graph.makeConstant"}}),
            ):
                with self.subTest(mutation=name), self.assertRaises(ValueError):
                    changed = copy.deepcopy(fixture)
                    next(inst for inst in changed["instructions"] if inst["index"] == index)[key] = value
                    path.write_text(json.dumps(changed))
                    max_exponent_inventory(path, pair_count=2, unary_count=1)
            with self.assertRaises(ValueError):
                changed = copy.deepcopy(fixture)
                changed["instructions"].append(copy.deepcopy(changed["instructions"][0]))
                path.write_text(json.dumps(changed))
                max_exponent_inventory(path, pair_count=2, unary_count=1)


if __name__ == "__main__":
    unittest.main()
