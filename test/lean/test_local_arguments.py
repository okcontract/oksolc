#!/usr/bin/env python3
"""Fail-closed controls for the named local's complete owning helper.
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
import extract_local_arguments as admission
from extract_compiler import Unsupported
from constructor_array_checks import local_inventory


class LocalArgumentsTests(unittest.TestCase):
    def inputs(self):
        nested = admission.construction.nested
        return nested.SOURCE.read_bytes(), nested.OPCODES.read_bytes(), nested.STORAGE.read_bytes()

    def test_complete_owner_and_generated_segment_are_bound(self):
        self.assertEqual(admission.extract(*self.inputs()), admission.OUTPUT.read_bytes())
        report = admission.check()
        self.assertTrue(report["allocationBeforeInitializerReads"])
        self.assertTrue(report["aggregateInitialization"])
        self.assertFalse(report["completeHelperNativeCorrespondenceVerified"])
        self.assertFalse(report["completeRecursiveConstructorsVerified"])

    def test_copy_selection_guard_and_handoff_mutations_reject(self):
        source, opcodes, storage = self.inputs()
        text = source.decode()
        for before, after in (
            ("var operands = [2]ExpressionId{ nested[0], nested[1] };", "var operands = [2]ExpressionId{ nested[1], nested[0] };"),
            ("var operands = [2]ExpressionId{ nested[0], nested[1] };", "var operands = [2]ExpressionId{ repeated, nested[1] };"),
            ("var operands = [2]ExpressionId{ nested[0], nested[1] };", "const operands = [2]ExpressionId{ nested[0], nested[1] };"),
            ("var operands = [2]ExpressionId{ nested[0], nested[1] };", "var operands = [3]ExpressionId{ nested[0], nested[1], repeated };"),
            ("if (sameExpression(classes, nested[1], repeated)) 1", "if (sameExpression(classes, nested[0], repeated)) 0"),
            ("if (repeated_is_first) operands[repeated_index] = repeated;", "operands[repeated_index] = repeated;"),
            ("if (repeated_is_first) operands[repeated_index] = repeated;", "if (!repeated_is_first) operands[repeated_index] = repeated;"),
            ("operands[repeated_index] = repeated;", "operands[0] = repeated;"),
            ("return try classes.makeOperation(instruction, &operands, debug_data);", "return classes.makeOperation(instruction, &operands, debug_data);"),
            ("return try classes.makeOperation(instruction, &operands, debug_data);", "return try classes.makeOperation(instruction, nested, debug_data);"),
        ):
            with self.subTest(mutation=after), self.assertRaises(Unsupported):
                self.assertEqual(text.count(before), 1)
                admission.extract(text.replace(before, after).encode(), opcodes, storage)
        start = text.index("fn dropRepeatedNested(")
        end = text.index("\n}\n", start) + 3
        helper = text[start:end]
        self.assertEqual(helper.count("if (nested.len != 2) return null;"), 1)
        changed = text[:start] + helper.replace("if (nested.len != 2) return null;", "if (nested.len < 2) return null;") + text[end:]
        with self.assertRaises(Unsupported):
            admission.extract(changed.encode(), opcodes, storage)

    def test_comments_cannot_admit_changed_initializer(self):
        source, opcodes, storage = self.inputs()
        decoy = b"// var operands = [2]ExpressionId{ nested[0], nested[1] };\n"
        changed = source.replace(b"var operands = [2]ExpressionId{ nested[0], nested[1] };",
                                 b"var operands = [2]ExpressionId{ nested[1], nested[0] };")
        with self.assertRaises(Unsupported):
            admission.extract(decoy + changed, opcodes, storage)
        self.assertNotEqual(admission.extract(decoy + source, opcodes, storage), admission.OUTPUT.read_bytes())

    def test_named_array_inventory_rejects_wrong_store_and_read_shapes(self):
        word = {"kind": "int", "bits": 32, "signedness": "unsigned"}
        array = {"kind": "array", "length": 2, "sentinel": None, "child": word,
                 "layout": {"kind": "abi", "bytes": 8, "alignment": 4}}
        reference = lambda index: {"kind": "instruction", "index": index}
        source_type = {"flags": {"size": "slice", "isConst": True}, "child": word}
        record = {"instructions": [
            {"index": 0, "tag": "alloc", "allocationKind": "stack", "type": {
                "kind": "pointer", "flags": {"isConst": False}, "child": array}},
            {"index": 1, "tag": "load", "operand": reference(99), "type": source_type},
            {"index": 2, "tag": "slice_elem_ptr", "lhs": reference(1), "rhs": {"value": 0}},
            {"index": 3, "tag": "load", "operand": reference(2)},
            {"index": 4, "tag": "load", "operand": reference(99), "type": source_type},
            {"index": 5, "tag": "slice_elem_ptr", "lhs": reference(4), "rhs": {"value": 1}},
            {"index": 6, "tag": "load", "operand": reference(5)},
            {"index": 7, "tag": "aggregate_init", "type": array, "unsupportedPayload": True},
            {"index": 8, "tag": "store", "lhs": reference(0), "rhs": reference(7)},
            {"index": 9, "tag": "ptr_elem_ptr", "lhs": reference(0), "rhs": reference(98)},
            {"index": 10, "tag": "store_safe", "lhs": reference(9)},
            {"index": 11, "tag": "array_to_slice", "unsupportedPayload": True}]}
        mutations = []
        for position in (3, 6, 7, 8, 9, 10, 11):
            changed = deepcopy(record)
            changed["instructions"].pop(position)
            mutations.append(changed)
        changed = deepcopy(record)
        del changed["instructions"][0]["type"]["child"]["sentinel"]
        mutations.append(changed)
        for position, field, value in ((0, "allocationKind", "heap"), (2, "rhs", {"value": 1}),
                                        (4, "operand", reference(98)), (8, "rhs", reference(6)),
                                        (9, "rhs", {"kind": "constant", "value": 0})):
            changed = deepcopy(record)
            changed["instructions"][position][field] = value
            mutations.append(changed)
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "air.json"
            path.write_text(json.dumps(record))
            accepted = local_inventory(path)
            self.assertEqual(accepted["initializerReadInstructions"], [3, 6])
            self.assertFalse(accepted["airControlSemanticsVerified"])
            for changed in mutations:
                path.write_text(json.dumps(changed))
                with self.assertRaises(ValueError):
                    local_inventory(path)


if __name__ == "__main__":
    unittest.main()
