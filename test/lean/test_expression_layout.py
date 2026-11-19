#!/usr/bin/env python3
"""Admission controls for the complete native Expression descriptor layout.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean/zig_air"))
import generate_expression_layout as admission
from check_expression_fields import check_observations
from extract_storage import Unsupported
from test_item_layout import fixture as item_fixture


def fixture(mode="ReleaseFast"):
    target = {**item_fixture(), "schema": "oksolc.expression-layout.v1", "mode": mode,
              "name": admission.NATIVE, "bytes": 32, "alignment": 8}
    fields = [{"name": name, "type": native, "offset": offset, "bytes": size, "alignment": alignment}
              for name, native, offset, size, alignment in (
                  ("id", "u32", 24, 4, 4), ("item", "*" + admission.ITEM, 0, 8, 8),
                  ("arguments", "[]u32", 8, 16, 8), ("sequence_number", "u32", 28, 4, 4))]
    return {"schema": "oksolc.expression-field-layout.v1", "target": target, "fields": fields,
            "item": {"name": admission.ITEM, "bytes": 224, "alignment": 16}}


class ExpressionLayoutTests(unittest.TestCase):
    def test_complete_current_layout_and_modes(self):
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            self.assertEqual(admission.generate(fixture(mode)), admission.OUTPUT.read_bytes())

    def test_field_order_is_canonical(self):
        profile = fixture()
        profile["fields"].reverse()
        self.assertEqual(admission.generate(profile), admission.OUTPUT.read_bytes())

    def test_complete_unique_field_inventory_is_required(self):
        for mutation in ("omit", "duplicate", "unknown", "extra-key", "wrong-container"):
            profile = fixture()
            if mutation == "omit":
                profile["fields"].pop()
            elif mutation == "duplicate":
                profile["fields"][3] = profile["fields"][0].copy()
            elif mutation == "unknown":
                profile["fields"][0]["name"] = "other"
            elif mutation == "extra-key":
                profile["fields"][0]["default"] = 0
            else:
                profile["fields"] = {}
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                admission.generate(profile)

    def test_every_field_type_geometry_and_offset_is_checked(self):
        for index in range(4):
            for key, value in (("type", "u64"), ("bytes", 0), ("bytes", True),
                               ("alignment", 1), ("alignment", False), ("offset", -1),
                               ("offset", 1), ("offset", 32), ("offset", True)):
                profile = fixture()
                profile["fields"][index][key] = value
                with self.subTest(index=index, key=key, value=value), self.assertRaises(ValueError):
                    admission.generate(profile)

    def test_overlapping_fields_reject(self):
        for index in (0, 2, 3):
            profile = fixture()
            profile["fields"][index]["offset"] = 0
            with self.subTest(index=index), self.assertRaisesRegex(ValueError, "overlapping"):
                admission.generate(profile)

    def test_nominal_item_target_is_reused(self):
        for key, value in (("name", "other.Item"), ("bytes", 240), ("alignment", 8), ("bytes", True)):
            profile = fixture()
            profile["item"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                admission.generate(profile)

    def test_target_and_profile_metadata_reject(self):
        for key, value in (("arch", "x86_64"), ("mode", "ReleaseSmall"), ("backend", "stage2_aarch64"),
                           ("pointerBits", 32), ("bytes", 0), ("alignment", 3), ("name", "other.Expression"),
                           ("cpuFeatures", [False]), ("osVersionRange", {}), ("unknown", 1)):
            profile = fixture()
            profile["target"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                admission.generate(profile)
        for key, value in (("schema", "unknown"), ("item", []), ("fields", None), ("unknown", 1)):
            profile = fixture()
            profile[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                admission.generate(profile)

    def test_changed_admissible_layout_is_not_the_committed_layout(self):
        profile = fixture()
        profile["target"]["bytes"] = 40
        self.assertNotEqual(admission.generate(profile), admission.OUTPUT.read_bytes())

    def test_source_field_changes_and_late_fields_reject(self):
        source = admission.storage.SOURCE.read_text()
        for before, after in (
                ("    id: Id,", "    id: u64,"),
                ("    arguments: []Id,", "    arguments: []const Id,"),
                ("    item: *AssemblyItem,", "    item: *const AssemblyItem,"),
                ("    sequence_number: u32 = 0,", "    sequence_number: u32 = 1,"),
                ("    pub fn eql(self: *const Expression, other: *const Expression) bool {",
                 "    extra: usize = 0,\n    pub fn eql(self: *const Expression, other: *const Expression) bool {"),
                ("\n};\n\nconst ExpressionKey =", "\n    extra: usize = 0,\n};\n\nconst ExpressionKey =")):
            # Only the owning Expression declaration is changed, even where an
            # insertion parameter elsewhere has the same spelling.
            self.assertIn(before, source)
            changed = source.replace(before, after, 1).encode()
            with self.subTest(mutation=after), self.assertRaises(Unsupported):
                admission.generate(fixture(), changed)

    def test_source_identity_is_retained(self):
        source = admission.storage.SOURCE.read_bytes()
        self.assertNotEqual(admission.generate(fixture(), b"// comment\n" + source), admission.OUTPUT.read_bytes())
        changed = copy.deepcopy(fixture())
        changed["fields"][1]["type"] = "*u8"
        with self.assertRaises(ValueError):
            admission.generate(changed)

    def observations(self):
        fields = {"item_pointer": 32, "arguments_pointer": 260, "arguments_length": 2, "id": 17, "sequence_number": 23}
        return {"schema": "oksolc.expression-field-observations.v1", "zigVersion": "0.17.0", "mode": "Debug",
            "backend": "stage2_llvm", "item_pointer": 32, "argument_allocation_pointer": 256,
            "argument_allocation_length": 4, "descriptor_pointers": [512, 544], "descriptor_bytes": 32,
            "descriptor_alignment": 8, "before": [fields.copy(), fields.copy()],
            "after": [fields.copy(), {**fields, "id": 19, "sequence_number": 29}], "borrowed_arguments": [99, 1]}

    def test_native_field_observations_are_complete_and_typed(self):
        original = self.observations()
        check_observations(original, "Debug")
        for label in ("before", "after"):
            for key in original[label][0]:
                changed = copy.deepcopy(original)
                del changed[label][0][key]
                with self.subTest(label=label, omitted=key), self.assertRaises(ValueError):
                    check_observations(changed, "Debug")
                for value in (0, True, "changed"):
                    changed = copy.deepcopy(original)
                    changed[label][0][key] = value
                    with self.subTest(label=label, key=key, value=value), self.assertRaises(ValueError):
                        check_observations(changed, "Debug")
        for key, value in (("item_pointer", 33), ("item_pointer", 512), ("item_pointer", True),
                           ("argument_allocation_pointer", 258), ("descriptor_pointers", [512, 548]),
                           ("descriptor_pointers", [512, True]), ("descriptor_pointers", []),
                           ("descriptor_bytes", True), ("descriptor_alignment", 4),
                           ("borrowed_arguments", [1, 99]), ("borrowed_arguments", [99, True]),
                           ("before", []), ("unknown", 1)):
            changed = copy.deepcopy(original)
            changed[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                check_observations(changed, "Debug")


if __name__ == "__main__":
    unittest.main()
