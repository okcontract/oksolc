#!/usr/bin/env python3
"""Fail-closed admission of native representative headers and reader evidence.
// Copyright (C) 2026 OKcontract Pte. Ltd.
// SPDX-License-Identifier: GPL-3.0
"""
import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "lean/zig_air"))
import generate_representative_array_layout as admission
from check_representative_array import check_observations
from extract_storage import Unsupported
from test_item_layout import fixture as item_fixture


def fixture(mode="ReleaseFast"):
    owner_size, cache_size = (56, 16) if mode == "ReleaseFast" else (72, 24)
    target = {**item_fixture(), "schema": "oksolc.representative-header-layout.v1", "mode": mode,
        "name": admission.NATIVE, "bytes": 24 if mode == "ReleaseFast" else 32, "alignment": 8}
    fields = [{"name": "items", "type": "[]" + admission.ELEMENT, "offset": 0, "bytes": 16, "alignment": 8},
        {"name": "capacity", "type": "usize", "offset": 16, "bytes": 8, "alignment": 8}]
    fields.append({"name": "pointer_stability", "type": "debug.SafetyLock", "offset": 24,
        "bytes": 0 if mode == "ReleaseFast" else 8, "alignment": 1 if mode == "ReleaseFast" else 8})
    owner = {"target": {**target, "schema": "oksolc.expression-owner-layout.v1", "name": admission.OWNER, "bytes": owner_size},
        "fields": [{"name": "allocator", "type": "mem.Allocator", "offset": 0, "bytes": 16, "alignment": 8},
            {"name": "representatives", "type": admission.NATIVE, "offset": 16, "bytes": 24 if mode == "ReleaseFast" else 32, "alignment": 8},
            {"name": "expressions", "type": admission.MAP, "offset": 40 if mode == "ReleaseFast" else 48, "bytes": cache_size, "alignment": 8},
            {"name": "test_id_limit", "type": "void", "offset": 0, "bytes": 0, "alignment": 1}]}
    cache = {"target": {**target, "schema": "oksolc.expression-map-layout.v1", "name": admission.MAP, "bytes": cache_size},
        "fields": [{"name": "metadata", "type": "?[*]" + admission.MAP + ".Metadata", "offset": 0, "bytes": 8, "alignment": 8},
            {"name": "size", "type": "u32", "offset": 8 if mode == "ReleaseFast" else 16, "bytes": 4, "alignment": 4},
            {"name": "available", "type": "u32", "offset": 12 if mode == "ReleaseFast" else 20, "bytes": 4, "alignment": 4},
            {"name": "pointer_stability", "type": "debug.SafetyLock", "offset": 16 if mode == "ReleaseFast" else 8, "bytes": 0 if mode == "ReleaseFast" else 8, "alignment": 1 if mode == "ReleaseFast" else 8}],
        "metadata": {"pointer": {"name": "[*]" + admission.MAP + ".Metadata", "bytes": 8, "alignment": 8,
            "is_const": False, "is_allowzero": False, "size": "many"},
            "child": {"name": admission.MAP + ".Metadata", "bytes": 1, "alignment": 1}},
        "lock": {"fields": [{"name": "state", "type": "debug.SafetyLock.State__enum_1234", "offset": 0,
            "bytes": 0 if mode == "ReleaseFast" else 8, "alignment": 1 if mode == "ReleaseFast" else 8}],
            "state_bits": 0 if mode == "ReleaseFast" else 64, "exhaustive": mode == "ReleaseFast", "initial": 0,
            "states": [{"name": name, "value": value} for name, value in
                ([("unknown", 0)] if mode == "ReleaseFast" else [("unlocked", 0), ("exclusive", 2**64 - 1)])]}}
    return {"schema": "oksolc.representative-array-layout.v5", "target": target, "fields": fields,
        "element": {"name": admission.ELEMENT, "bytes": 32, "alignment": 8}, "owner": owner, "cache": cache}


def observations(mode="Debug"):
    rows = [{"pointer": 512 + index * 32, "readonly": True, "item_pointer": 1024 + index * 256,
        "arguments_pointer": (2400 + index * 8) if arguments else 2**64 - 1,
        "arguments_length": len(arguments), "arguments": arguments, "id": index, "sequence_number": 23 if index == 4 else 0}
        for index, arguments in enumerate(([], [], [0], [1], [3, 2]))]
    owned_rows = [{"pointer": 524288 + index * 32, "readonly": True, "item_pointer": 525312 + index * 256,
        "arguments_pointer": 526336 if index else 2**64 - 1, "arguments_length": index, "arguments": [0] if index else [],
        "id": index, "sequence_number": 0} for index in range(2)]
    return {"schema": "oksolc.representative-array-observations.v11", "zigVersion": "0.17.0", "mode": mode,
        "owner_pointer": 4080, "owner_bytes": 56 if mode == "ReleaseFast" else 72,
        "owner_alignment": 8, "allocator_pointer": 4080, "expressions_pointer": 4120 if mode == "ReleaseFast" else 4128,
        "backend": "stage2_llvm", "header_pointer": 4096, "header_bytes": 24 if mode == "ReleaseFast" else 32, "header_alignment": 8,
        "items_pointer": 512, "length": 5, "capacity": 8, "element_bytes": 32, "element_alignment": 8,
        "empty_rejected": True, "length_rejected": True, "capacity_rejected": True, "maximum_rejected": True,
        "cache_hit": True, "cache_hit_size_unchanged": True,
        "before_append_length": 4, "before_append_capacity": 8, "before_append_pointer": 512,
        "append_size_increased": True, "append_capacity_unchanged": True, "append_backing_unchanged": True,
        "append_id_matches_previous_length": True,
        "parent_pointer": 8192, "parent_before": [777, 3, 2, 5], "parent_after": [777, 3, 2, 5], "parent_offset": 1, "parent_length": 2,
        "representatives": rows,
        "owned_append": {"owner_pointer": 527360, "before": {"pointer": 2**64 - 1, "length": 0, "capacity": 0},
            "first_header": {"pointer": 524288, "length": 1, "capacity": 5}, "first": copy.deepcopy(owned_rows[0]),
            "after": {"pointer": 524288, "length": 2, "capacity": 5}, "rows": owned_rows,
            "length_rejected": True, "capacity_rejected": True},
        "first_growth": {"before": {"pointer": 2**64 - 1, "length": 0, "capacity": 0},
            "noop": {"pointer": 2**64 - 1, "length": 0, "capacity": 0},
            "failed": {"pointer": 2**64 - 1, "length": 0, "capacity": 0},
            "after": {"pointer": 65536, "length": 0, "capacity": 3},
            "unchanged": {"pointer": 65536, "length": 0, "capacity": 3},
            "noop_skipped_allocator": True, "oom_reported": True, "oom_induced": True,
            "allocated_bytes": 96, "allocations": 1, "allocation_calls": 2, "requested_bytes": 96,
            "requested_alignment": 8, "resize_calls": 0, "remap_calls": 0, "free_calls": 0},
        "capacity_selection": {"arch": "aarch64", "cache_line": 128,
            "samples": [{"minimum": minimum, "capacity": capacity} for minimum, capacity in (
                (0, 4), (1, 5), (2, 7), (3, 8), (8, 16),
                (9223372036854775807, 13835058055282163714),
                (18446744073709551614, 18446744073709551615),
                (18446744073709551615, 18446744073709551615))],
            "first_growth": {"before": {"pointer": 2**64 - 1, "length": 0, "capacity": 0},
                "noop": {"pointer": 2**64 - 1, "length": 0, "capacity": 0},
                "failed": {"pointer": 2**64 - 1, "length": 0, "capacity": 0},
                "after": {"pointer": 131072, "length": 0, "capacity": 5},
                "unchanged": {"pointer": 131072, "length": 0, "capacity": 5},
                "noop_skipped_allocator": True, "oom_reported": True, "oom_induced": True,
                "allocated_bytes": 160, "allocations": 1, "allocation_calls": 2, "requested_bytes": 160,
                "requested_alignment": 8, "resize_calls": 0, "remap_calls": 0, "free_calls": 0},
            "overflow_oom": True,
            "overflow_before": {"pointer": 2**64 - 1, "length": 0, "capacity": 0},
            "overflow_after": {"pointer": 2**64 - 1, "length": 0, "capacity": 0}},
        "growing_append": {"before": {"pointer": 2**64 - 1, "length": 0, "capacity": 0},
            "failed": {"pointer": 2**64 - 1, "length": 0, "capacity": 0},
            "after": {"pointer": 262144, "length": 1, "capacity": 5}, "oom_reported": True, "oom_induced": True,
            "allocated_bytes": 160, "allocations": 1, "allocation_calls": 2, "requested_bytes": 160,
            "requested_alignment": 8, "resize_calls": 0, "remap_calls": 0, "free_calls": 0,
            "record": {"pointer": 262144, "readonly": True, "item_pointer": 2048,
                "arguments_pointer": 8196, "arguments_length": 2, "arguments": [3, 2], "id": 0, "sequence_number": 29},
            "parent_after": [777, 3, 2, 5]},
        "copy": {"source_before": copy.deepcopy(rows), "header_before": {"pointer": 512, "length": 5, "capacity": 8},
            "target_pointer": 16384, "target_capacity": 7,
            "copied": [dict(row, pointer=16384 + index * 32) for index, row in enumerate(rows)]},
        "publication": {"before": {"pointer": 16384, "length": 5, "capacity": 7},
            "after": {"pointer": 32768, "length": 5, "capacity": 10},
            "representatives": [dict(row, pointer=32768 + index * 32) for index, row in enumerate(rows)]}}


class RepresentativeArrayTests(unittest.TestCase):
    def test_owned_first_and_spare_append(self):
        for path, value in (
                (("before", "length"), 1), (("before", "capacity"), 5), (("first_header", "length"), 0),
                (("first_header", "capacity"), 0), (("first_header", "pointer"), 524320), (("after", "length"), 1),
                (("after", "capacity"), 6), (("owner_pointer",), True), (("owner_pointer",), 524288),
                (("length_rejected",), False), (("capacity_rejected",), 1), (("first", "id"), True),
                (("first", "sequence_number"), 9), (("rows", 0, "sequence_number"), 9),
                (("rows", 1, "id"), 0), (("rows", 1, "pointer"), 524288), (("rows", 1, "arguments"), [1]),
                (("rows", 1, "arguments_length"), 2), (("rows", 1, "arguments_pointer"), 524288),
                (("rows", 1, "arguments_pointer"), 2**64), (("rows", 1, "item_pointer"), 525312)):
            profile = observations()
            owner = profile["owned_append"]
            for key in path[:-1]:
                owner = owner[key]
            owner[path[-1]] = value
            with self.subTest(path=path, value=value), self.assertRaises(ValueError):
                check_observations(profile, "Debug")
        for key in observations()["owned_append"]:
            profile = observations()
            del profile["owned_append"][key]
            with self.subTest(missing=key), self.assertRaises(ValueError):
                check_observations(profile, "Debug")

    def test_first_growth_requires_all_headers_and_allocator_effects(self):
        original = observations()
        check_observations(original, "Debug")
        for selected in (False, True):
            def growth(profile):
                return (profile["capacity_selection"] if selected else profile)["first_growth"]
            for key, value in growth(original).items():
                profile = copy.deepcopy(original)
                del growth(profile)[key]
                with self.subTest(selected=selected, missing=key), self.assertRaises(ValueError):
                    check_observations(profile, "Debug")
                if isinstance(value, dict):
                    for field, expected in value.items():
                        for changed in (True, expected + 1):
                            profile = copy.deepcopy(original)
                            growth(profile)[key][field] = changed
                            with self.subTest(selected=selected, header=key, field=field, value=changed), self.assertRaises(ValueError):
                                check_observations(profile, "Debug")
                else:
                    for changed in ((False, 1) if type(value) is bool else (True, value + 1)):
                        profile = copy.deepcopy(original)
                        growth(profile)[key] = changed
                        with self.subTest(selected=selected, effect=key, value=changed), self.assertRaises(ValueError):
                            check_observations(profile, "Debug")

    def test_first_growth_backing_is_live_and_separate(self):
        for selected in (False, True):
            for pointer in (0, 65537, 2**64 - 8, 512, 32768, 65536 if selected else 131072):
                profile = observations()
                first = (profile["capacity_selection"] if selected else profile)["first_growth"]
                for key in ("after", "unchanged"):
                    first[key]["pointer"] = pointer
                with self.subTest(selected=selected, pointer=pointer), self.assertRaises(ValueError):
                    check_observations(profile, "Debug")

    def test_capacity_policy_requires_complete_typed_observations(self):
        original = observations()
        for key in original["capacity_selection"]:
            profile = copy.deepcopy(original)
            del profile["capacity_selection"][key]
            with self.subTest(missing=key), self.assertRaises(ValueError):
                check_observations(profile, "Debug")
        for key, changed in (("arch", "x86_64"), ("cache_line", 64), ("cache_line", True),
                ("overflow_oom", False), ("overflow_oom", 1), ("extra", 0), ("samples", []), ("samples", None)):
            profile = copy.deepcopy(original)
            profile["capacity_selection"][key] = changed
            with self.subTest(key=key, changed=changed), self.assertRaises(ValueError):
                check_observations(profile, "Debug")
        for index in range(8):
            for field in ("minimum", "capacity"):
                for changed in (True, original["capacity_selection"]["samples"][index][field] + 1):
                    profile = copy.deepcopy(original)
                    profile["capacity_selection"]["samples"][index][field] = changed
                    with self.subTest(index=index, field=field, changed=changed), self.assertRaises(ValueError):
                        check_observations(profile, "Debug")
        profile = copy.deepcopy(original)
        profile["capacity_selection"]["samples"].reverse()
        with self.assertRaises(ValueError):
            check_observations(profile, "Debug")

    def test_capacity_overflow_preserves_header(self):
        for key in ("overflow_before", "overflow_after"):
            for field, changed in (("pointer", 0), ("pointer", True), ("pointer", 2**64),
                    ("length", 1), ("length", False), ("capacity", 5), ("capacity", False), ("extra", 0)):
                profile = observations()
                profile["capacity_selection"][key][field] = changed
                with self.subTest(key=key, field=field, changed=changed), self.assertRaises(ValueError):
                    check_observations(profile, "Debug")

    def test_growing_append_headers_and_allocator_effects_are_required(self):
        original = observations()
        check_observations(original, "Debug")
        for key, value in original["growing_append"].items():
            profile = copy.deepcopy(original)
            del profile["growing_append"][key]
            with self.subTest(missing=key), self.assertRaises(ValueError):
                check_observations(profile, "Debug")
            if key in ("before", "failed", "after"):
                for field, expected in value.items():
                    for changed in (True, expected + 1):
                        profile = copy.deepcopy(original)
                        profile["growing_append"][key][field] = changed
                        with self.subTest(header=key, field=field, changed=changed), self.assertRaises(ValueError):
                            check_observations(profile, "Debug")
            elif type(value) in (bool, int):
                for changed in ((False, 1) if type(value) is bool else (True, value + 1)):
                    profile = copy.deepcopy(original)
                    profile["growing_append"][key] = changed
                    with self.subTest(effect=key, changed=changed), self.assertRaises(ValueError):
                        check_observations(profile, "Debug")

    def test_growing_append_retains_all_descriptor_fields_and_parent(self):
        original = observations()
        for key, value in original["growing_append"]["record"].items():
            profile = copy.deepcopy(original)
            del profile["growing_append"]["record"][key]
            with self.subTest(missing=key), self.assertRaises(ValueError):
                check_observations(profile, "Debug")
            changes = ([2, 3], [3, True]) if isinstance(value, list) else ((False, 1) if type(value) is bool else (False, value + 1))
            for changed in changes:
                profile = copy.deepcopy(original)
                profile["growing_append"]["record"][key] = changed
                with self.subTest(field=key, changed=changed), self.assertRaises(ValueError):
                    check_observations(profile, "Debug")
        for changed in ([777, 2, 3, 5], [777, 3, True, 5], [3, 2], []):
            profile = copy.deepcopy(original)
            profile["growing_append"]["parent_after"] = changed
            with self.subTest(parent=changed), self.assertRaises(ValueError):
                check_observations(profile, "Debug")

    def test_growing_append_backing_is_live_and_separate(self):
        for pointer in (0, 262145, 2**64 - 8, 512, 65536, 131072, 8192):
            profile = observations()
            profile["growing_append"]["after"]["pointer"] = pointer
            profile["growing_append"]["record"]["pointer"] = pointer
            with self.subTest(pointer=pointer), self.assertRaises(ValueError):
                check_observations(profile, "Debug")

    def programs(self, profile, source=None):
        # The real acceptance gate hashes all pinned std files. Layout mutations
        # are isolated here from filesystem-dependent toolchain discovery.
        with patch.object(admission.graph, "check_std", return_value=admission.graph.STD.copy()):
            return admission.programs(profile, Path("/unused/pinned-lib"), source)

    def generate(self, profile, source=None):
        return self.programs(profile, source)[admission.OUTPUT]

    def test_complete_layout_in_all_modes(self):
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            for path, generated in self.programs(fixture(mode)).items():
                self.assertEqual(generated, path.read_bytes())

    def test_native_field_order_is_canonical(self):
        profile = fixture()
        profile["fields"].reverse()
        profile["owner"]["fields"].reverse()
        profile["cache"]["fields"].reverse()
        for path, generated in self.programs(profile).items():
            self.assertEqual(generated, path.read_bytes())

    def test_every_owner_field_is_unique_and_required(self):
        for index in range(4):
            for mutation in ("omitted", "duplicate", "unknown", "extra"):
                profile = fixture()
                fields = profile["owner"]["fields"]
                if mutation == "omitted":
                    fields.pop(index)
                elif mutation == "duplicate":
                    fields[index] = fields[(index + 1) % 4].copy()
                elif mutation == "unknown":
                    fields[index]["name"] = "unreviewed"
                else:
                    fields[index]["default"] = 0
                with self.subTest(index=index, mutation=mutation), self.assertRaises(ValueError):
                    self.programs(profile)

    def test_capacity_limit_has_no_production_storage(self):
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            for key, value in (("type", "u32"), ("bytes", 4), ("bytes", False),
                    ("alignment", 4), ("alignment", True), ("offset", -1),
                    ("offset", True), ("offset", 73)):
                profile = fixture(mode)
                profile["owner"]["fields"][3][key] = value
                with self.subTest(mode=mode, key=key, value=value), self.assertRaises(ValueError):
                    self.programs(profile)

    def test_complete_map_fields_and_mode_specific_lock_are_required(self):
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            for index in range(4):
                for key, value in (("name", "foreign"), ("type", "opaque"), ("offset", 1),
                        ("offset", True), ("bytes", 7), ("bytes", False), ("alignment", 3),
                        ("alignment", True), ("extra", 0)):
                    profile = fixture(mode)
                    profile["cache"]["fields"][index][key] = value
                    with self.subTest(mode=mode, index=index, key=key), self.assertRaises(ValueError):
                        self.programs(profile)
                for mutation in ("omitted", "duplicate"):
                    profile = fixture(mode)
                    fields = profile["cache"]["fields"]
                    if mutation == "omitted":
                        fields.pop(index)
                    else:
                        fields[index] = fields[(index + 1) % 4].copy()
                    with self.subTest(mode=mode, index=index, mutation=mutation), self.assertRaises(ValueError):
                        self.programs(profile)
            profile = fixture(mode)
            profile["cache"]["fields"][3]["bytes"] = 1 if mode == "ReleaseFast" else 0
            with self.subTest(mode=mode), self.assertRaises(ValueError):
                self.programs(profile)

    def test_metadata_pointer_and_lock_profiles_are_exact(self):
        # Every leaf and every record/list boundary is required, including
        # zero-sized ReleaseFast state, pointer qualifiers and enum tags.
        def paths(value, prefix=()):
            yield prefix, value
            if isinstance(value, dict):
                for key, child in value.items():
                    yield from paths(child, prefix + (key,))
            elif isinstance(value, list):
                for index, child in enumerate(value):
                    yield from paths(child, prefix + (index,))

        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            original = fixture(mode)
            for part in ("metadata", "lock"):
                for path, value in paths(original["cache"][part], (part,)):
                    changed_values = [None]
                    if isinstance(value, dict):
                        changed_values += [{**value, "extra": 0}]
                    elif isinstance(value, list):
                        changed_values += [[], value + value]
                    elif type(value) is bool:
                        changed_values += [not value, int(value)]
                    elif type(value) is int:
                        changed_values += [value + 1, bool(value)]
                    else:
                        changed_values += ["foreign"]
                    for changed in changed_values:
                        profile = copy.deepcopy(original)
                        owner = profile["cache"]
                        for key in path[:-1]:
                            owner = owner[key]
                        owner[path[-1]] = changed
                        with self.subTest(mode=mode, path=path, changed=changed), self.assertRaises(ValueError):
                            self.programs(profile)
                    profile = copy.deepcopy(original)
                    owner = profile["cache"]
                    for key in path[:-1]:
                        owner = owner[key]
                    del owner[path[-1]]
                    with self.subTest(mode=mode, missing=path), self.assertRaises(ValueError):
                        self.programs(profile)

    def test_anonymous_lock_suffix_does_not_change_admitted_type(self):
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            profile = fixture(mode)
            profile["cache"]["lock"]["fields"][0]["type"] = "debug.SafetyLock.State__enum_987654321"
            self.assertEqual(self.programs(profile), self.programs(fixture(mode)))

    def test_map_build_context_and_closed_profile_are_required(self):
        for key, value in (("schema", "foreign"), ("mode", "Debug"), ("cpu", "foreign"),
                ("cpuFeatures", [1]), ("bytes", 24), ("name", "foreign"), ("extra", 0)):
            profile = fixture()
            profile["cache"]["target"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.programs(profile)
        for value in (None, {}, {"target": fixture()["target"]}):
            profile = fixture()
            profile["cache"] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.programs(profile)

    def test_owner_field_types_and_geometry_are_checked(self):
        for index in range(3):
            for key, value in (("type", "opaque"), ("bytes", 0), ("bytes", True), ("alignment", 4),
                    ("alignment", True), ("offset", -1), ("offset", 1), ("offset", 56), ("offset", True)):
                profile = fixture()
                profile["owner"]["fields"][index][key] = value
                with self.subTest(index=index, key=key, value=value), self.assertRaises(ValueError):
                    self.programs(profile)
        profile = fixture()
        profile["owner"]["fields"][1]["offset"] = 8
        with self.assertRaisesRegex(ValueError, "overlapping"):
            self.programs(profile)

    def test_owner_target_and_complete_profile_are_checked(self):
        for key, value in (("arch", "x86_64"), ("schema", "foreign"), ("name", "foreign"), ("backend", "stage2_aarch64"),
                ("bytes", 48), ("bytes", True), ("alignment", 4), ("alignment", True), ("extra", 0)):
            profile = fixture()
            profile["owner"]["target"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.programs(profile)
        for key, value in (("target", {}), ("fields", {}), ("extra", 0)):
            profile = fixture()
            profile["owner"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.programs(profile)
        for value in ({}, [], None):
            profile = fixture()
            profile["owner"] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.programs(profile)

    def test_owner_and_header_share_the_exact_build_context(self):
        for key, value in (("mode", "Debug"), ("cpu", "other_cpu"), ("cpuFeatures", [1]),
                ("osVersionRange", item_fixture()["osVersionRange"])):
            profile = fixture()
            if key == "osVersionRange":
                value = copy.deepcopy(value)
                value["semver"]["max"]["major"] += 1
            profile["owner"]["target"][key] = value
            with self.subTest(key=key), self.assertRaisesRegex(ValueError, "contexts differ"):
                self.programs(profile)

    def test_every_header_field_is_unique_and_required(self):
        for mutation in ("omitted", "duplicate", "unknown", "extra", "wrong-container"):
            profile = fixture()
            if mutation == "omitted":
                profile["fields"].pop()
            elif mutation == "duplicate":
                profile["fields"][1] = profile["fields"][0].copy()
            elif mutation == "unknown":
                profile["fields"][1]["name"] = "allocator"
            elif mutation == "extra":
                profile["fields"][1]["default"] = 0
            else:
                profile["fields"] = {}
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                self.generate(profile)

    def test_all_header_field_types_and_geometry_are_checked(self):
        for index in range(2):
            for key, value in (("type", "u64"), ("bytes", 0), ("bytes", True), ("alignment", 1),
                    ("alignment", True), ("offset", -1), ("offset", 1), ("offset", 24), ("offset", True)):
                profile = fixture()
                profile["fields"][index][key] = value
                with self.subTest(index=index, key=key, value=value), self.assertRaises(ValueError):
                    self.generate(profile)
        profile = fixture()
        profile["fields"][1]["offset"] = 8
        with self.assertRaisesRegex(ValueError, "overlapping"):
            self.generate(profile)

    def test_nominal_element_is_bound_to_expression(self):
        for key, value in (("name", "foreign"), ("bytes", 40), ("alignment", 4), ("bytes", True), ("extra", 0)):
            profile = fixture()
            profile["element"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.generate(profile)

    def test_closed_target_and_profile_metadata(self):
        for key, value in (("arch", "x86_64"), ("mode", "ReleaseSmall"), ("backend", "stage2_aarch64"),
                ("pointerBits", 32), ("bytes", True), ("alignment", 3), ("name", "foreign"),
                ("cpuFeatures", [False]), ("osVersionRange", {}), ("extra", 0)):
            profile = fixture()
            profile["target"][key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.generate(profile)
        for key, value in (("schema", "foreign"), ("fields", None), ("element", []), ("extra", 0)):
            profile = fixture()
            profile[key] = value
            with self.subTest(key=key), self.assertRaises(ValueError):
                self.generate(profile)

    def test_changed_admissible_extent_is_not_committed_layout(self):
        profile = fixture()
        profile["target"]["bytes"] = 32
        with self.assertRaisesRegex(ValueError, "embedded.*extent"):
            self.programs(profile)
        profile = fixture()
        profile["owner"]["target"]["bytes"] = 64
        with self.assertRaisesRegex(ValueError, "build-mode extent"):
            self.programs(profile)

    def test_safety_and_fast_owner_extents_cannot_be_interchanged(self):
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            for target, field in ((56, 16), (72, 24)):
                profile = fixture(mode)
                if target == profile["owner"]["target"]["bytes"]:
                    continue
                profile["owner"]["target"]["bytes"] = target
                profile["owner"]["fields"][2]["bytes"] = field
                with self.subTest(mode=mode), self.assertRaisesRegex(ValueError, "build-mode extent"):
                    self.programs(profile)

    def test_source_owner_and_readers_are_bound(self):
        source = admission.graph.storage.SOURCE.read_text()
        for before, after in (
                ("representatives: std.ArrayList(Expression) = .empty,", "representatives: std.ArrayList(u32) = .empty,"),
                ("if (id >= self.representatives.items.len)", "if (id > self.representatives.items.len)"),
                ("return &self.representatives.items[id];", "return &self.representatives.items[0];"),
                ("    pub fn init(allocator: std.mem.Allocator) ExpressionClasses {",
                 "    extra: usize = 0,\n    pub fn init(allocator: std.mem.Allocator) ExpressionClasses {"),
                ("    fn writeDAG(self: *const ExpressionClasses, writer: anytype, id: Id) !void {",
                 "    extra: usize = 0,\n    fn writeDAG(self: *const ExpressionClasses, writer: anytype, id: Id) !void {")):
            self.assertIn(before, source)
            with self.subTest(mutation=after), self.assertRaises((Unsupported, ValueError)):
                self.generate(fixture(), source.replace(before, after, 1).encode())
        with self.assertRaises(ValueError):
            self.generate(fixture(), b"// changed source identity\n" + source.encode())

    def test_changed_standard_library_is_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            lib = Path(temporary)
            (lib / "std").mkdir()
            for name in admission.graph.STD:
                (lib / "std" / name).write_bytes(b"unreviewed standard library")
            with self.assertRaisesRegex(ValueError, "unreviewed Zig"):
                admission.generate(fixture(), lib)

    def test_descriptor_assignment_fields_are_source_bound(self):
        source = admission.graph.storage.SOURCE.read_text()
        for before, after in (
                (".id = id,", ".id = 0,"),
                (".item = owned_item,", ".item = item,"),
                (".arguments = representative_arguments,", ".arguments = normalized,"),
                (".sequence_number = sequence_number,", ".sequence_number = 0,"),
                ("try self.representatives.append(self.allocator, .{", "self.representatives.appendAssumeCapacity(.{")):
            self.assertIn(before, source)
            with self.subTest(field=before), self.assertRaises((Unsupported, ValueError)):
                self.generate(fixture(), source.replace(before, after, 1).encode())

    def test_native_observation_inventory_and_fields(self):
        original = observations()
        for mode in ("Debug", "ReleaseSafe", "ReleaseFast"):
            check_observations(observations(mode), mode)
        for index, record in enumerate(original["representatives"]):
            for key in record:
                profile = copy.deepcopy(original)
                del profile["representatives"][index][key]
                with self.subTest(index=index, omitted=key), self.assertRaises(ValueError):
                    check_observations(profile, "Debug")
                for value in (False, "changed", None):
                    profile = copy.deepcopy(original)
                    profile["representatives"][index][key] = value
                    with self.subTest(index=index, key=key, value=value), self.assertRaises(ValueError):
                        check_observations(profile, "Debug")

    def test_copy_requires_complete_exact_source_and_destination(self):
        original = observations()
        for branch in ("source_before", "copied"):
            for index in range(5):
                for key in original["copy"][branch][index]:
                    for value in (None, False, True, 0, [], "changed"):
                        profile = copy.deepcopy(original)
                        profile["copy"][branch][index][key] = value
                        if json.dumps(value) == json.dumps(original["copy"][branch][index][key]):
                            continue
                        with self.subTest(branch=branch, index=index, key=key, value=value), self.assertRaises(ValueError):
                            check_observations(profile, "Debug")
        for key, value in (("source_before", []), ("copied", []), ("header_before", {}),
                ("target_capacity", 5), ("target_capacity", True), ("target_pointer", True),
                ("target_pointer", 512), ("target_pointer", 4080), ("target_pointer", 8192),
                ("target_pointer", 1024), ("target_pointer", 2432), ("target_pointer", 16385),
                ("target_pointer", 2**64 - 8), ("extra", 0)):
            profile = copy.deepcopy(original)
            profile["copy"][key] = value
            if key == "target_pointer" and type(value) is int:
                profile["publication"]["before"]["pointer"] = value
                for index, row in enumerate(profile["copy"]["copied"]):
                    row["pointer"] = value + index * 32
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                check_observations(profile, "Debug")
        for key in ("pointer", "length", "capacity"):
            expected = original["copy"]["header_before"][key]
            for value in (True, float(expected), expected + 1):
                profile = copy.deepcopy(original)
                profile["copy"]["header_before"][key] = value
                with self.subTest(header=key, value=value), self.assertRaises(ValueError):
                    check_observations(profile, "Debug")

    def test_publication_exact_headers_and_all_descriptors(self):
        original = observations()
        for part in ("before", "after"):
            for key in ("pointer", "length", "capacity"):
                expected = original["publication"][part][key]
                for value in (True, float(expected), expected + 1):
                    profile = copy.deepcopy(original)
                    profile["publication"][part][key] = value
                    with self.subTest(part=part, key=key, value=value), self.assertRaises(ValueError):
                        check_observations(profile, "Debug")
        for index, row in enumerate(original["publication"]["representatives"]):
            for key in row:
                profile = copy.deepcopy(original)
                del profile["publication"]["representatives"][index][key]
                with self.subTest(index=index, key=key), self.assertRaises(ValueError):
                    check_observations(profile, "Debug")
        for key in ("before", "after", "representatives"):
            profile = copy.deepcopy(original)
            del profile["publication"][key]
            with self.subTest(omitted=key), self.assertRaises(ValueError):
                check_observations(profile, "Debug")

    def test_publication_checks_live_regions_without_assuming_remap_outcome(self):
        for pointer in (16384, 32768):
            profile = observations()
            profile["publication"]["after"]["pointer"] = pointer
            for index, row in enumerate(profile["publication"]["representatives"]):
                row["pointer"] = pointer + index * 32
            check_observations(profile, "Debug")
        for pointer in (0, 513, 512, 4080, 8192, 1024, 2416, 2**64 - 8):
            profile = observations()
            profile["publication"]["after"]["pointer"] = pointer
            for index, row in enumerate(profile["publication"]["representatives"]):
                row["pointer"] = pointer + index * 32
            with self.subTest(pointer=pointer), self.assertRaises(ValueError):
                check_observations(profile, "Debug")

    def test_native_bounds_stride_and_separation(self):
        original = observations()
        for key, value in (("header_pointer", 513), ("header_pointer", 512), ("header_pointer", True),
                ("items_pointer", 520), ("length", 6), ("capacity", 5), ("capacity", True), ("capacity", 2**32),
                ("header_bytes", True), ("element_alignment", 4), ("empty_rejected", False),
                ("length_rejected", 1), ("capacity_rejected", False), ("maximum_rejected", False),
                ("cache_hit", False), ("cache_hit", 1), ("cache_hit_size_unchanged", False),
                ("before_append_length", 3), ("before_append_length", True), ("before_append_capacity", 9),
                ("before_append_pointer", 544), ("before_append_pointer", False), ("append_size_increased", False),
                ("append_capacity_unchanged", False), ("append_backing_unchanged", False), ("append_id_matches_previous_length", False),
                ("schema", "oksolc.representative-array-observations.v2"),
                ("schema", "oksolc.representative-array-observations.v3"), ("parent_pointer", 513), ("parent_pointer", True),
                ("schema", "oksolc.representative-array-observations.v4"),
                ("owner_pointer", 4096), ("owner_pointer", True), ("owner_pointer", 2**64 - 24),
                ("owner_bytes", 24), ("owner_bytes", 56), ("owner_bytes", True), ("owner_alignment", 4), ("owner_alignment", True),
                ("allocator_pointer", 4088), ("allocator_pointer", True), ("expressions_pointer", 4112), ("expressions_pointer", True),
                ("parent_pointer", 4080), ("parent_pointer", 4128),
                ("parent_pointer", 512), ("parent_before", [777, 3, 2]), ("parent_before", [777, 2, 3, 5]),
                ("parent_after", [777, 3, 2, 6]), ("parent_after", [777, 3, True, 5]), ("parent_offset", 0), ("parent_offset", True), ("parent_length", 3),
                ("representatives", []), ("extra", 0)):
            profile = copy.deepcopy(original)
            profile[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(ValueError):
                check_observations(profile, "Debug")
        for index, key, value in ((1, "pointer", 512), (2, "item_pointer", 512),
                (2, "arguments_pointer", 2417), (3, "arguments_pointer", 2416),
                (4, "arguments", [2, 3]), (4, "arguments", [3, True]), (4, "arguments_length", 1),
                (4, "id", 3), (4, "sequence_number", 1), (4, "readonly", False)):
            profile = copy.deepcopy(original)
            profile["representatives"][index][key] = value
            with self.subTest(index=index, key=key), self.assertRaises(ValueError):
                check_observations(profile, "Debug")


if __name__ == "__main__":
    unittest.main()
